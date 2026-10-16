#!/usr/bin/env python3
"""Strict in-memory NSX managers and vCenters for exercising `fleetparity migpath`.
   python3 mock_nsx.py <role> <port> cert.pem key.pem      role: green-gm | blue-gm | green-lm | lm | vc

green-lm is Green's site-a Local Manager (edges, router MAC, VM tags); lm is any other Local Manager
(router MAC, VM tags; on 9446, Blue's site-a edges). Both serve the fabric: transport nodes, their
deployment state, edge clusters, Policy transport zones, uplink profiles and compute managers. The
Global Managers serve no global-config: the real Global Manager API has none, and the router MAC
lives on each Local Manager. vc is a vCenter (REST: sessions, networks, clusters, VMs with their
NICs and guest addresses; SOAP /sdk: a VDS with port groups, created and reconfigured by task).

Strict on purpose: PATCH on an existing object REPLACES it (partial patch disabled, the NSX
default), and PUT with a stale _revision is refused. Any code that PATCHes a partial body
onto a live object loses fields here, visibly. vCenter calls without a session are refused."""
import copy
import json
import re
import ssl
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

GM = "/global-manager/api/v1/global-infra"
ROLE = sys.argv[1]
PORTN = int(sys.argv[2])
S, LISTS, LM, GC, ALARMS, SIDE, FVM, VC, FAIL = {}, set(), {}, {}, {}, {}, {}, {}, {}
TN, ECS, PTZ, HSP, EDGEFAIL, VCFAIL = {}, {}, {}, {}, {}, {}
GC_PATH = "/policy/api/v1/infra/global-config"
FVM_PATH = "/api/v1/fabric/virtual-machines"
PTZ_PATH = "/policy/api/v1/infra/sites/default/enforcement-points/default/transport-zones"
TOKEN = "vc-session-%s" % sys.argv[2]
VCSERVER = {9445: "127.0.0.1:9450", 9446: "127.0.0.1:9448"}.get(PORTN, "127.0.0.1:9449")
VIMNS = "{urn:vim25}"
SOAPENV = "http://schemas.xmlsoap.org/soap/envelope/"
XSI = "http://www.w3.org/2001/XMLSchema-instance"


def edge_obj(name, ip, nets, ff="MEDIUM", static=False, tzs=None, uplink_switch=None):
    """A deployed edge as the fabric API returns it: read-only fields filled, passwords blank. uplink_switch:
    a second N-VDS on fp-eth2/3 carrying only that zone, no TEP, as VCF gives its Tier-0 edges."""
    tid = "tn-" + name
    spec = ({"resource_type": "StaticIpListSpec", "ip_list": ["10.1.9.%d" % (len(TN) + 10)], "subnet_mask": "255.255.255.0",
             "default_gateway": "10.1.9.1"} if static else {"resource_type": "StaticIpPoolSpec", "ip_pool_id": "pool-tep"})
    return {"resource_type": "TransportNode", "id": tid, "display_name": name, "_revision": 0, "_create_time": 1,
            "_system_owned": False, "failure_domain_id": "fd-default", "maintenance_mode": "DISABLED",
            "host_switch_spec": {"resource_type": "StandardHostSwitchSpec", "host_switches": [
                {"host_switch_name": "nvds-overlay", "host_switch_id": "hs-" + name, "host_switch_type": "NVDS",
                 "host_switch_mode": "STANDARD",
                 "host_switch_profile_ids": [{"key": "UplinkHostSwitchProfile", "value": "up-edge-2"}],
                 "pnics": [{"device_name": "fp-eth0", "uplink_name": "uplink-1"}, {"device_name": "fp-eth1", "uplink_name": "uplink-2"}],
                 "ip_assignment_spec": spec,
                 "transport_zone_endpoints": [{"transport_zone_id": t} for t in (tzs if tzs is not None else LM.get(name, []))]}]
                + ([{"host_switch_name": "vlan-switch-x", "host_switch_id": "hs2-" + name, "host_switch_type": "NVDS",
                     "host_switch_mode": "STANDARD", "host_switch_profile_ids": [{"key": "UplinkHostSwitchProfile", "value": "up-edge-2"}],
                     "pnics": [{"device_name": "fp-eth2", "uplink_name": "uplink-1"}, {"device_name": "fp-eth3", "uplink_name": "uplink-2"}],
                     "ip_assignment_spec": {"resource_type": "AssignedByDhcp"},
                     "transport_zone_endpoints": [{"transport_zone_id": uplink_switch}]}] if uplink_switch else [])},
            "node_deployment_info": {
                "resource_type": "EdgeNode", "id": tid, "external_id": tid, "display_name": name, "fqdn": name + ".example.com",
                "ip_addresses": [ip], "discovered_ip_addresses": [ip], "deployment_type": "VIRTUAL_MACHINE",
                "deployment_config": {"form_factor": ff, "node_user_settings": {"cli_username": "admin"},
                                      "vm_deployment_config": {
                                          "placement_type": "VsphereDeploymentConfig", "vc_id": "cm-1", "compute_id": "domain-c8",
                                          "storage_id": "datastore-10", "host_id": "host-20", "management_network_id": "dvportgroup-200",
                                          "data_network_ids": list(nets), "default_gateway_addresses": ["10.1.1.1"],
                                          "management_port_subnets": [{"ip_addresses": [ip], "prefix_length": 24}],
                                          "resource_allocation": {"cpu_count": 4, "memory_allocation_in_mb": 8192}}},
                "node_settings": {"hostname": name + ".example.com", "dns_servers": ["10.1.1.5"], "ntp_servers": ["10.1.1.5"],
                                  "search_domains": ["example.com"], "enable_ssh": True, "allow_ssh_root_login": False}}}


def tn_view(t):
    """What GET returns: the object with its passwords blank and its zone endpoints as attached."""
    v = copy.deepcopy(t)
    (v["node_deployment_info"].get("deployment_config") or {}).pop("node_user_settings", None)
    v["node_deployment_info"].setdefault("deployment_config", {})["node_user_settings"] = {"cli_username": "admin"}
    if v["display_name"] in LM:                      # seeded edges: zones from /mock/attach
        v["host_switch_spec"]["host_switches"][0]["transport_zone_endpoints"] = [
            {"transport_zone_id": z} for z in LM[v["display_name"]]]
    v.pop("_state", None)
    v.pop("_polls", None)
    return v


def tn_state(t):
    t["_polls"] = t.get("_polls", 0) + 1
    st = t.get("_state") or "ready"
    if st == "failed":
        return {"state": "failed", "node_deployment_state": {"state": "VM_DEPLOYMENT_FAILED",
                                                             "failure_message": "no datastore with 200 GB free"},
                "failure_message": "Edge VM deployment failed"}
    if st == "deploying" and t["_polls"] <= 2:
        return {"state": "in_progress", "node_deployment_state": {"state": "VM_DEPLOYMENT_IN_PROGRESS"}}
    if st == "deploying":
        t["_state"] = "ready"
    return {"state": "success", "node_deployment_state": {"state": "NODE_READY"}}


def seed_fabric():
    HSP["nsx-edge-single-nic-uplink-profile"] = {
        "resource_type": "UplinkHostSwitchProfile", "id": "up-edge-1", "display_name": "nsx-edge-single-nic-uplink-profile",
        "teaming": {"policy": "FAILOVER_ORDER", "active_list": [{"uplink_name": "uplink-1", "uplink_type": "PNIC"}]},
        "transport_vlan": 0, "_system_owned": True}
    HSP["up-edge-2"] = {"resource_type": "UplinkHostSwitchProfile", "id": "up-edge-2", "display_name": "up-edge-2",
                        "teaming": {"policy": "LOADBALANCE_SRCID", "active_list": [
                            {"uplink_name": "uplink-1", "uplink_type": "PNIC"}, {"uplink_name": "uplink-2", "uplink_type": "PNIC"}]}}
    for tid, name, typ in (("tz-ov", "nsx-overlay-transportzone", "OVERLAY_STANDARD"),
                           ("tz-vl", "nsx-vlan-transportzone", "VLAN_BACKED")):
        PTZ[tid] = {"id": tid, "display_name": name, "tz_type": typ, "realization_id": "uuid-" + tid,
                    "path": PTZ_PATH.split("/policy/api/v1")[1] + "/" + tid, "_revision": 0}
    nets = ["dvportgroup-201", "dvportgroup-202"]
    if PORTN == 9445:
        PTZ["tz-br"] = {"id": "tz-br", "display_name": "tz-vlan-bridge-a", "tz_type": "VLAN_BACKED", "realization_id": "uuid-tz-br",
                        "path": PTZ_PATH.split("/policy/api/v1")[1] + "/tz-br", "_revision": 0}
        for i, n in enumerate(("green-a-bdg01", "green-a-bdg02", "green-a-edge05", "green-a-edge06")):
            TN["tn-" + n] = edge_obj(n, "10.1.1.%d" % (21 + i), nets)
        ECS["ec-br"] = {"id": "ec-br", "display_name": "green-a-bridge-ec", "_revision": 0, "members": [
            {"transport_node_id": "tn-green-a-bdg01"}, {"transport_node_id": "tn-green-a-bdg02"}]}
        ECS["ec-w1"] = {"id": "ec-w1", "display_name": "green-a-w01-ec01", "_revision": 0, "members": [
            {"transport_node_id": "tn-green-a-edge05"}, {"transport_node_id": "tn-green-a-edge06"}]}
    elif PORTN == 9446:
        PTZ["tz-ov"]["realization_id"] = "uuid-b-ov"
        for i, n in enumerate(("blue-a-edge01", "blue-a-edge02", "blue-a-bdg01", "blue-a-bdg02")):
            TN["tn-" + n] = edge_obj(n, "10.1.2.%d" % (21 + i), nets, tzs=["uuid-b-ov"])
            TN["tn-" + n]["node_deployment_info"]["deployment_config"]["vm_deployment_config"]["compute_id"] = "resgroup-1"
        ECS["bec"] = {"id": "bec", "display_name": "blue-edge-cluster", "_revision": 0, "members": [
            {"transport_node_id": "tn-blue-a-edge01"}, {"transport_node_id": "tn-blue-a-edge02"}]}
        ECS["bbec"] = {"id": "bbec", "display_name": "blue-bridge-ec", "_revision": 0, "members": [
            {"transport_node_id": "tn-blue-a-bdg01"}, {"transport_node_id": "tn-blue-a-bdg02"}]}


def seed_vc():
    VC["dvs"] = {"dvs-1": {"name": "vds01", "version": "8.0.0"}}
    VC["pg"] = {}
    VC["tasks"] = {}
    VC["rules"] = []                # [{"name", "enabled", "vm": [morefs]}] anti-affinity rules of cluster domain-c8
    VC["opts"] = {"config.vpxd.network.rollback": "true"}     # vCenter advanced settings
    VC["moves"] = []                # RelocateVM_Task specs received, passwords removed
    VC["folders"] = {"group-v3": {"name": "vm", "parent": ("Datacenter", "datacenter-2")},
                     "group-h4": {"name": "host", "parent": ("Datacenter", "datacenter-2")}}
    for moref, name, cfg in (("dvportgroup-200", "mgmt-pg", {"vlan": 100}), ("dvportgroup-201", "edge-uplink-a", {"vlan": 0}),
                             ("dvportgroup-202", "edge-uplink-b", {"vlan": 0})):
        VC["nets"][name] = moref
        VC["pg"][moref] = dict({"name": name, "dvs": "dvs-1", "trunk": None, "forged": False, "promisc": False, "learning": False,
                                "flooding": False, "description": "", "version": "1"}, **cfg)


def put(rel, obj):
    obj = dict(obj)
    obj.setdefault("id", rel.rstrip("/").split("/")[-1])
    obj.setdefault("display_name", obj["id"])
    obj["path"] = "/global-infra" + rel
    obj.setdefault("_revision", 0)
    S[rel] = obj
    LISTS.add(rel.rsplit("/", 1)[0])


def seed():
    for d in (S, LISTS, LM, GC, ALARMS, SIDE, FVM, VC, FAIL, TN, ECS, PTZ, HSP, EDGEFAIL, VCFAIL):
        d.clear()
    VC.update({"vms": {}, "nets": {}, "n": 0})
    if ROLE == "vc":
        seed_vc()
    if ROLE in ("green-lm", "lm"):
        GC.update({"resource_type": "GlobalConfig", "vdr_mac": "02:50:56:56:44:52",
                   "allow_changing_vdr_mac_in_use": False, "_revision": 0})
    if ROLE == "green-gm":
        site = "site-a"
        ep = "/sites/%s/enforcement-points/default" % site
        for s in ("site-a", "site-b"):
            put("/sites/" + s, {})
        for tid, name, typ in (("tz-ov", "nsx-overlay-transportzone", "OVERLAY_BACKED"),
                               ("tz-vl", "nsx-vlan-transportzone", "VLAN_BACKED"),
                               ("tz-t0", "nsx-vlan-t0-tz", "VLAN_BACKED"),
                               ("tz-br", "tz-vlan-bridge-a", "VLAN_BACKED")):
            put(ep + "/transport-zones/" + tid, {"display_name": name, "tz_type": typ, "nsx_id": "uuid-" + tid})
        clusters = {"green-a-m01-ec01": ["green-a-edge01", "green-a-edge02", "green-a-edge03", "green-a-edge04"],
                    "green-a-m01-ec02": ["green-a-edge07", "green-a-edge08", "green-a-edge09", "green-a-edge10"],
                    "green-a-w01-ec01": ["green-a-edge05", "green-a-edge06"],
                    "green-a-bridge-ec": ["green-a-bdg01", "green-a-bdg02"]}
        for i, (cn, nodes) in enumerate(clusters.items()):
            put(ep + "/edge-clusters/ec-%d" % i, {"display_name": cn})
            for j, nn in enumerate(nodes):
                put(ep + "/edge-clusters/ec-%d/edge-nodes/n%d" % (i, j), {"display_name": nn})
        LISTS.add(ep + "/edge-bridge-profiles")
        put("/tier-0s/T0-STRETCHED-A-B", {"display_name": "T0-STRETCHED-A-B"})
        put("/tier-0s/T0-STRETCHED-A-B/locale-services/site-a",
            {"edge_cluster_path": "/global-infra" + ep + "/edge-clusters/ec-1",
             "route_redistribution_config": {"redistribution_rules": [
                 {"name": "r1", "route_redistribution_types": ["TIER1_CONNECTED", "TIER0_CONNECTED"]}]}})
        put("/tier-0s/T0-STRETCHED-A-B/locale-services/site-a/bgp/neighbors/nbr-a1",
            {"neighbor_address": "198.51.100.30", "route_filtering": [
                {"address_family": "IPV4",
                 "out_route_filters": ["/global-infra/tier-0s/T0-STRETCHED-A-B/prefix-lists/PL-STRETCHED-OUT"]}]})
        put("/tier-0s/T0-STRETCHED-A-B/locale-services/site-a/bgp", {"local_as_num": "65001", "enabled": True})
        put("/tier-0s/T0-STRETCHED-A-B/locale-services/site-b",
            {"edge_cluster_path": "/global-infra/sites/site-b/enforcement-points/default/edge-clusters/ec-9",
             "route_redistribution_config": {"redistribution_rules": [
                 {"name": "r1", "route_redistribution_types": ["TIER1_CONNECTED", "TIER0_CONNECTED"]}]}})
        put("/tier-0s/T0-STRETCHED-A-B/locale-services/site-b/bgp/neighbors/nbr-b1",
            {"neighbor_address": "203.0.113.30", "route_filtering": [
                {"address_family": "IPV4",
                 "out_route_filters": ["/global-infra/tier-0s/T0-STRETCHED-A-B/prefix-lists/PL-STRETCHED-B-OUT"]}]})
        put("/tier-0s/T0-STRETCHED-A-B/prefix-lists/PL-STRETCHED-B-OUT",
            {"prefixes": [{"network": "10.40.0.0/16", "action": "PERMIT", "le": 24}, {"network": "ANY", "action": "DENY"}]})
        put("/tier-0s/T0-STRETCHED-A-B/prefix-lists/PL-STRETCHED-OUT",
            {"prefixes": [{"network": "10.50.98.0/24", "action": "PERMIT"}, {"network": "ANY", "action": "DENY"}]})
        put("/tier-1s/T1-STRETCHED-A-PRI", {"tier0_path": "/global-infra/tier-0s/T0-STRETCHED-A-B",
                                             "route_advertisement_types": ["TIER1_CONNECTED", "TIER1_STATIC_ROUTES"]})
        put("/segments/seg-stretched-test", {"connectivity_path": "/global-infra/tier-1s/T1-STRETCHED-A-PRI",
                                             "subnets": [{"gateway_address": "10.50.98.1/24"}]})
    elif ROLE == "blue-gm":
        ep = "/sites/blue-a/enforcement-points/default"
        put("/sites/blue-a", {"display_name": "SITE-A"})
        put("/sites/blue-b", {"display_name": "SITE-B"})
        put(ep + "/transport-zones/b-ov", {"display_name": "blue-overlay-tz", "tz_type": "OVERLAY_BACKED"})
        put(ep + "/transport-zones/b-br", {"display_name": "tz-vlan-bridge-blue", "tz_type": "VLAN_BACKED"})
        put(ep + "/transport-zones/b-vl", {"display_name": "blue-vlan-tz", "tz_type": "VLAN_BACKED"})
        # production edges run Blue's gateways; the bridge edges are a separate, dedicated cluster
        put(ep + "/edge-clusters/bec", {"display_name": "blue-edge-cluster"})
        for j, nn in enumerate(["blue-a-edge01", "blue-a-edge02", "blue-a-edge03", "blue-a-edge04"]):
            put(ep + "/edge-clusters/bec/edge-nodes/b%d" % j, {"display_name": nn})
        put(ep + "/edge-clusters/bbec", {"display_name": "blue-bridge-ec"})
        for j, nn in enumerate(["blue-a-bdg01", "blue-a-bdg02"]):
            put(ep + "/edge-clusters/bbec/edge-nodes/bb%d" % j, {"display_name": nn})
        LISTS.add(ep + "/edge-bridge-profiles")
        bec = "/global-infra" + ep + "/edge-clusters/bec"
        put("/tier-0s/T0-BLUE", {"display_name": "T0-BLUE", "ha_mode": "ACTIVE_ACTIVE"})
        put("/tier-0s/T0-BLUE/locale-services/blue-a", {"edge_cluster_path": bec, "route_redistribution_config": {
            "redistribution_rules": [{"name": "r1", "route_redistribution_types": ["TIER1_CONNECTED"]}]}})
        put("/tier-0s/T0-BLUE/locale-services/blue-a/bgp/neighbors/nbr-blue1",
            {"neighbor_address": "192.0.2.62", "remote_as_num": "65002", "password": "s3cret-bgp"})
        put("/tier-0s/T0-BLUE/prefix-lists/PL-BLUE-OUT",
            {"prefixes": [{"network": "10.30.0.0/16", "action": "PERMIT", "le": 24}, {"network": "ANY", "action": "DENY"}]})
        put("/tier-1s/T1-BLUE-APP", {"display_name": "T1-BLUE-APP", "tier0_path": "/global-infra/tier-0s/T0-BLUE",
                                     "route_advertisement_types": ["TIER1_CONNECTED"]})
        put("/tier-1s/T1-BLUE-APP/locale-services/blue-a", {"edge_cluster_path": bec})
        for sid, gw in (("app-210", "10.30.10.1/24"), ("db-211", "10.30.11.1/24"), ("vdi-60", "10.60.0.1/24")):
            # fields migpath does not manage: they must survive every write
            put("/segments/" + sid, {"connectivity_path": "/global-infra/tier-1s/T1-BLUE-APP",
                                     "subnets": [{"gateway_address": gw}], "advanced_config": {"connectivity": "ON"},
                                     "description": "blue production " + sid, "tags": [{"scope": "app", "tag": sid}],
                                     "admin_state": "UP", "replication_mode": "MTEP"})
        put("/segments/telecom-vlan-400", {"vlan_ids": ["400"], "subnets": [],
                                           "transport_zone_path": "/global-infra" + ep + "/transport-zones/b-vl"})
    elif ROLE == "green-lm":
        for n in ("green-a-bdg01", "green-a-bdg02", "green-a-edge05", "green-a-edge06"):
            LM[n] = ["uuid-tz-ov"]
    if ROLE in ("green-lm", "lm"):
        seed_fabric()


def side_effect(written):
    t = SIDE.get("touch")
    if SIDE.get("on") == written and t in S:
        S[t]["_revision"] += 1


def tn():
    return {"results": [tn_view(t) for t in TN.values()], "result_count": len(TN)}


def ecs():
    return {"results": list(ECS.values()), "result_count": len(ECS)}


def vc_net(name):
    if name not in VC["nets"]:
        VC["n"] += 1
        VC["nets"][name] = "dvportgroup-%d" % (100 + VC["n"])
        if "pg" in VC:
            VC["pg"][VC["nets"][name]] = {"name": name, "dvs": "dvs-1", "trunk": None, "vlan": 0, "forged": False,
                                          "promisc": False, "learning": False, "flooding": False, "description": "", "version": "1"}
    return VC["nets"][name]


def xesc(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def pg_xml(moref, p):
    vl = ('<vlan xsi:type="VmwareDistributedVirtualSwitchTrunkVlanSpec"><inherited>false</inherited>%s</vlan>'
          % "".join("<vlanId><start>%d</start><end>%d</end></vlanId>" % r for r in p["trunk"])
          if p.get("trunk") else '<vlan xsi:type="VmwareDistributedVirtualSwitchVlanIdSpec"><inherited>false</inherited>'
          '<vlanId>%d</vlanId></vlan>' % p.get("vlan", 0))
    tf = lambda b: "true" if b else "false"     # noqa: E731
    return ('<val xsi:type="DVPortgroupConfigInfo"><key>%s</key><name>%s</name><numPorts>8</numPorts>'
            '<distributedVirtualSwitch type="VmwareDistributedVirtualSwitch">%s</distributedVirtualSwitch>'
            '<defaultPortConfig xsi:type="VMwareDVSPortSetting">%s<macManagementPolicy><inherited>false</inherited>'
            '<allowPromiscuous>%s</allowPromiscuous><macChanges>false</macChanges><forgedTransmits>%s</forgedTransmits>'
            '<macLearningPolicy><inherited>false</inherited><enabled>%s</enabled><allowUnicastFlooding>%s</allowUnicastFlooding>'
            '<limit>4096</limit><limitPolicy>DROP</limitPolicy></macLearningPolicy></macManagementPolicy></defaultPortConfig>'
            '<description>%s</description><configVersion>%s</configVersion><type>earlyBinding</type></val>'
            % (moref, xesc(p["name"]), p["dvs"], vl, tf(p["promisc"]), tf(p["forged"]), tf(p["learning"]), tf(p["flooding"]),
               xesc(p.get("description") or ""), p["version"]))


def pg_from_spec(spec, p=None):
    """A DVPortgroupConfigSpec, strictly: the elements in schema order, the trunk as ranges."""
    p = dict(p or {"name": None, "dvs": "dvs-1", "trunk": None, "vlan": 0, "forged": False, "promisc": False,
                   "learning": False, "flooding": False, "description": "", "version": "0"})
    order = [c.tag.replace(VIMNS, "") for c in spec]
    want = [t for t in ("configVersion", "name", "numPorts", "defaultPortConfig", "description", "type", "autoExpand") if t in order]
    if order != want:
        raise ValueError("DVPortgroupConfigSpec elements out of order: %s" % ",".join(order))
    if spec.findtext(VIMNS + "name"):
        p["name"] = spec.findtext(VIMNS + "name")
    if spec.findtext(VIMNS + "description") is not None:
        p["description"] = spec.findtext(VIMNS + "description")
    dpc = spec.find(VIMNS + "defaultPortConfig")
    if dpc is not None:
        if dpc.get("{%s}type" % XSI) != "VMwareDVSPortSetting":
            raise ValueError("defaultPortConfig must be a VMwareDVSPortSetting")
        sub = [c.tag.replace(VIMNS, "") for c in dpc]
        if sub != [t for t in ("blocked", "vlan", "macManagementPolicy") if t in sub]:
            raise ValueError("VMwareDVSPortSetting elements out of order: %s" % ",".join(sub))
        vl = dpc.find(VIMNS + "vlan")
        if vl is not None:
            if vl.get("{%s}type" % XSI) != "VmwareDistributedVirtualSwitchTrunkVlanSpec":
                raise ValueError("vlan is not a trunk spec")
            p["trunk"] = [(int(r.findtext(VIMNS + "start")), int(r.findtext(VIMNS + "end"))) for r in vl.findall(VIMNS + "vlanId")]
        mm = dpc.find(VIMNS + "macManagementPolicy")
        if mm is not None:
            sub = [c.tag.replace(VIMNS, "") for c in mm]
            if sub != [t for t in ("inherited", "allowPromiscuous", "macChanges", "forgedTransmits", "macLearningPolicy") if t in sub]:
                raise ValueError("DVSMacManagementPolicy elements out of order: %s" % ",".join(sub))
            p["promisc"] = mm.findtext(VIMNS + "allowPromiscuous") == "true"
            p["forged"] = mm.findtext(VIMNS + "forgedTransmits") == "true"
            ml = mm.find(VIMNS + "macLearningPolicy")
            if ml is not None:
                sub = [c.tag.replace(VIMNS, "") for c in ml]
                if sub != [t for t in ("inherited", "enabled", "allowUnicastFlooding", "limit", "limitPolicy") if t in sub]:
                    raise ValueError("DVSMacLearningPolicy elements out of order: %s" % ",".join(sub))
                p["learning"] = ml.findtext(VIMNS + "enabled") == "true"
                p["flooding"] = ml.findtext(VIMNS + "allowUnicastFlooding") == "true"
    return p


class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body):
        raw = b"" if code == 204 else json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def body(self):
        n = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(n) or b"{}")

    def rel(self):
        u = urllib.parse.urlparse(self.path)
        return u.path, urllib.parse.parse_qs(u.query)

    def vc_get(self, p, q):
        if p == "/sdk/vimServiceVersions.xml":
            raw = ('<?xml version="1.0"?><namespaces version="1.0"><namespace><name>urn:vim25</name>'
                   '<version>8.0.3.0</version><priorVersions><version>8.0.2.0</version><version>7.0.3.0</version>'
                   '</priorVersions></namespace></namespaces>').encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/xml")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            return self.wfile.write(raw)
        if self.headers.get("vmware-api-session-id") != TOKEN:
            return self.send(401, {"error_type": "UNAUTHENTICATED"})
        if p == "/api/vcenter/network":
            names = q.get("names") or list(VC["nets"])
            return self.send(200, [{"network": VC["nets"][n], "name": n, "type": "DISTRIBUTED_PORTGROUP"}
                                   for n in names if n in VC["nets"]])
        if p == "/api/vcenter/cluster":
            return self.send(200, [{"cluster": "domain-c8", "name": "cl01", "drs_enabled": True, "ha_enabled": True}]
                             if not q.get("names") or "cl01" in q["names"] else [])
        if p == "/api/vcenter/datastore":
            return self.send(200, [{"datastore": "datastore-10", "name": "vsan-ds", "type": "VSAN"}]
                             if not q.get("names") or "vsan-ds" in q["names"] else [])
        if p == "/api/vcenter/vm":
            if q.get("clusters") and q["clusters"] != ["domain-c8"]:
                return self.send(200, [])
            return self.send(200, [{"vm": v["vm"], "name": n, "power_state": v.get("power_state", "POWERED_ON")}
                                   for n, v in sorted(VC["vms"].items()) if not q.get("names") or n in q["names"]])
        parts = p.split("/")
        if len(parts) >= 5 and p.startswith("/api/vcenter/vm/"):
            v = next((dict(x, name=n) for n, x in VC["vms"].items() if x["vm"] == parts[4]), None)
            if not v:
                return self.send(404, {"error_type": "NOT_FOUND"})
            if len(parts) == 5:
                nics = {"4000": {"backing": {"network": VC["nets"][v["network"]], "type": "DISTRIBUTED_PORTGROUP"},
                                 "state": "CONNECTED"}} if v.get("network") else {}
                return self.send(200, {"name": v["name"], "power_state": v.get("power_state", "POWERED_ON"), "nics": nics})
            if parts[5:] == ["guest", "identity"]:
                if not v.get("ip"):
                    return self.send(503, {"error_type": "SERVICE_UNAVAILABLE"})
                return self.send(200, {"ip_address": v["ip"], "host_name": v["name"], "family": "LINUX"})
        return self.send(404, {"error_type": "NOT_FOUND"})

    def authed(self):
        """The Local Managers check the password: any user, password pw."""
        if ROLE not in ("green-lm", "lm"):
            return True
        import base64
        try:
            u, _s, pw = base64.b64decode((self.headers.get("Authorization") or "").split(" ", 1)[1]).decode().partition(":")
        except Exception:
            u, pw = "", ""
        if pw == "pw":
            return True
        self.send(403, {"error_message": "The credentials were incorrect or the account specified has been locked."})
        return False

    def do_GET(self):
        p, q = self.rel()
        if ROLE == "vc":
            return self.vc_get(p, q)
        if not self.authed():
            return
        if p == "/api/v1/alarms":
            return self.send(200, {"results": list(ALARMS.values()), "result_count": len(ALARMS)})
        if p == "/api/v1/node/version":
            return self.send(200, {"product_version": "9.1.1.0.25691509" if ROLE != "blue-gm" and PORTN != 9446
                                   else "4.2.3.3.0.25171321"})
        if ROLE in ("green-lm", "lm"):
            if p == GC_PATH:
                return self.send(200, GC)
            if p == FVM_PATH:
                want = (q.get("display_name") or [None])[0]
                res = [v for v in FVM.values() if want is None or v["display_name"] == want]
                return self.send(200, {"results": res, "result_count": len(res)})
            if self.injected("GET", p):
                return
            if p == "/api/v1/transport-nodes":
                return self.send(200, tn())
            m = re.fullmatch(r"/api/v1/transport-nodes/([^/]+)(/state)?", p)
            if m and m.group(1) in TN:
                return self.send(200, tn_state(TN[m.group(1)]) if m.group(2) else tn_view(TN[m.group(1)]))
            if p == "/api/v1/edge-clusters":
                return self.send(200, ecs())
            if p.startswith("/api/v1/edge-clusters/") and p.split("/")[-1] in ECS:
                return self.send(200, ECS[p.split("/")[-1]])
            if p == PTZ_PATH:
                return self.send(200, {"results": list(PTZ.values()), "result_count": len(PTZ)})
            if p.startswith(PTZ_PATH + "/") and p.split("/")[-1] in PTZ:
                z = PTZ[p.split("/")[-1]]
                if z.get("_pending"):                 # realized only on the second read, as NSX
                    z["_pending"] -= 1
                    return self.send(200, {k: v for k, v in z.items() if k not in ("realization_id", "_pending")})
                return self.send(200, {k: v for k, v in z.items() if k != "_pending"})
            if p == "/api/v1/host-switch-profiles":
                return self.send(200, {"results": list(HSP.values()), "result_count": len(HSP)})
            if p == "/api/v1/fabric/compute-managers/cm-1":
                return self.send(200, {"id": "cm-1", "display_name": "vc", "server": VCSERVER, "origin_type": "vCenter"})
            return self.send(404, {"error_message": "not found"})
        if not p.startswith(GM):
            return self.send(404, {"error_message": "not found"})
        r = p[len(GM):]
        if self.injected("GET", r):
            return
        if r in S:
            return self.send(200, S[r])
        kids = [o for k, o in S.items() if k.rsplit("/", 1)[0] == r]
        if kids or r in LISTS:
            return self.send(200, {"results": kids, "result_count": len(kids)})
        return self.send(404, {"error_message": "The path=[%s] is invalid" % r})

    def do_PATCH(self):
        p, q = self.rel()
        if p.startswith("/api/") or p.startswith("/policy/"):
            if not self.authed():
                return
        if ROLE in ("green-lm", "lm"):
            if self.injected("PATCH", p):
                return
            if p.startswith(PTZ_PATH + "/"):
                b, tid = self.body(), p.split("/")[-1]
                if b.get("tz_type") not in ("VLAN_BACKED", "OVERLAY_STANDARD", "OVERLAY_ENS", "OVERLAY_BACKED"):
                    return self.send(400, {"error_message": "tz_type %r is not valid" % b.get("tz_type")})
                z = PTZ.get(tid) or {"id": tid, "realization_id": "uuid-" + tid, "_revision": -1, "_pending": 1,
                                     "path": PTZ_PATH.split("/policy/api/v1")[1] + "/" + tid}
                z.update({k: v for k, v in b.items() if k in ("display_name", "tz_type", "tags", "description")})
                z["_revision"] += 1
                PTZ[tid] = z
                return self.send(200, {k: v for k, v in z.items() if k not in ("realization_id", "_pending")})
            return self.send(404, {"error_message": "not found"})
        r = p[len(GM):]
        b = self.body()
        rev = S[r]["_revision"] + 1 if r in S else 0
        b["_revision"] = rev
        put(r, b)                              # strict: the body REPLACES the object
        S[r]["_revision"] = rev
        side_effect(r)
        return self.send(200, S[r])

    def injected(self, method, r):
        """A failure injected by /mock/failnext answers the next matching request once, after letting
        "skip" matching requests through."""
        if FAIL and FAIL.get("method") == method and FAIL.get("path") == r:
            if FAIL.get("skip"):
                FAIL["skip"] -= 1
                return False
            code = int(FAIL.get("code") or 503)
            FAIL.clear()
            self.send(code, {"error_message": "injected failure"})
            return True
        return False

    def do_PUT(self):
        p, q = self.rel()
        if p.startswith("/api/") or p.startswith("/policy/"):
            if not self.authed():
                return
        if self.injected("PUT", p[len(GM):] if p.startswith(GM) else p):
            return
        if ROLE in ("green-lm", "lm") and p == GC_PATH:
            b = self.body()
            if b.get("_revision") != GC.get("_revision"):
                return self.send(412, {"error_message": "Object was modified by somebody else"})
            if b.get("vdr_mac") != GC.get("vdr_mac") and not b.get("allow_changing_vdr_mac_in_use"):
                return self.send(400, {"error_message": "VDR MAC in use; set allow_changing_vdr_mac_in_use"})
            GC.update(b)
            GC["_revision"] += 1
            return self.send(200, GC)
        if ROLE in ("green-lm", "lm") and p.startswith("/api/v1/edge-clusters/"):
            b, cid = self.body(), p.split("/")[-1]
            if cid not in ECS:
                return self.send(404, {"error_message": "not found"})
            if b.get("_revision") != ECS[cid]["_revision"]:
                return self.send(412, {"error_message": "Object was modified by somebody else"})
            for m_ in b.get("members") or []:
                if m_.get("transport_node_id") not in TN:
                    return self.send(400, {"error_message": "transport node %s not found" % m_.get("transport_node_id")})
            ECS[cid] = dict(b, id=cid, _revision=ECS[cid]["_revision"] + 1)
            return self.send(200, ECS[cid])
        if ROLE in ("green-lm", "lm") and p.startswith("/api/v1/transport-nodes/"):
            return self.send(400, {"error_message": "the mock refuses edits to a transport node: the tool never modifies one"})
        r = p[len(GM):]
        b = self.body()
        if r in S and b.get("_revision") != S[r].get("_revision"):
            return self.send(412, {"error_message": "Object was modified by somebody else"})
        rev = (S[r]["_revision"] + 1) if r in S else 0
        b["_revision"] = rev
        put(r, b)
        S[r]["_revision"] = rev
        side_effect(r)
        return self.send(200, S[r])

    def do_DELETE(self):
        p, q = self.rel()
        r = p[len(GM):]
        if not p.startswith(GM) or r not in S:
            return self.send(404, {"error_message": "The path=[%s] is invalid" % r})
        if S[r].get("bridge_profiles"):
            return self.send(400, {"error_message": "Segment has a bridge profile attached"})
        del S[r]
        side_effect(r)
        return self.send(200, {})

    def soap(self, inner, fault=None):
        raw = ('<?xml version="1.0" encoding="UTF-8"?><soapenv:Envelope xmlns:soapenv="%s" xmlns:xsd="http://www.w3.org/2001/XMLSchema" '
               'xmlns:xsi="%s"><soapenv:Body>%s</soapenv:Body></soapenv:Envelope>' % (
                   SOAPENV, XSI, ('<soapenv:Fault><faultcode>ServerFaultCode</faultcode><faultstring>%s</faultstring></soapenv:Fault>'
                                  % xesc(fault)) if fault else ('<LoginResponse xmlns="urn:vim25"><returnval><key>k</key>'
                                                                '<userName>u</userName></returnval></LoginResponse>'
                                                                if inner == "LOGIN" else inner))).encode()
        self.send_response(500 if fault else 200)
        self.send_header("Content-Type", "text/xml; charset=utf-8")
        if inner == "LOGIN":
            self.send_header("Set-Cookie", 'vmware_soap_session="%s"; Path=/; HttpOnly; Secure' % TOKEN)
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def vc_sdk(self):
        n = int(self.headers.get("Content-Length") or 0)
        try:
            env = ET.fromstring(self.rfile.read(n))
        except ET.ParseError as e:
            return self.soap(None, "not XML: %s" % e)
        if not (self.headers.get("SOAPAction") or "").startswith('"urn:vim25/'):
            return self.soap(None, "SOAPAction must name the urn:vim25 version")
        body = env.find("{%s}Body" % SOAPENV)
        call = body[0]
        method = call.tag.replace(VIMNS, "")
        if method == "RetrieveServiceContent":
            return self.soap('<RetrieveServiceContentResponse xmlns="urn:vim25"><returnval><rootFolder type="Folder">group-d1</rootFolder>'
                             '<propertyCollector type="PropertyCollector">propertyCollector</propertyCollector>'
                             '<about><instanceUuid>uuid-vc-%d</instanceUuid></about>'
                             '<setting type="OptionManager">VpxSettings</setting>'
                             '<sessionManager type="SessionManager">SessionManager</sessionManager></returnval>'
                             '</RetrieveServiceContentResponse>' % PORTN)
        if method == "Login":
            if call.findtext(VIMNS + "password") != "pw":
                return self.soap(None, "Cannot complete login due to an incorrect user name or password.")
            self.soap("LOGIN")
            return
        if 'vmware_soap_session="%s"' % TOKEN not in (self.headers.get("Cookie") or ""):
            return self.soap(None, "The session is not authenticated.")
        if method == "Logout":
            return self.soap('<LogoutResponse xmlns="urn:vim25"/>')
        if method == "RetrievePropertiesEx":
            objs, typ = [], None
            spec = call.find(VIMNS + "specSet")
            paths = [x.text for x in spec.find(VIMNS + "propSet").findall(VIMNS + "pathSet")]
            for os_ in spec.findall(VIMNS + "objectSet"):
                o = os_.find(VIMNS + "obj")
                objs.append(o.text)
                typ = o.get("type")
            out = []
            for o in objs:
                props = []
                if typ == "DistributedVirtualPortgroup":
                    p_ = VC["pg"].get(o)
                    if not p_:
                        return self.soap(None, "The object '%s:%s' has already been deleted or has not been completely created" % (typ, o))
                    for pa in paths:
                        if pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">%s</val></propSet>' % xesc(p_["name"]))
                        elif pa == "config.distributedVirtualSwitch":
                            props.append('<propSet><name>config.distributedVirtualSwitch</name><val type="VmwareDistributedVirtualSwitch" '
                                         'xsi:type="ManagedObjectReference">%s</val></propSet>' % p_["dvs"])
                        elif pa == "config":
                            props.append('<propSet><name>config</name>%s</propSet>' % pg_xml(o, p_))
                        elif pa == "key":
                            props.append('<propSet><name>key</name><val xsi:type="xsd:string">%s</val></propSet>' % o)
                elif typ == "VmwareDistributedVirtualSwitch" and paths == ["uuid"]:
                    props.append('<propSet><name>uuid</name><val xsi:type="xsd:string">50 99 88 77-%s</val></propSet>' % o)
                elif typ == "VmwareDistributedVirtualSwitch":
                    d = VC["dvs"].get(o)
                    if not d:
                        return self.soap(None, "The object '%s:%s' has already been deleted or has not been completely created" % (typ, o))
                    for pa in paths:
                        if pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">%s</val></propSet>' % d["name"])
                        elif pa == "portgroup":
                            props.append('<propSet><name>portgroup</name><val xsi:type="ArrayOfManagedObjectReference">%s</val></propSet>'
                                         % "".join('<ManagedObjectReference type="DistributedVirtualPortgroup">%s</ManagedObjectReference>'
                                                   % m for m, pg in VC["pg"].items() if pg["dvs"] == o))
                        elif pa == "summary.productInfo.version":
                            props.append('<propSet><name>summary.productInfo.version</name><val xsi:type="xsd:string">%s</val></propSet>'
                                         % d["version"])
                elif typ == "OptionManager":
                    props.append('<propSet><name>setting</name><val xsi:type="ArrayOfOptionValue">%s</val></propSet>' % "".join(
                        '<OptionValue xsi:type="OptionValue"><key>%s</key><value xsi:type="xsd:string">%s</value></OptionValue>'
                        % (xesc(k), xesc(v)) for k, v in sorted(VC["opts"].items())))
                elif typ == "Datastore":
                    nm_, ty_ = ("vsan-ds", "vsan") if o == "datastore-10" else ("local-" + o.rsplit("-", 1)[-1], "VMFS")
                    for pa in paths:
                        if pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">%s</val></propSet>' % nm_)
                        elif pa == "summary.type":
                            props.append('<propSet><name>summary.type</name><val xsi:type="xsd:string">%s</val></propSet>' % ty_)
                elif typ == "Folder":
                    f_ = VC["folders"].get(o)
                    if not f_:
                        return self.soap(None, "The object 'Folder:%s' has already been deleted or has not been completely created" % o)
                    for pa in paths:
                        if pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">%s</val></propSet>' % xesc(f_["name"]))
                        elif pa == "parent":
                            props.append('<propSet><name>parent</name><val type="%s" xsi:type="ManagedObjectReference">%s</val>'
                                         '</propSet>' % f_["parent"])
                        elif pa == "childEntity":
                            kids = ['<ManagedObjectReference type="Folder">%s</ManagedObjectReference>' % m_
                                    for m_, c_ in sorted(VC["folders"].items()) if c_["parent"] == ("Folder", o)]
                            kids += ['<ManagedObjectReference type="VirtualMachine">%s</ManagedObjectReference>' % v["vm"]
                                     for v in VC["vms"].values() if (v.get("folder") or "group-v3") == o]
                            props.append('<propSet><name>childEntity</name><val xsi:type="ArrayOfManagedObjectReference">%s</val>'
                                         '</propSet>' % "".join(kids))
                elif typ == "Datacenter":
                    props.append('<propSet><name>vmFolder</name><val type="Folder" xsi:type="ManagedObjectReference">'
                                 'group-v3</val></propSet>')
                elif typ == "ResourcePool":
                    if o != "resgroup-1":
                        return self.soap(None, "The object 'ResourcePool:%s' has already been deleted or has not been completely created" % o)
                    props.append('<propSet><name>owner</name><val type="ClusterComputeResource" xsi:type="ManagedObjectReference">'
                                 'domain-c8</val></propSet>')
                elif typ == "ClusterComputeResource":
                    if o != "domain-c8":
                        return self.soap(None, "The object 'ClusterComputeResource:%s' has already been deleted or has not been completely created" % o)
                    for pa in paths:
                        if pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">cl01</val></propSet>')
                        elif pa == "resourcePool":
                            props.append('<propSet><name>resourcePool</name><val type="ResourcePool" '
                                         'xsi:type="ManagedObjectReference">resgroup-1</val></propSet>')
                        elif pa == "parent":
                            props.append('<propSet><name>parent</name><val type="Folder" xsi:type="ManagedObjectReference">'
                                         'group-h4</val></propSet>')
                        elif pa == "host":
                            props.append('<propSet><name>host</name><val xsi:type="ArrayOfManagedObjectReference">'
                                         '<ManagedObjectReference type="HostSystem">host-20</ManagedObjectReference>'
                                         '<ManagedObjectReference type="HostSystem">host-21</ManagedObjectReference></val></propSet>')
                        elif pa == "configurationEx":
                            props.append('<propSet><name>configurationEx</name><val xsi:type="ClusterConfigInfoEx">%s</val></propSet>' % "".join(
                                '<rule xsi:type="ClusterAntiAffinityRuleSpec"><key>%d</key><enabled>%s</enabled><name>%s</name>'
                                '<userCreated>true</userCreated>%s</rule>' % (
                                    i + 1, "true" if r_["enabled"] else "false", xesc(r_["name"]),
                                    "".join('<vm type="VirtualMachine">%s</vm>' % v for v in r_["vm"]))
                                for i, r_ in enumerate(VC["rules"])))
                elif typ == "HostSystem":
                    if o not in ("host-20", "host-21"):
                        return self.soap(None, "The object 'HostSystem:%s' has already been deleted or has not been completely created" % o)
                    vms_ = [v["vm"] for n_, v in sorted(VC["vms"].items())]
                    mine = vms_[0::2] if o == "host-20" else vms_[1::2]
                    for pa in paths:
                        if pa == "vm":
                            props.append('<propSet><name>vm</name><val xsi:type="ArrayOfManagedObjectReference">%s</val></propSet>'
                                         % "".join('<ManagedObjectReference type="VirtualMachine">%s</ManagedObjectReference>' % v
                                                   for v in mine))
                        elif pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">esx%s.example.com</val></propSet>'
                                         % o.split("-")[1])
                        elif pa == "parent":
                            props.append('<propSet><name>parent</name><val type="ClusterComputeResource" '
                                         'xsi:type="ManagedObjectReference">domain-c8</val></propSet>')
                        elif pa == "runtime.connectionState":
                            props.append('<propSet><name>runtime.connectionState</name><val xsi:type="HostSystemConnectionState">'
                                         'connected</val></propSet>')
                        elif pa == "runtime.inMaintenanceMode":
                            props.append('<propSet><name>runtime.inMaintenanceMode</name><val xsi:type="xsd:boolean">%s</val>'
                                         '</propSet>' % ("true" if VC.get("maint") == o else "false"))
                        elif pa == "network":
                            props.append('<propSet><name>network</name><val xsi:type="ArrayOfManagedObjectReference">%s</val></propSet>'
                                         % "".join('<ManagedObjectReference type="DistributedVirtualPortgroup">%s</ManagedObjectReference>'
                                                   % m_ for m_ in sorted(VC["pg"])))
                        elif pa == "datastore":         # the shared vSAN datastore, and a local one per host
                            props.append('<propSet><name>datastore</name><val xsi:type="ArrayOfManagedObjectReference">'
                                         '<ManagedObjectReference type="Datastore">datastore-10</ManagedObjectReference>'
                                         '<ManagedObjectReference type="Datastore">datastore-local-%s</ManagedObjectReference>'
                                         '</val></propSet>' % o.split("-")[1])
                elif typ == "VirtualMachine":
                    v_ = next((dict(x, name=n_) for n_, x in VC["vms"].items() if x["vm"] == o), None)
                    if not v_:
                        return self.soap(None, "The object 'VirtualMachine:%s' has already been deleted or has not been completely created" % o)
                    for pa in paths:
                        if pa == "name":
                            props.append('<propSet><name>name</name><val xsi:type="xsd:string">%s</val></propSet>' % xesc(v_["name"]))
                        elif pa == "runtime.host":
                            props.append('<propSet><name>runtime.host</name><val type="HostSystem" xsi:type="ManagedObjectReference">'
                                         'host-21</val></propSet>')
                        elif pa == "resourcePool":
                            props.append('<propSet><name>resourcePool</name><val type="ResourcePool" xsi:type="ManagedObjectReference">'
                                         'resgroup-1</val></propSet>')
                        elif pa == "parent":
                            props.append('<propSet><name>parent</name><val type="Folder" xsi:type="ManagedObjectReference">'
                                         '%s</val></propSet>' % (v_.get("folder") or "group-v3"))
                        elif pa == "config.files.vmPathName":
                            props.append('<propSet><name>config.files.vmPathName</name><val xsi:type="xsd:string">[vsan-ds] %s/%s.vmx'
                                         '</val></propSet>' % (xesc(v_["name"]), xesc(v_["name"])))
                        elif pa == "config.hardware.device":
                            pgk = VC["nets"].get(v_.get("network")) or "dvportgroup-0"
                            props.append(
                                '<propSet><name>config.hardware.device</name><val xsi:type="ArrayOfVirtualDevice">'
                                '<VirtualDevice xsi:type="VirtualDisk"><key>2000</key><deviceInfo><label>Hard disk 1</label>'
                                '<summary>16 GB</summary></deviceInfo><controllerKey>1000</controllerKey><unitNumber>0</unitNumber>'
                                '<capacityInKB>16777216</capacityInKB></VirtualDevice>'
                                '<VirtualDevice xsi:type="VirtualVmxnet3"><key>4000</key><deviceInfo><label>Network adapter 1</label>'
                                '<summary>%s</summary></deviceInfo>'
                                '<backing xsi:type="VirtualEthernetCardDistributedVirtualPortBackingInfo"><port>'
                                '<switchUuid>50 1a 2b 3c-src</switchUuid><portgroupKey>%s</portgroupKey><portKey>12</portKey>'
                                '</port></backing><connectable><startConnected>true</startConnected><allowGuestControl>true'
                                '</allowGuestControl><connected>true</connected><status>ok</status></connectable>'
                                '<slotInfo xsi:type="VirtualDevicePciBusSlotInfo"><pciSlotNumber>192</pciSlotNumber></slotInfo>'
                                '<controllerKey>100</controllerKey><unitNumber>7</unitNumber><addressType>assigned</addressType>'
                                '<macAddress>00:50:56:b2:56:%02x</macAddress><wakeOnLanEnabled>true</wakeOnLanEnabled>'
                                '</VirtualDevice></val></propSet>' % (xesc(v_.get("network") or ""), pgk, int(o.split("-")[1]) % 256))
                elif typ == "Task":
                    t = VC["tasks"].get(o)
                    if not t:
                        return self.soap(None, "The object 'Task:%s' has already been deleted or has not been completely created" % o)
                    t["polls"] += 1
                    state = t["state"] if t["polls"] > 1 else "running"
                    props.append('<propSet><name>info</name><val xsi:type="TaskInfo"><key>%s</key><task type="Task">%s</task>'
                                 '<state>%s</state>%s</val></propSet>' % (o, o, state, (
                                     '<result type="DistributedVirtualPortgroup" xsi:type="ManagedObjectReference">%s</result>' % t["result"]
                                     if state == "success" and t.get("result") else
                                     '<error><localizedMessage>%s</localizedMessage></error>' % xesc(t["error"]) if state == "error" else "")))
                else:
                    return self.soap(None, "the mock serves no %s properties" % typ)
                out.append('<objects><obj type="%s">%s</obj>%s</objects>' % (typ, o, "".join(props)))
            return self.soap('<RetrievePropertiesExResponse xmlns="urn:vim25"><returnval>%s</returnval></RetrievePropertiesExResponse>'
                             % "".join(out))
        if method in ("CreateDVPortgroup_Task", "ReconfigureDVPortgroup_Task"):
            this = call.find(VIMNS + "_this")
            spec = call.find(VIMNS + "spec")
            VC["n"] += 1
            tid = "task-%d" % VC["n"]
            task = {"state": "success", "polls": 0}
            VC["tasks"][tid] = task
            try:
                if VCFAIL.get("task"):
                    raise ValueError(VCFAIL.pop("task"))
                if method == "CreateDVPortgroup_Task":
                    if this.get("type") != "VmwareDistributedVirtualSwitch" or this.text not in VC["dvs"]:
                        raise ValueError("_this is not a VDS of this vCenter: %s %s" % (this.get("type"), this.text))
                    p_ = pg_from_spec(spec)
                    if not p_["name"]:
                        raise ValueError("A specified parameter was not correct: spec.name")
                    if any(x["name"] == p_["name"] and x["dvs"] == this.text for x in VC["pg"].values()):
                        raise ValueError("The name '%s' already exists." % p_["name"])
                    moref = "dvportgroup-%d" % (300 + VC["n"])
                    p_["dvs"], p_["version"] = this.text, "1"
                    VC["pg"][moref], VC["nets"][p_["name"]] = p_, moref
                    task["result"] = moref
                else:
                    if this.get("type") != "DistributedVirtualPortgroup" or this.text not in VC["pg"]:
                        raise ValueError("_this is not a port group of this vCenter")
                    cur = VC["pg"][this.text]
                    if spec.findtext(VIMNS + "configVersion") != cur["version"]:
                        raise ValueError("Cannot complete operation due to concurrent modification by another operation.")
                    p_ = pg_from_spec(spec, cur)
                    p_["version"] = str(int(cur["version"]) + 1)
                    VC["pg"][this.text] = p_
            except ValueError as e:
                task.update(state="error", error=str(e))
            return self.soap('<%sResponse xmlns="urn:vim25"><returnval type="Task">%s</returnval></%sResponse>' % (method, tid, method))
        if method == "CreateFolder":
            this, nm = call.find(VIMNS + "_this"), call.findtext(VIMNS + "name") or ""
            if this is None or this.get("type") != "Folder" or this.text not in VC["folders"]:
                return self.soap(None, "The object 'Folder:%s' has already been deleted or has not been completely created"
                                 % (this.text if this is not None else ""))
            shown = nm.replace("%", "%25").replace("/", "%2f").replace("\\", "%5c")
            if any(c_["parent"] == ("Folder", this.text) and c_["name"].lower() == shown.lower() for c_ in VC["folders"].values()):
                return self.soap(None, "The name '%s' already exists." % nm)
            VC["n"] += 1
            mo = "group-v%d" % (100 + VC["n"])
            VC["folders"][mo] = {"name": shown, "parent": ("Folder", this.text)}
            return self.soap('<CreateFolderResponse xmlns="urn:vim25"><returnval type="Folder">%s</returnval>'
                             '</CreateFolderResponse>' % mo)
        if method == "UpdateOptions":
            if call.findtext(VIMNS + "_this") != "VpxSettings":
                return self.soap(None, "_this is not this vCenter's settings")
            for cv in call.findall(VIMNS + "changedValue"):
                val = cv.find(VIMNS + "value")
                if [k.tag.replace(VIMNS, "") for k in cv] != ["key", "value"] or val.get("{%s}type" % XSI) != "xsd:string":
                    return self.soap(None, "A specified parameter was not correct: changedValue")
                VC["opts"][cv.findtext(VIMNS + "key")] = val.text or ""
            return self.soap('<UpdateOptionsResponse xmlns="urn:vim25"/>')
        if method == "RelocateVM_Task":
            this, spec = call.find(VIMNS + "_this"), call.find(VIMNS + "spec")
            VC["n"] += 1
            tid = "task-%d" % VC["n"]
            task = {"state": "success", "polls": 0}
            VC["tasks"][tid] = task
            try:
                if VCFAIL.get("task"):
                    raise ValueError(VCFAIL.pop("task"))
                name = next((n_ for n_, x in VC["vms"].items() if x["vm"] == this.text), None)
                if this.get("type") != "VirtualMachine" or not name:
                    raise ValueError("_this is not a VM of this vCenter: %s" % this.text)
                if VC["opts"].get("config.vpxd.network.allowVmotionBetweenLogicalSwitches") != "true":
                    raise ValueError("the type of the destination network is not supported for vMotion based on the "
                                     "source network type")
                order = ["service", "folder", "datastore", "diskMoveType", "pool", "host", "disk", "transform",
                         "deviceChange", "profile", "cryptoSpec"]
                kids = [k.tag.replace(VIMNS, "") for k in spec]
                if [order.index(k) for k in kids] != sorted(order.index(k) for k in kids):
                    raise ValueError("VirtualMachineRelocateSpec fields out of schema order: %s" % kids)
                sv = spec.find(VIMNS + "service")
                if [k.tag.replace(VIMNS, "") for k in sv] != ["instanceUuid", "url", "credential", "sslThumbprint"]:
                    raise ValueError("ServiceLocator fields: %s" % [k.tag for k in sv])
                cr = sv.find(VIMNS + "credential")
                if cr.get("{%s}type" % XSI) != "ServiceLocatorNamePassword" or cr.findtext(VIMNS + "password") != "pw":
                    raise ValueError("Login to the destination vCenter failed: incorrect user name or password")
                if not re.fullmatch(r"([0-9A-F]{2}:){19}[0-9A-F]{2}", sv.findtext(VIMNS + "sslThumbprint") or ""):
                    raise ValueError("sslThumbprint is not a SHA-1 thumbprint")
                for k, t in (("folder", "Folder"), ("datastore", "Datastore"), ("pool", "ResourcePool"), ("host", "HostSystem")):
                    if spec.find(VIMNS + k) is None or spec.find(VIMNS + k).get("type") != t:
                        raise ValueError("spec.%s missing or not a %s" % (k, t))
                dest_net = None
                for dc in spec.findall(VIMNS + "deviceChange"):
                    if [k.tag.replace(VIMNS, "") for k in dc] != ["operation", "device"] or dc.findtext(VIMNS + "operation") != "edit":
                        raise ValueError("deviceChange must be operation edit, then device")
                    dev = dc.find(VIMNS + "device")
                    b = dev.find(VIMNS + "backing")
                    if dev.findtext(VIMNS + "key") != "4000" or dev.findtext(VIMNS + "macAddress") is None or b is None \
                            or b.get("{%s}type" % XSI) != "VirtualEthernetCardDistributedVirtualPortBackingInfo" \
                            or [k.tag.replace(VIMNS, "") for k in b.find(VIMNS + "port")] != ["switchUuid", "portgroupKey"]:
                        raise ValueError("A specified parameter was not correct: deviceChange.device")
                    dest_net = b.findtext(VIMNS + "port/" + VIMNS + "portgroupKey")
                if not dest_net:
                    raise ValueError("no network adapter in deviceChange")
                url = sv.findtext(VIMNS + "url")
                hp = re.match(r"https://([^/]+)/sdk$", url or "")
                if not hp:
                    raise ValueError("service.url: %s" % url)
                rq = urllib.request.Request("https://%s/mock/vm" % hp.group(1), method="POST",
                                            data=json.dumps({"name": name, "pgkey": dest_net, "ip": VC["vms"][name].get("ip"),
                                                             "folder": spec.findtext(VIMNS + "folder")}).encode(),
                                            headers={"Content-Type": "application/json"})
                c_ = ssl.create_default_context()
                c_.check_hostname, c_.verify_mode = False, ssl.CERT_NONE
                urllib.request.urlopen(rq, context=c_, timeout=10).read()
                VC["moves"].append({"vm": name, "host": spec.findtext(VIMNS + "host"), "pgkey": dest_net,
                                    "folder": spec.findtext(VIMNS + "folder"),
                                    "thumb": sv.findtext(VIMNS + "sslThumbprint"), "uuid": sv.findtext(VIMNS + "instanceUuid")})
                VC["vms"].pop(name)
            except ValueError as e:
                task.update(state="error", error=str(e))
            return self.soap('<%sResponse xmlns="urn:vim25"><returnval type="Task">%s</returnval></%sResponse>' % (method, tid, method))
        if method == "ReconfigureComputeResource_Task":
            this, spec = call.find(VIMNS + "_this"), call.find(VIMNS + "spec")
            VC["n"] += 1
            tid = "task-%d" % VC["n"]
            task = {"state": "success", "polls": 0}
            VC["tasks"][tid] = task
            try:
                if VCFAIL.get("task"):
                    raise ValueError(VCFAIL.pop("task"))
                if this.get("type") != "ClusterComputeResource" or this.text != "domain-c8":
                    raise ValueError("_this is not a cluster of this vCenter: %s %s" % (this.get("type"), this.text))
                if spec is None or spec.get("{%s}type" % XSI) != "ClusterConfigSpecEx" or call.findtext(VIMNS + "modify") != "true":
                    raise ValueError("A specified parameter was not correct: spec")
                kids = [k.tag.replace(VIMNS, "") for k in spec]
                if kids != ["rulesSpec"]:
                    raise ValueError("the mock takes rulesSpec alone, got %s" % kids)
                rs = spec.find(VIMNS + "rulesSpec")
                if [k.tag.replace(VIMNS, "") for k in rs] != ["operation", "info"] or rs.findtext(VIMNS + "operation") != "add":
                    raise ValueError("rulesSpec must be operation add, then info (in that order)")
                info = rs.find(VIMNS + "info")
                if info.get("{%s}type" % XSI) != "ClusterAntiAffinityRuleSpec":
                    raise ValueError("the mock takes ClusterAntiAffinityRuleSpec only")
                order = [k.tag.replace(VIMNS, "") for k in info]
                allowed = ["key", "status", "enabled", "name", "mandatory", "userCreated", "inCompliance", "ruleUuid", "vm"]
                idx = [allowed.index(k) for k in order]
                if idx != sorted(idx) or "vm" not in order or "name" not in order:
                    raise ValueError("ClusterAntiAffinityRuleSpec fields out of schema order: %s" % order)
                vms_ = [v.text for v in info.findall(VIMNS + "vm")]
                known = {x["vm"] for x in VC["vms"].values()}
                if len(vms_) < 2 or not set(vms_) <= known or any(v.get("type") != "VirtualMachine" for v in info.findall(VIMNS + "vm")):
                    raise ValueError("A specified parameter was not correct: spec.rulesSpec.info.vm")
                if any(r_["name"] == info.findtext(VIMNS + "name") for r_ in VC["rules"]):
                    raise ValueError("The name '%s' already exists." % info.findtext(VIMNS + "name"))
                VC["rules"].append({"name": info.findtext(VIMNS + "name"), "enabled": info.findtext(VIMNS + "enabled") == "true", "vm": vms_})
            except ValueError as e:
                task.update(state="error", error=str(e))
            return self.soap('<%sResponse xmlns="urn:vim25"><returnval type="Task">%s</returnval></%sResponse>' % (method, tid, method))
        return self.soap(None, "the mock serves no %s" % method)

    def do_POST(self):
        p, q = self.rel()
        if p.startswith("/api/") or p.startswith("/policy/"):
            if not self.authed():
                return
        if ROLE == "vc" and p == "/sdk":
            return self.vc_sdk()
        if ROLE in ("green-lm", "lm") and p == "/api/v1/transport-nodes":
            if self.injected("POST", p):
                return
            b = self.body()
            ndi = b.get("node_deployment_info") or {}
            dc = ndi.get("deployment_config") or {}
            vdc = dc.get("vm_deployment_config") or {}
            us = dc.get("node_user_settings") or {}
            name = b.get("display_name")
            bad = None
            if any(k in b for k in ("id", "_revision", "_create_time")) or any(k in ndi for k in ("id", "external_id", "fqdn", "_revision")):
                bad = "read-only field in the body"
            elif any("host_switch_id" in hs for hs in (b.get("host_switch_spec") or {}).get("host_switches") or []):
                bad = "host_switch_id is read-only"
            elif any(t["display_name"] == name for t in TN.values()):
                bad = "Transport node %s already exists" % name
            elif not (us.get("cli_password") and us.get("root_password") and us.get("cli_username")):
                bad = "node_user_settings: cli_username, cli_password and root_password are required"
            elif not (ndi.get("node_settings") or {}).get("hostname"):
                bad = "node_settings.hostname is required"
            elif not vdc.get("management_port_subnets") or not vdc.get("vc_id") or not vdc.get("compute_id") \
                    or not vdc.get("storage_id") or not vdc.get("management_network_id"):
                bad = "vm_deployment_config is incomplete"
            elif dc.get("form_factor") not in ("SMALL", "MEDIUM", "LARGE", "XLARGE"):
                bad = "form_factor"
            elif len(vdc.get("data_network_ids") or []) < 1 + max(int(x["device_name"][-1]) for hs in b["host_switch_spec"]["host_switches"]
                                                                 for x in hs.get("pnics") or []):
                bad = "data_network_ids: fewer networks than fastpath vNICs in use"
            elif any(z.get("transport_zone_id") not in {v["realization_id"] for v in PTZ.values()}
                     for hs in b["host_switch_spec"]["host_switches"] for z in hs.get("transport_zone_endpoints") or []):
                bad = "transport_zone_id not found"
            elif any(pr.get("value") not in {v["id"] for v in HSP.values()} for hs in b["host_switch_spec"]["host_switches"]
                     for pr in hs.get("host_switch_profile_ids") or []):
                bad = "host switch profile not found"
            if bad:
                return self.send(400, {"error_message": bad, "error_code": 8000})
            VC["n"] = VC.get("n", 0) + 1
            tid = "tn-%s" % name
            t = copy.deepcopy(b)
            t.update(id=tid, _revision=0, _create_time=1, _state="failed" if EDGEFAIL.pop(name, None) else "deploying", _polls=0)
            t["node_deployment_info"].update(id=tid, external_id=tid, fqdn=t["node_deployment_info"]["node_settings"]["hostname"],
                                             ip_addresses=list(vdc["management_port_subnets"][0]["ip_addresses"]))
            TN[tid] = t
            return self.send(201, tn_view(t))
        if ROLE in ("green-lm", "lm") and p == "/api/v1/edge-clusters":
            b = self.body()
            if any(c["display_name"] == b.get("display_name") for c in ECS.values()):
                return self.send(400, {"error_message": "Edge cluster %s already exists" % b.get("display_name")})
            for m_ in b.get("members") or []:
                if m_.get("transport_node_id") not in TN:
                    return self.send(400, {"error_message": "transport node %s not found" % m_.get("transport_node_id")})
                if TN[m_["transport_node_id"]].get("_state") not in (None, "ready"):
                    return self.send(400, {"error_message": "transport node %s is not ready" % m_["transport_node_id"]})
            VC["n"] = VC.get("n", 0) + 1
            cid = "ec-%d" % VC["n"]
            ECS[cid] = dict(b, id=cid, _revision=0)
            return self.send(201, ECS[cid])
        if p == "/mock/edgefail":              # test hook: the next edge of this name fails to deploy
            b = self.body()
            EDGEFAIL[b["name"]] = True
            return self.send(200, EDGEFAIL)
        if p == "/mock/dvs":                   # test hook: the VDS as vSphere reports it (version)
            VC["dvs"]["dvs-1"].update(self.body())
            return self.send(200, VC["dvs"])
        if p == "/mock/vcfail":                # test hook: the next vCenter task fails with this message
            VCFAIL["task"] = self.body().get("message") or "injected failure"
            return self.send(200, VCFAIL)
        if p == "/mock/pg":                    # test hook: a port group made by hand
            b = self.body()
            moref = vc_net(b["name"])
            VC["pg"][moref].update({k: v for k, v in b.items() if k != "name"})
            if b.get("trunk"):
                VC["pg"][moref]["trunk"] = [tuple(x) for x in b["trunk"]]
            return self.send(200, {"moref": moref})
        if p == "/mock/edge":                  # test hook: an edge on this Local Manager, or gone
            b = self.body()
            if b.get("remove"):
                for k in [k for k, t in TN.items() if t["display_name"] == b["name"]]:
                    del TN[k]
                return self.send(200, {})
            t = edge_obj(b["name"], b["ip"], ["dvportgroup-201", "dvportgroup-202"] * (2 if b.get("uplink_switch") else 1),
                         static=bool(b.get("static")), tzs=b.get("tzs") or ["uuid-tz-ov"], uplink_switch=b.get("uplink_switch"))
            if b.get("tags"):
                t["tags"] = b["tags"]
            TN[t["id"]] = t
            return self.send(200, tn_view(t))
        if ROLE == "vc" and p == "/api/session":
            if not (self.headers.get("Authorization") or "").startswith("Basic "):
                return self.send(401, {"error_type": "UNAUTHENTICATED"})
            return self.send(201, TOKEN)
        if ROLE in ("green-lm", "lm") and p == FVM_PATH and q.get("action") == ["add_tags"]:
            b = self.body()
            v = next((x for x in FVM.values() if x["external_id"] == b.get("external_id")), None)
            if not v:
                return self.send(404, {"error_message": "VM not found"})
            for t in b.get("tags") or []:
                if t not in v["tags"]:
                    v["tags"].append(t)
            return self.send(204, None)
        if p == "/mock/reset":
            seed()
            return self.send(200, {"ok": True})
        if p == "/mock/state":
            return self.send(200, {"S": S, "LM": LM, "GC": GC, "FVM": FVM, "VC": VC, "ECS": ECS, "PTZ": PTZ,
                                   "TN": {k: {kk: vv for kk, vv in t.items() if kk != "_polls"} for k, t in TN.items()}})
        if p == "/mock/merge":                 # test hook: change an object as if done by hand
            b = self.body()
            o = S[b["path"]]
            o.update(b["merge"])
            o["_revision"] += 1
            return self.send(200, o)
        if p == "/mock/put":                   # test hook: an object created by hand
            b = self.body()
            put(b["path"], b["obj"])
            return self.send(200, S[b["path"]])
        if p == "/mock/sideeffect":            # test hook: {"on": path, "touch": path}, or {} to clear
            SIDE.clear()
            SIDE.update(self.body())
            return self.send(200, SIDE)
        if p == "/mock/failnext":              # test hook: {"method", "path", "code"}: the next match fails once
            FAIL.clear()
            FAIL.update(self.body())
            return self.send(200, FAIL)
        if p == "/mock/alarm":                 # test hook: an alarm opens on this manager
            b = self.body()
            ALARMS[b["id"]] = b
            return self.send(200, b)
        if p == "/mock/gc":                    # test hook: router MAC changed on this Local Manager
            GC.update(self.body())
            GC["_revision"] += 1
            return self.send(200, GC)
        if p == "/mock/attach":                # test hook: zone attached to an edge on the LM
            b = self.body()
            LM.setdefault(b["node"], []).append(b["tz"])
            return self.send(200, {"ok": True})
        if p == "/mock/fvm":                   # test hook: a VM in this Local Manager's inventory, or every VM
            b = self.body()                    # of that name gone from it. Names need not be unique; ids are.
            if b.get("remove"):
                for k in [k for k, v in FVM.items() if v["display_name"] == b["name"]]:
                    del FVM[k]
                return self.send(200, {})
            FVM[b["external_id"]] = {"display_name": b["name"], "external_id": b["external_id"],
                                     "tags": copy.deepcopy(b.get("tags") or [])}
            return self.send(200, FVM[b["external_id"]])
        if p == "/mock/vm":                    # test hook: a VM on this vCenter (network by name), or gone
            b = self.body()
            if b.get("remove"):
                VC["vms"].pop(b["name"], None)
                return self.send(200, {})
            if b.get("pgkey"):
                b["network"] = (VC["pg"].get(b["pgkey"]) or {}).get("name")
            if b.get("network"):
                vc_net(b["network"])
            old = VC["vms"].get(b["name"]) or {}
            VC["n"] += 1
            VC["vms"][b["name"]] = {"vm": b.get("vm") or old.get("vm") or "vm-%d" % (1000 + VC["n"]), "network": b.get("network"),
                                    "ip": b.get("ip"), "power_state": b.get("power_state", "POWERED_ON"),
                                    "folder": b.get("folder") or old.get("folder") or "group-v3"}
            return self.send(200, VC["vms"][b["name"]])
        if p == "/mock/rules":                 # test hook: the cluster's anti-affinity rules, or one added by hand
            b = self.body() or {}
            if b.get("name"):
                VC["rules"].append({"name": b["name"], "enabled": b.get("enabled", True),
                                    "vm": [VC["vms"][n_]["vm"] for n_ in b.get("vms") or [] if n_ in VC["vms"]]})
            return self.send(200, VC["rules"])
        if p == "/mock/folder":                # test hook: a folder path under the VM folder, made where missing
            cur = "group-v3"
            for nm in [x for x in (self.body().get("path") or "").split("/") if x]:
                hit = next((m_ for m_, c_ in VC["folders"].items() if c_["parent"] == ("Folder", cur) and c_["name"] == nm), None)
                if not hit:
                    VC["n"] += 1
                    hit = "group-v%d" % (100 + VC["n"])
                    VC["folders"][hit] = {"name": nm, "parent": ("Folder", cur)}
                cur = hit
            return self.send(200, {"moref": cur})
        if p == "/mock/folders":               # test hook: every folder as its path, and the folder of each VM

            def path_of(m_):
                out = []
                while m_ in VC["folders"] and m_ != "group-v3":
                    out.insert(0, VC["folders"][m_]["name"])
                    m_ = VC["folders"][m_]["parent"][1]
                return "/".join(out)
            return self.send(200, {"folders": sorted(path_of(m_) for m_ in VC["folders"] if m_ not in ("group-v3", "group-h4")),
                                   "vms": {n_: path_of(v.get("folder") or "group-v3") for n_, v in VC["vms"].items()}})
        if p == "/mock/opts":                  # test hook: the vCenter's advanced settings, and the moves it ran
            return self.send(200, {"opts": VC["opts"], "moves": VC["moves"]})
        if p == "/mock/net":                   # test hook: a network with no VM on it
            return self.send(200, {"network": vc_net(self.body()["name"])})
        return self.send(404, {})


if __name__ == "__main__":
    seed()
    srv = ThreadingHTTPServer(("127.0.0.1", int(sys.argv[2])), H)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.load_cert_chain(sys.argv[3], sys.argv[4])
    srv.socket = ctx.wrap_socket(srv.socket, server_side=True)
    srv.serve_forever()
