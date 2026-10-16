#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fleetparity.py -- VCF 9.x fleet parity check, NSX Federation worksheets, and migpath

Noah Farshad  <noah@essential.coach>
v1.24.1  2026-10-13

run, collect and compare collect the same inventory from VCF Operations (API,
CaSA, vcopsdb, bridge logs), from each SDDC Manager (API, and platform DB when
local), and from each NSX Local Manager, then compare them per domain and
across instances. Anything that differs is flagged; everything collected is
written out in full. Those three are read-only: HTTP GET, POST to ../query
endpoints, SQL SELECT, log reads.

When two or more NSX Local Managers are found, they also produce the NSX
Federation readiness worksheets. VCF does not deploy or manage Global
Managers, so those steps are manual; the worksheets are what they need:
readiness.txt, dns_records.csv, ip_allocation.csv, dci_firewall.csv,
validation.txt.

fedapply converges the stretched Tier-0's north-south configuration, and
migpath moves segments and their VMs from one NSX Federation (Blue) to
another (Green) over edge bridges, one subnet at a time. Both plan by
default and write only with --commit.

Python 3, standard library only. PyYAML is used when it is installed.

Usage
  python3 fleetparity.py run --config env.yaml        # one command, from the Ops primary
  python3 fleetparity.py run --plan --config env.yaml # print the calls, execute nothing

  Split workflow (only if a node is unreachable from the Ops primary):
  python3 fleetparity.py collect --tag <instance> --config env.yaml
  python3 fleetparity.py compare <bundles...> --config env.yaml
  python3 fleetparity.py migpath --config env.yaml [--commit|--test --setup|--edges|--cutover SUBNET|... [--remove]]

Credentials: environment variable, then config file, then interactive prompt.
Never on the command line. Never written to disk. Secret-looking fields are
redacted before anything is serialised.

Exit codes: 0 no deltas, 1 deltas flagged, 2 collection error.
"""

from __future__ import print_function

import argparse
import atexit
import base64
import collections
import csv
import datetime
import fnmatch
import ipaddress
import getpass
import glob
import gzip
import hashlib
import io
import json
import os
import re
import shutil
import signal
import socket
import ssl
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from xml.sax.saxutils import escape as xml_escape

__version__ = "1.24.1"
TOOL = "fleetparity"

# ------------------------------------------------------------------ constants
CTX = ssl.create_default_context()
CTX.check_hostname = False
CTX.verify_mode = ssl.CERT_NONE

LIST_KEYS = (
    "vcfPasswordAccounts", "vcfCertificates", "certificates", "accounts",
    "adapterInstancesInfoDto", "resourceList", "collector", "slices",
    "elements", "credentials", "hosts", "domains", "clusters", "networkPools",
)
SECRET_KEY = re.compile(
    r"(passw|secret|token|private|hash|encrypt|^fields$|credential_?value|"
    r"^key$|api_?key|ssh_?key|private_?key|salt|cipher|ciphertext)", re.I)
SAFE = re.compile(r"[^A-Za-z0-9_.-]+")
FQDN = re.compile(r"^[a-z0-9]([a-z0-9-]*[a-z0-9])?(\.[a-z0-9]([a-z0-9-]*[a-z0-9])?)+$", re.I)
ROW_CAP = 5000
PAGE = 1000

OPS_LOGDIR = "/storage/log/vcops/log"
OPS_PSQL_CANDIDATES = ("/opt/vmware/vpostgres/current/bin/psql",)
SDDC_PSQL_CANDIDATES = ("psql", "/usr/pgsql/13/bin/psql") + tuple(
    sorted(glob.glob("/usr/pgsql/*/bin/psql"), reverse=True))

OPS_TABLE_PAT = re.compile(r"vcf|fleet|password|certificate|lcm|locker|sddc|"
                           r"^resource$|^adapter$|^credential$", re.I)
SDDC_TABLE_PAT = re.compile(r"credential|host|domain|cluster|vcenter|nsx|"
                            r"network|pool|lock|task|resource|workflow|"
                            r"password|certificate|sso|psc|edge|license", re.I)
FLEET_TABLE_PAT = re.compile(r"sddc|vm_|environment|product|locker|password|"
                             r"certificate|datacenter|request", re.I)

# vcops-bridge log patterns (product format; not site specific)
RX_KV = re.compile(r"-(?P<type>[A-Z_]+)-(?P<fqdn>[a-z0-9.-]+)-SSH-(?P<user>[A-Za-z0-9_.@-]+)"
                   r"-(?P<uuid>[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})"
                   r"_(?P<epoch>\d{13})")
RX_CANCEL = re.compile(r"not of primary vim instance")
RX_ADAPTERINFO = re.compile(r"Unable to get AdapterInstanceInfo for adapter name = (\S+), "
                            r"uuid = ([0-9a-f-]{36})")
RX_STALE = re.compile(r"Ignoring stale collection cycle.*?vimInstanceId=([0-9a-f-]{36})")
RX_VIM = re.compile(r"vimInstanceId=([0-9a-f-]{36})")
RX_OPSERR = re.compile(r"\b(ERROR|WARN)\b.*?(fleet|lcm|locker|password|certificate|token|expired|"
                       r"401|403|unauthori|forbidden|sddc)", re.I)
RX_LINE_TS = re.compile(r"^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2})")

PLAN = []          # populated in --plan mode
_DP = {}           # edge datapath read, shared with the verdict
DRY = False


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def log(msg):
    print("[%s] %s" % (datetime.datetime.now().strftime("%H:%M:%S"), msg))


# ---------------------------------------------------------------- config
def read_config(path):
    """YAML via PyYAML if importable; else JSON; else the minimal reader below. A block named after a
    site ("site-a:" with that site's keys under it) is read as the <key>_<site> keys the tool uses."""
    if not path:
        return {}
    if not os.path.exists(path):
        sys.exit("config not found: %s" % path)
    mode = stat.S_IMODE(os.stat(path).st_mode)
    with open(path) as fh:
        text = fh.read()
    has_secret = re.search(r"^[ \t]*[^#\n]*passw[^:\n]*:[ \t]*[^#\s]", text, re.I | re.M)
    if mode & 0o077 and has_secret:
        log("WARNING: %s contains a password and is readable by others (mode %o). "
            "Run: chmod 600 %s" % (path, mode, path))
    try:
        import yaml  # type: ignore
        raw = yaml.safe_load(text) or {}
    except ImportError:
        try:
            raw = json.loads(text)
        except Exception:
            raw = _cfg_text(text)
    if isinstance(raw, dict) and isinstance(raw.get("sites"), dict):
        return _cfg_v2(raw, path)
    return _cfg_sites(raw, path)


def _cfg_uncomment(raw):
    """The line without its comment, by YAML's rule: a # at the start of the line or after a space, and
    outside quotes. A password such as 'a#b' or "x #y" keeps its #."""
    q, i, n = None, 0, len(raw)
    while i < n:
        ch = raw[i]
        if q == '"':
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                q = None
        elif q == "'":
            if ch == "'":
                if i + 1 < n and raw[i + 1] == "'":
                    i += 2
                    continue
                q = None
        elif ch in "'\"" and (i == 0 or raw[i - 1] in " \t[,:"):
            q = ch
        elif ch == "#" and (i == 0 or raw[i - 1] in " \t"):
            return raw[:i]
        i += 1
    return raw


def _cfg_unquote(v):
    """A scalar as YAML reads it: '...' ('' is one '), "..." (\\" and \\\\), else as written."""
    v = v.strip()
    if len(v) >= 2 and v[0] == v[-1] == "'":
        return v[1:-1].replace("''", "'")
    if len(v) >= 2 and v[0] == v[-1] == '"':
        return re.sub(r'\\(["\\])', r"\1", v[1:-1])
    return v


def _cfg_items(s):
    """The items inside a flow list [a, 'b,c'], split on the commas outside quotes."""
    out, cur, q = [], "", None
    for ch in s:
        if q:
            cur += ch
            if ch == q:
                q = None
        elif ch in "'\"" and not cur.strip():
            q, cur = ch, cur + ch
        elif ch == ",":
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [_cfg_unquote(x) for x in out if x.strip()]


def _cfg_text(text):
    """Minimal YAML reader: "key: value", "key: [a, b]" (also over several lines), and blocks nested by
    indentation (a key with nothing after it, its keys indented under it). A block left empty reads as
    blank. Quotes and comments as YAML has them. Sufficient for this tool's config."""
    root, stack, opened = {}, [(-1, {})], []
    stack[0] = (-1, root)
    pending, buf = None, ""
    for raw in text.splitlines():
        line = _cfg_uncomment(raw).rstrip()
        if pending is not None:
            buf += " " + line.strip()
            if "]" in line:
                items = buf[:buf.rindex("]")]
                pending[0][pending[1]] = _cfg_items(items)
                pending, buf = None, ""
            continue
        if not line.strip() or ":" not in line:
            continue
        ind = len(line) - len(line.lstrip(" \t"))
        while len(stack) > 1 and stack[-1][0] >= ind:
            stack.pop()
        dst = stack[-1][1]
        k, v = line.split(":", 1)
        k, v = k.strip().strip("'\""), v.strip()
        if not v:
            dst[k] = {}
            opened.append((dst, k))
            stack.append((ind, dst[k]))
            continue
        if v.startswith("[") and "]" not in v:
            pending, buf = (dst, k), v[1:]
            continue
        dst[k] = _cfg_items(v[1:-1]) if v.startswith("[") and v.endswith("]") else _cfg_unquote(v)
    for d, k in opened:
        if d.get(k) == {}:
            d[k] = ""
    return root


# ---- the config as people write it: shared settings, then sites.<site> with blue and green under each.
# Blue is the NSX the segments and VMs leave; Green the one they land on. Each entry: the place in the
# file -> the key the tool reads (a site's keys get _<site>). Anything else in the file is a typo and stops
# the run, with the nearest known name.
_CFG_V2_SHARED = (
    (("blue", "gm"), "mig_blue_gm_host"), (("blue", "gm_user"), "mig_blue_gm_user"),
    (("blue", "gm_password"), "mig_blue_gm_password"), (("blue", "lm_user"), "mig_blue_lm_user"),
    (("blue", "lm_password"), "mig_blue_lm_password"), (("blue", "vc_user"), "mig_blue_vc_user"),
    (("blue", "vc_password"), "mig_blue_vc_password"), (("blue", "edge_password"), "mig_blue_edge_password"),
    (("blue", "edge_root_password"), "mig_blue_edge_root_password"),
    (("green", "gm"), "nsx_gm_host"), (("green", "gm_user"), "nsx_gm_user"), (("green", "gm_password"), "nsx_gm_password"),
    (("green", "lm_user"), "nsx_admin_user"), (("green", "lm_password"), "nsx_admin_password"),
    (("green", "vc_user"), "mig_green_vc_user"), (("green", "vc_password"), "mig_green_vc_password"),
    (("green", "edge_password"), "nsx_edge_password"), (("green", "edge_root_password"), "mig_edge_root_password"),
    (("green", "router_mac"), "mig_router_mac"), (("green", "local_as"), "fed_ns_local_as"),
    (("green", "tier0"), "fed_ns_tier0_name"),
    (("leaves", "user"), "leaf_user"), (("leaves", "password"), "leaf_password"), (("leaves", "vlans"), "mig_leaf_vlans"),
    (("edges", "domain"), "mig_edge_domain"), (("edges", "form_factor"), "mig_bridge_edge_form_factor"),
    (("edges", "deploy_wait"), "mig_edge_deploy_wait"), (("edges", "ssh_user"), "nsx_edge_ssh_user"),
    (("edges", "uplink_profile"), "mig_bridge_uplink_profile"),
    (("moves", "batch"), "mig_move_batch"), (("moves", "wait"), "mig_move_wait"), (("moves", "delete_wait"), "mig_delete_wait"),
)
_CFG_V2_SITE = (
    (("scope",), "mig_scope"), (("skip",), "mig_skip"), (("move_vms",), "mig_move_vms"), (("return_vms",), "mig_return_vms"),
    (("move_batch",), "mig_move_batch"), (("cutover_with_blue_vms",), "mig_cutover_with_blue_vms"),
    (("blue_writes",), "mig_blue_writes"), (("transit_vlans",), "mig_transit_vlans"), (("infra_vlans",), "mig_infra_vlans"),
    (("probes",), "mig_probe_ips"), (("test_segments",), "mig_test_segments"), (("test_subnet",), "mig_test_subnet"),
    (("test_blue_tier1",), "mig_test_blue_tier1"), (("state_file",), "mig_state_file"),
    (("blue", "location"), "mig_blue_site"), (("blue", "lm"), "mig_blue_lm_host"), (("blue", "lm_user"), "mig_blue_lm_user"),
    (("blue", "lm_password"), "mig_blue_lm_password"), (("blue", "vcenter"), "mig_blue_vc"),
    (("blue", "vc_user"), "mig_blue_vc_user"), (("blue", "vc_password"), "mig_blue_vc_password"),
    (("blue", "vcenter_remote"), "mig_blue_vc_remote"), (("blue", "cluster"), "mig_blue_cluster"),
    (("blue", "datastore"), "mig_blue_datastore"),
    (("blue", "bridge", "edges"), "mig_blue_bridge_edges"),
    (("blue", "bridge", "admin_password"), "mig_blue_edge_password"),
    (("blue", "bridge", "root_password"), "mig_blue_edge_root_password"), (("blue", "bridge", "ips"), "mig_blue_bridge_edge_ips"),
    (("blue", "bridge", "vc_password"), "mig_blue_edge_vc_password"),
    (("blue", "bridge", "cluster"), "mig_blue_bridge_edge_cluster"), (("blue", "bridge", "template"), "mig_blue_bridge_edge_template"),
    (("blue", "bridge", "zone"), "mig_blue_bridge_vlan_tz"), (("blue", "bridge", "profile"), "mig_blue_bridge_profile"),
    (("blue", "bridge", "trunk_pg"), "mig_blue_bridge_trunk_pg"),
    (("green", "lm"), "nsx_lm_host"), (("green", "lm_user"), "nsx_admin_user"), (("green", "lm_password"), "nsx_admin_password"),
    (("green", "tier1"), "mig_tier1"), (("green", "local_as"), "fed_ns_local_as"),
    (("green", "vcenter"), "mig_green_vc"), (("green", "vc_user"), "mig_green_vc_user"),
    (("green", "vc_password"), "mig_green_vc_password"),
    (("green", "cluster"), "mig_green_cluster"), (("green", "datastore"), "mig_green_datastore"),
    (("green", "bridge", "edges"), "mig_bridge_edges"),
    (("green", "bridge", "admin_password"), "nsx_edge_password"),
    (("green", "bridge", "root_password"), "mig_edge_root_password"), (("green", "bridge", "ips"), "mig_bridge_edge_ips"),
    (("green", "bridge", "vc_password"), "mig_green_edge_vc_password"),
    (("green", "bridge", "cluster"), "mig_bridge_edge_cluster"), (("green", "bridge", "template"), "mig_bridge_edge_template"),
    (("green", "bridge", "zone"), "mig_bridge_vlan_tz"), (("green", "bridge", "profile"), "mig_bridge_profile"),
    (("green", "bridge", "trunk_pg"), "mig_bridge_trunk_pg"),
    (("leaves", "user"), "leaf_user"), (("leaves", "password"), "leaf_password"),
    (("leaves", "bridge"), "mig_bridge_leaves"), (("leaves", "route"), "mig_route_leaves"), (("leaves", "tep"), "mig_tep_leaves"),
    (("leaves", "ports"), "mig_bridge_ports"),
)
_CFG_V2_SHARED_MAP = dict(_CFG_V2_SHARED)
_CFG_V2_SITE_MAP = dict(_CFG_V2_SITE)
# Sign-ins that belong to one site's systems (its Local Managers, vCenters, bridge edges, leaves): written in
# that site's block, so each one says which site and side it is for. Only the Global Managers' are for all sites.
_CFG_SITE_SIGNINS = ("mig_blue_lm_user", "mig_blue_lm_password", "mig_blue_vc_user", "mig_blue_vc_password",
                     "mig_blue_edge_password", "mig_blue_edge_root_password", "nsx_admin_user", "nsx_admin_password",
                     "mig_green_vc_user", "mig_green_vc_password", "nsx_edge_password", "mig_edge_root_password",
                     "leaf_user", "leaf_password")


def _cfg_v2(raw, path=""):
    """The layout above as the flat keys the tool reads. Every name is checked against it: an unknown
    one stops the run and names the nearest known one. `extra:` holds raw keys, as they are."""
    import difflib
    out, bad = {}, []

    def unknown(where, k, known):
        near = difflib.get_close_matches(str(k), [str(x) for x in known], 1)
        bad.append("%s%s%s" % (where, k, " (did you mean %s?)" % near[0] if near else ""))

    def walk(node, prefix, table, where, put):
        known = sorted({p_[len(prefix)] for p_ in table if p_[:len(prefix)] == prefix and len(p_) > len(prefix)})
        for k, v in (node or {}).items() if isinstance(node, dict) else []:
            p_ = prefix + (str(k),)
            if p_ in table:
                put(table[p_], v)
            elif any(t[:len(p_)] == p_ for t in table):
                if isinstance(v, dict):
                    walk(v, p_, table, where + str(k) + ".", put)
                elif v not in (None, ""):
                    bad.append("%s%s: a block, not a value" % (where, k))
            else:
                unknown(where, k, known)
    for top, val in raw.items():
        if top == "sites":
            continue
        if top == "extra":
            out.update(val or {})
        elif any(t[0] == top for t in _CFG_V2_SHARED_MAP):
            walk({top: val}, (), _CFG_V2_SHARED_MAP, "", lambda k_, v_: out.__setitem__(k_, v_))
        else:
            unknown("", top, ["sites", "extra"] + sorted({t[0] for t in _CFG_V2_SHARED_MAP}))
    sites = [str(x) for x in raw["sites"]]
    for site in sites:
        walk(raw["sites"][site], (), _CFG_V2_SITE_MAP, "sites.%s." % site,
             lambda k_, v_, s_=site: out.__setitem__("%s_%s" % (k_, s_), v_))
    if bad:
        sys.exit("%s: not understood: %s" % (path or "config", "; ".join(bad)))
    for site in sites:                  # the other sites' Blue vCenters, for KB 330523, unless named
        if not out.get("mig_blue_vc_remote_%s" % site):
            other = [out.get("mig_blue_vc_%s" % x) for x in sites if x != site and out.get("mig_blue_vc_%s" % x)]
            if len(other) == 1:
                out["mig_blue_vc_remote_%s" % site] = other[0]
    out["mig_sites"], out["_site_blocks"], out["_v2"] = sites, sites, True
    return out


def _cfg_sites(cfg, path=""):
    """Each site block as <key>_<site> keys. A value set both in a block and as <key>_<site> stops the
    run: one place per value. Without mig_sites, the blocks in order are the sites."""
    if not isinstance(cfg, dict):
        return cfg
    blocks = [k for k, v in cfg.items() if isinstance(v, dict)]
    for site in blocks:
        for k, v in cfg.pop(site).items():
            fk = "%s_%s" % (k, site)
            if fk in cfg and cfg[fk] != v:
                sys.exit("%s: %s is set twice, under %s: and as %s: keep one" % (path or "config", k, site, fk))
            cfg[fk] = v
    if blocks:
        cfg["_site_blocks"] = blocks
        if not cfg.get("mig_sites"):
            cfg["mig_sites"] = blocks
    return cfg


EXAMPLE_CONFIG = """# ---------------------------------------------------------------------------
# fleetparity configuration  (flat YAML; JSON also accepted; PyYAML optional)
# Environment variables override anything here. Anything missing is prompted.
# If you put secrets in this file:  chmod 600 <file>   and never commit it.
# ---------------------------------------------------------------------------
site_name: example

# VCF Operations (run `collect --tag ops` on the primary node; localhost is fine)
ops_host: localhost
ops_user: admin
# ops_password: ""

# SDDC Manager API user (shared SSO domain => usually one password for all)
sddc_user: administrator@vsphere.local
# sddc_password: ""
# Per-instance override, keyed by the --tag you pass on that box:
# sddc_password_<tag>: ""

# Optional layers. Each is prompted for if absent; Enter skips it.
# ops_root_password: ""        # other Operations nodes' logs over SSH
# sddc_ssh_user: vcf
# sddc_ssh_password: ""        # SDDC Manager DB layer over SSH (vcf, then su -)
# sddc_root_password: ""
# esxi_root_password: ""       # esxcli + jumbo-frame mesh; per-domain: esxi_root_password_<domain>
#
# Any of these can be scoped when instances or domains differ. A scoped key
# that is present but blank is prompted for by name when that scope is reached:
#   sddc_password_<instance>:        sddc_ssh_password_<instance>:
#   sddc_root_password_<instance>:   esxi_root_password_<domain>:
#   nsx_admin_password_<fqdn>:
# If a shared credential is rejected somewhere, the tool asks once for that
# scope and continues.
# nsx_admin_user: admin
# nsx_admin_password: ""       # NSX cluster status and version

# Optional: known SDDC Managers, used only for documentation / --plan output
sddc_hosts: []

# Optional: hosts you expect to exist. compare flags any that are never seen.
expected_hosts: []

# Optional: appliances planned but not yet deployed, as fqdn=ip. Each is
# checked for forward and reverse DNS and for nothing already answering on 443.
planned_appliances: []

# Flag credentials whose auto-rotate schedule is due within this many days
rotation_warn_days: 30

# ---- Existing NSX Federation: give the active Global Manager and it is read too
# nsx_gm_host:                # FQDN or VIP of the active Global Manager
# nsx_gm_user: admin
# nsx_gm_password:            # Enter at the prompt = same as the NSX admin password

# ---- NSX Federation readiness (runs when two or more NSX Local Managers are found)
# Blank values become "decide" items in the worksheets rather than errors.
# fed_enabled: true
# fed_gm_node_count: 3
# fed_gm_domain: example.com
# fed_gm_site: <instance name that hosts the active Global Manager>
# fed_gm_netmask: 255.255.255.0
# fed_gm_gateway:
# fed_gm_node1_fqdn:   fed_gm_node1_ip:
# fed_gm_node2_fqdn:   fed_gm_node2_ip:
# fed_gm_node3_fqdn:   fed_gm_node3_ip:
# fed_gm_vip_fqdn:     fed_gm_vip_ip:
# fed_gm_size: Medium
# Standby Global Manager at the second site (strongly recommended):
# fed_gm_standby_site: <instance name>
# fed_gm_standby_netmask:      fed_gm_standby_gateway:
# fed_gm_standby_node1_fqdn:   fed_gm_standby_node1_ip:   (... node2, node3, vip)
# Per instance, keyed by the VCF instance name:
# fed_rtep_vlan_<instance>:   fed_rtep_cidr_<instance>:   fed_rtep_gateway_<instance>:
# fed_rtep_range_<instance>: <first>-<last>      # pool range for the RTEP addresses
# fed_rtep_mtu: 1700                             # what the DCI carries between RTEP subnets; measure before raising
# fed_reference_vm_<instance>: <LM node 1 VM name>   # GM nodes copy its portgroup/datastore/folder (auto-detected if blank)
# fed_gm_ova_path: /path/to/nsx-unified-appliance-9.1.x.ova   # version and role options are verified
# Optional leaf-switch check (read-only `ip -j addr show`): RTEP VLAN present, MTU, address
# leaf_user: cumulus
# leaf_password:
# leaf_hosts_<instance>: [leaf1.example.com, leaf2.example.com]
# fed_edge_clusters_<instance>: []      # blank = every edge cluster

outdir: /tmp/fleetparity
"""


def secret(envname, cfg, keys, prompt):
    v = os.environ.get(envname)
    if v:
        return v
    for k in keys:
        if cfg.get(k):
            return str(cfg[k])
    if DRY:
        return "<dry-run>"
    return getpass.getpass(prompt)


# ---------------------------------------------------------------- scoped credentials
_CRED_CACHE = {}


def env_key(base, scope):
    return "%s_%s" % (base, re.sub(r"[^A-Za-z0-9]", "_", scope).upper())


def scoped_secret(cfg, base_key, scope, default, prompt_label):
    """Credential for one scope (an instance, a domain, an appliance).
    Order: env FLEETPARITY_<BASE>_<SCOPE>  >  config <base>_<scope>  >
    (if the config lists that scoped key, even blank: prompt for it)  >  default."""
    ck = "%s_%s" % (base_key, scope)
    if ck in _CRED_CACHE:
        return _CRED_CACHE[ck]
    v = os.environ.get(env_key("FLEETPARITY_" + base_key.upper(), scope)) or cfg.get(ck)
    if not v and ck in cfg and not DRY:
        v = getpass.getpass("      %s for %s (Enter = use the shared one): " % (prompt_label, scope)) or default
    _CRED_CACHE[ck] = v or default
    return _CRED_CACHE[ck]


def reprompt(scope, prompt_label):
    """Shared credential was rejected for this scope: ask once for that scope."""
    if DRY:
        return ""
    print("      The shared credential was not accepted for %s." % scope)
    try:
        return getpass.getpass("      %s for %s (Enter to skip it): " % (prompt_label, scope))
    except Exception:
        return ""


def is_auth_failure(msg):
    return bool(re.search(r"permission denied|authentication fail|invalid credential|401|403|"
                          r"incorrect password|too many authentication", str(msg), re.I))


# ---------------------------------------------------------------- redaction
def deep_redact(obj):
    if isinstance(obj, dict):
        return {k: ("<redacted len=%d>" % len(str(v)) if SECRET_KEY.search(str(k)) and v
                    else deep_redact(v)) for k, v in obj.items()}
    if isinstance(obj, list):
        return [deep_redact(x) for x in obj]
    return obj


# ---------------------------------------------------------------- HTTP
TRACE = os.environ.get("FLEETPARITY_TRACE") not in (None, "", "0")


def http(url, method="GET", headers=None, body=None, timeout=90, retries=1):
    if DRY:
        PLAN.append("%-4s %s%s" % (method, url, ("  body=%s" % json.dumps(body)) if body else ""))
        return 0, {}
    if TRACE:
        sys.stderr.write("      %s %s ... " % (method, url[:150]))
        sys.stderr.flush()
        _t0 = time.time()
        try:
            st, b = _http(url, method, headers, body, timeout, retries)
            sys.stderr.write("%s  %.1fs\n" % (st, time.time() - _t0))
            sys.stderr.flush()
            return st, b
        except BaseException as e:
            sys.stderr.write("EXC %s  %.1fs\n" % (str(e)[:60], time.time() - _t0))
            sys.stderr.flush()
            raise
    return _http(url, method, headers, body, timeout, retries)


def _http(url, method="GET", headers=None, body=None, timeout=90, retries=1):
    data = None
    hdrs = dict(headers or {})
    if body is not None:
        data = json.dumps(body).encode()
        hdrs.setdefault("Content-Type", "application/json")
    hdrs.setdefault("Accept", "application/json")
    last = (0, {"_error": "no attempt"})
    for attempt in range(retries + 1):
        req = urllib.request.Request(url, data=data, headers=hdrs, method=method)
        try:
            with urllib.request.urlopen(req, context=CTX, timeout=timeout) as r:
                return r.status, _decode(r.read())
        except urllib.error.HTTPError as e:
            return e.code, _decode(e.read())
        except Exception as e:
            last = (0, {"_error": str(e)})
            time.sleep(1.0)
    return last


def _decode(raw):
    text = raw.decode("utf-8", "replace")
    try:
        return json.loads(text)
    except Exception:
        return {"_raw": text[:4000]}


def rows(obj):
    if isinstance(obj, list):
        return obj
    if not isinstance(obj, dict):
        return []
    for k in LIST_KEYS:
        if isinstance(obj.get(k), list):
            return obj[k]
    for v in obj.values():
        if isinstance(v, list) and v and isinstance(v[0], dict):
            return v
    return []


def paged(url, headers, cap_pages=20):
    """Follow suite-api pageInfo pagination. Returns merged list."""
    sep = "&" if "?" in url else "?"
    out, page = [], 0
    while page < cap_pages:
        st, b = http("%s%spage=%d&pageSize=%d&_no_links=true" % (url, sep, page, PAGE),
                     headers=headers)
        if DRY:
            return []
        out.extend(rows(b))
        info = b.get("pageInfo", {}) if isinstance(b, dict) else {}
        total = info.get("totalCount", 0) or 0
        page += 1
        if len(out) >= total or not rows(b):
            break
    return out


def dig(rec, *names):
    if not isinstance(rec, dict):
        return None
    for n in names:
        v = rec.get(n)
        if isinstance(v, str) and v:
            return v
    for v in rec.values():
        if isinstance(v, dict):
            for n in names:
                x = v.get(n)
                if isinstance(x, str) and x:
                    return x
    return None


# ---------------------------------------------------------------- auth
def ops_auth(host, user, pw):
    if DRY:
        PLAN.append("POST https://%s/suite-api/api/auth/token/acquire  (token)" % host)
        return "vRealizeOpsToken <dry-run>"
    st, body = http("https://%s/suite-api/api/auth/token/acquire" % host,
                    method="POST", body={"username": user, "password": pw})
    tok = body.get("token") if isinstance(body, dict) else None
    if not tok:
        log("  ! Operations token HTTP %s: %s" % (st, str(body)[:160]))
        return None
    for scheme in ("vRealizeOpsToken", "OpsToken", "Bearer"):
        st2, _ = http("https://%s/suite-api/api/adapters?_no_links=true" % host,
                      headers={"Authorization": "%s %s" % (scheme, tok)})
        if st2 == 200:
            log("  Operations token OK (scheme %s)" % scheme)
            return "%s %s" % (scheme, tok)
    log("  ! token acquired but no auth scheme accepted on /adapters")
    return None


def sddc_auth(host, user, pw):
    if DRY:
        PLAN.append("POST https://%s/v1/tokens  (token)" % host)
        return "Bearer <dry-run>"
    st, body = http("https://%s/v1/tokens" % host,
                    method="POST", body={"username": user, "password": pw})
    tok = body.get("accessToken") if isinstance(body, dict) else None
    if not tok:
        log("  ! SDDC token HTTP %s: %s" % (st, str(body)[:160]))
        return None
    log("  SDDC Manager token OK")
    return "Bearer " + tok


# ---------------------------------------------------------------- psql
def _first_existing(cands):
    for c in cands:
        if "/" not in c:
            for d in os.environ.get("PATH", "").split(":"):
                if os.path.exists(os.path.join(d, c)):
                    return c
        elif os.path.exists(c):
            return c
    return None


def run_sql(mode, db, sql, port=None):
    """(ok, rows|error). mode: ops | sddc | fleet. Read-only; caller passes SELECTs."""
    if DRY:
        PLAN.append("SQL  [%s:%s] %s" % (mode, db, " ".join(sql.split())[:110]))
        return True, []
    fd, path = tempfile.mkstemp(prefix="fp_", suffix=".sql", dir="/tmp")
    with os.fdopen(fd, "w") as f:
        f.write(sql)
    os.chmod(path, 0o644)
    env = dict(os.environ)
    if os.environ.get("FLEETPARITY_PGPASSWORD"):
        env["PGPASSWORD"] = os.environ["FLEETPARITY_PGPASSWORD"]
    try:
        attempts = []
        if mode == "ops":
            bin_ = _first_existing(OPS_PSQL_CANDIDATES) or "psql"
            base = "%s -d %s -p %s -X -q -w -f %s" % (bin_, db, port or 5433, path)
            attempts.append((["su", "-", "postgres", "-c", base + " --csv"], "csv"))
            attempts.append((["su", "-", "postgres", "-c", base + " -A -F \x1f"], "us"))
            attempts.append(([bin_, "-h", "localhost", "-p", str(port or 5433), "-U", "postgres",
                              "-d", db, "-X", "-q", "-w", "--csv", "-f", path], "csv"))
        elif mode == "fleet":
            base = "psql -d %s -X -q -w -f %s" % (db, path)
            attempts.append((["su", "-", "postgres", "-c", base + " --csv"], "csv"))
            attempts.append((["su", "-", "postgres", "-c", base + " -A -F \x1f"], "us"))
        else:
            bin_ = _first_existing(SDDC_PSQL_CANDIDATES) or "psql"
            common = [bin_, "-h", "localhost", "-U", "postgres", "-d", db, "-X", "-q", "-w", "-f", path]
            attempts.append((common + ["--csv"], "csv"))
            attempts.append((common + ["-A", "-F", "\x1f"], "us"))
        err = ""
        for cmd, fmt in attempts:
            try:
                p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   timeout=180, env=env)
            except Exception as e:
                err = str(e)
                continue
            out = p.stdout.decode("utf-8", "replace")
            err = p.stderr.decode("utf-8", "replace").strip()
            if p.returncode == 0 and out.strip():
                if fmt == "csv":
                    return True, [deep_redact(r) for r in csv.DictReader(io.StringIO(out))]
                lines = out.splitlines()
                hdr = lines[0].split("\x1f")
                recs = [dict(zip(hdr, ln.split("\x1f"))) for ln in lines[1:]
                        if ln and not ln.startswith("(")]
                return True, [deep_redact(r) for r in recs]
            if p.returncode == 0 and not out.strip():
                return True, []
        return False, err or "psql failed"
    finally:
        try:
            os.unlink(path)
        except Exception:
            pass


def list_tables(mode, db, pat, port=None):
    ok, res = run_sql(mode, db, "SELECT table_name FROM information_schema.tables "
                                "WHERE table_schema='public' ORDER BY 1;", port)
    if not ok:
        return False, res
    return True, [r["table_name"] for r in res if pat.search(r.get("table_name", ""))]


def dump_tables(mode, db, tables, out, prefix, port=None):
    summary = {}
    for t in tables:
        ok, res = run_sql(mode, db, 'SELECT * FROM "%s" LIMIT %d;' % (t, ROW_CAP), port)
        if ok:
            write_json(out, "%s_%s" % (prefix, t), {"table": t, "row_cap": ROW_CAP, "rows": res})
            summary[t] = len(res)
        else:
            summary[t] = "ERR: %s" % str(res)[:120]
    return summary


# ---------------------------------------------------------------- bundle io
def write_json(outdir, name, obj):
    if DRY:
        return None
    p = os.path.join(outdir, SAFE.sub("_", name) + ".json")
    with open(p, "w") as f:
        json.dump(deep_redact(obj), f, indent=2, sort_keys=True, default=str)
    return p


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def finalize_bundle(outdir, meta, tar=True):
    if DRY:
        return outdir
    manifest = {"tool": TOOL, "version": __version__, "created": now(), "meta": meta, "files": {}}
    for fn in sorted(os.listdir(outdir)):
        fp = os.path.join(outdir, fn)
        if fn != "manifest.json" and os.path.isfile(fp):
            manifest["files"][fn] = sha256(fp)
    write_json(outdir, "manifest", manifest)
    if not tar:
        return outdir
    tgz = outdir.rstrip("/") + ".tgz"
    with tarfile.open(tgz, "w:gz") as t:
        t.add(outdir, arcname=os.path.basename(outdir.rstrip("/")))
    return tgz


# ---------------------------------------------------------------- role detect
def detect_role():
    if os.path.isdir("/opt/vmware/vcf/operationsmanager") or os.path.isdir("/var/log/vmware/vcf"):
        return "sddc"
    if os.path.isdir(OPS_LOGDIR) or os.path.isdir("/usr/lib/vmware-vcops"):
        return "ops"
    if os.path.isdir("/opt/vmware/vlcm"):
        return "fleet"
    return "remote"


# ---------------------------------------------------------------- ops: logs
def _open_log(path):
    return gzip.open(path, "rt", errors="replace") if path.endswith(".gz") \
        else open(path, "r", errors="replace")


def analyse_bridge_logs(out, max_files=60):
    files = sorted(glob.glob(os.path.join(OPS_LOGDIR, "vcops-bridge*")))
    if not files:
        return {}
    if DRY:
        PLAN.append("LOG  read %d file(s) matching %s/vcops-bridge*" % (len(files), OPS_LOGDIR))
        return {}
    files = files[:max_files]
    kv = collections.defaultdict(lambda: {"count": 0, "first": None, "last": None})
    by_uuid = collections.defaultdict(set)
    cancel = collections.Counter()
    adapterinfo = collections.Counter()
    stale = collections.Counter()
    vims = collections.Counter()
    for p in files:
        try:
            with _open_log(p) as fh:
                for line in fh:
                    for m in RX_KV.finditer(line):
                        k = (m.group("type"), m.group("fqdn"), m.group("user"), m.group("uuid"))
                        e = int(m.group("epoch"))
                        d = kv[k]
                        d["count"] += 1
                        d["first"] = e if d["first"] is None else min(d["first"], e)
                        d["last"] = e if d["last"] is None else max(d["last"], e)
                        by_uuid[m.group("uuid")].add(m.group("fqdn"))
                    if RX_CANCEL.search(line):
                        cancel[os.path.basename(p)] += 1
                    for m in RX_ADAPTERINFO.finditer(line):
                        adapterinfo[m.group(1) + " " + m.group(2)] += 1
                    for m in RX_STALE.finditer(line):
                        stale[m.group(1)] += 1
                    for m in RX_VIM.finditer(line):
                        vims[m.group(1)] += 1
        except Exception as e:
            log("  ! %s: %s" % (os.path.basename(p), e))
    keys = [{"type": t, "fqdn": f, "user": u, "uuid": uu, "count": v["count"],
             "first_epoch": v["first"], "last_epoch": v["last"],
             "first": datetime.datetime.fromtimestamp(v["first"] / 1000, datetime.timezone.utc).isoformat(),
             "last": datetime.datetime.fromtimestamp(v["last"] / 1000, datetime.timezone.utc).isoformat()}
            for (t, f, u, uu), v in sorted(kv.items())]
    res = {"files_scanned": [os.path.basename(f) for f in files],
           "kv_keys": keys,
           "uuid_scopes": {u: sorted(s) for u, s in by_uuid.items()},
           "primary_cancel_counts": dict(cancel),
           "primary_cancel_total": sum(cancel.values()),
           "adapterinfo_failures": dict(adapterinfo),
           "stale_cycle_vim_instances": dict(stale),
           "vim_instance_counts": dict(vims),
           "scanned_at_epoch_ms": int(time.time() * 1000),
           "node": os.uname()[1]}
    if out is not None:
        write_json(out, "opslog_bridge_analysis", res)
    if out is not None:
        log("  bridge logs: %d files, %d distinct keys, %d primary-cancel lines"
            % (len(files), len(keys), res["primary_cancel_total"]))
    return res


def scan_ops_logs(out, max_lines=400):
    """ERROR/WARN lines in the other Operations logs that mention fleet, lcm, locker,
    password, certificate, token or auth failures. Capped; file counts kept in full."""
    files = [f for f in sorted(glob.glob(os.path.join(OPS_LOGDIR, "*.log")))
             if "vcops-bridge" not in os.path.basename(f)]
    if DRY:
        PLAN.append("LOG  scan %d non-bridge *.log files in %s for fleet/lcm/password/cert errors"
                    % (len(files), OPS_LOGDIR))
        return
    per_file, sample = collections.Counter(), []
    for p in files:
        try:
            with _open_log(p) as fh:
                for line in fh:
                    if RX_OPSERR.search(line):
                        per_file[os.path.basename(p)] += 1
                        if len(sample) < max_lines:
                            sample.append("%s: %s" % (os.path.basename(p), line.strip()[:300]))
        except Exception:
            continue
    write_json(out, "opslog_error_scan", {"per_file": dict(per_file), "sample": sample})
    log("  other logs: %d matching lines across %d files" % (sum(per_file.values()), len(per_file)))


def local_clock():
    info = {"python_utc": now(), "epoch_ms": int(time.time() * 1000)}
    for name, cmd in (("date_u", ["date", "-u"]), ("timedatectl", ["timedatectl"]),
                      ("chronyc", ["chronyc", "tracking"])):
        try:
            p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
            info[name] = p.stdout.decode("utf-8", "replace").strip()[:800]
        except Exception as e:
            info[name] = "n/a (%s)" % e.__class__.__name__
    return info


# ---------------------------------------------------------------- remote execution
def _kill_group(proc):
    try:
        os.killpg(os.getpgid(proc.pid), 15)
        try:
            proc.wait(timeout=3)
        except Exception:
            os.killpg(os.getpgid(proc.pid), 9)
    except Exception:
        try:
            proc.kill()
        except Exception:
            pass


def ssh_exec(host, user, password, remote_cmd, stdin_data=None, timeout=60, tty=False):
    """Run a command over SSH. Key-based first; then password via SSH_ASKPASS
    (stdlib + stock OpenSSH, no sshpass needed). Never prompts on the terminal.
    tty=True forces a remote pty (needed when the remote command is `su -`)."""
    common = ["-o", "StrictHostKeyChecking=accept-new", "-o", "ConnectTimeout=8",
              "-o", "LogLevel=ERROR", "-o", "NumberOfPasswordPrompts=1"]
    if tty:
        common = ["-tt"] + common
    common += ["%s@%s" % (user, host)]
    if remote_cmd:
        common += [remote_cmd]
    attempts = [(["ssh", "-o", "BatchMode=yes"] + common, dict(os.environ))]
    ap = None
    if password:
        fd, ap = tempfile.mkstemp(prefix="fp_ap_", suffix=".sh", dir="/tmp")
        with os.fdopen(fd, "w") as f:
            f.write('#!/bin/sh\nprintf "%s" "$FP_SSHPW"\n')
        os.chmod(ap, 0o700)
        env = dict(os.environ, SSH_ASKPASS=ap, SSH_ASKPASS_REQUIRE="force", DISPLAY=":0",
                   FP_SSHPW=password)
        cmd = ["ssh", "-o", "PubkeyAuthentication=no"] + common
        attempts.append((cmd, env))
    last = "ssh failed"
    try:
        for cmd, env in attempts:
            # start_new_session detaches ssh from our terminal (so it cannot prompt there)
            # AND gives it its own process group, so a timeout or Ctrl-C kills ssh too.
            try:
                proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, env=env, start_new_session=True)
            except Exception as e:
                last = str(e)
                continue
            try:
                out, err = proc.communicate(input=(stdin_data.encode() if stdin_data else None), timeout=timeout)
            except subprocess.TimeoutExpired:
                _kill_group(proc)
                last = "timed out after %ds" % timeout
                continue
            except KeyboardInterrupt:
                _kill_group(proc)
                raise
            if proc.returncode == 0:
                return True, out.decode("utf-8", "replace")
            last = err.decode("utf-8", "replace").strip()[:300] or "exit %d" % proc.returncode
        return False, last
    finally:
        if ap:
            try:
                os.unlink(ap)
            except Exception:
                pass


def remote_bridge_analysis(host, user, password, out, tag):
    """Run this same file's bridge analyser on another Operations node and keep its JSON."""
    if DRY:
        PLAN.append("SSH  %s@%s  python3 - _bridge_json  (this script over stdin)" % (user, host))
        return
    with open(os.path.abspath(sys.argv[0])) as fh:
        me = fh.read()
    ok, o = ssh_exec(host, user, password, "python3 - _bridge_json", stdin_data=me, timeout=90)
    if ok:
        try:
            write_json(out, "opslog_bridge_analysis_%s" % SAFE.sub("_", tag), json.loads(o))
            log("  %s: bridge analysis collected" % host)
            return
        except Exception as e:
            o = "bad json: %s" % e
    write_json(out, "opslog_bridge_analysis_%s" % SAFE.sub("_", tag), {"_error": o})
    log("  %s: not collected (%s)" % (host, o[:80]))


# ---------------------------------------------------------------- best-practice checks
BP = []          # {"area","check","result","detail"}  result: PASS | WARN | FAIL | SKIP | INFO


def bp(area, check, result, detail=""):
    BP.append({"area": area, "check": check, "result": result, "detail": str(detail)[:400]})


def days_until(value):
    """Days from now to an ISO-ish date string or epoch (s/ms). None if unparseable."""
    if value in (None, "", 0):
        return None
    try:
        if isinstance(value, (int, float)) or (isinstance(value, str) and value.isdigit()):
            v = float(value)
            if v > 1e12:
                v /= 1000.0
            when = datetime.datetime.fromtimestamp(v, datetime.timezone.utc).replace(tzinfo=None)
        else:
            txt = str(value).strip().replace("Z", "")
            for fmt in ("%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S",
                        "%Y-%m-%d", "%b %d %H:%M:%S %Y GMT", "%b %d %H:%M:%S %Y"):
                try:
                    when = datetime.datetime.strptime(txt[:26] if "." in txt else txt, fmt)
                    break
                except ValueError:
                    continue
            else:
                return None
        return (when - datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None)).days
    except Exception:
        return None


def tls_info(host, port=443):
    """Certificate facts as presented on the wire, via the system openssl."""
    if DRY:
        PLAN.append("TLS  openssl s_client %s:%d (subject/issuer/dates/SAN)" % (host, port))
        return {}
    cmd = ("echo | openssl s_client -connect %s:%d -servername %s 2>/dev/null | "
           "openssl x509 -noout -subject -issuer -dates -fingerprint -sha256 -ext subjectAltName 2>/dev/null"
           % (host, port, host))
    try:
        p = subprocess.run(["sh", "-c", cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        txt = p.stdout.decode("utf-8", "replace")
    except Exception as e:
        return {"_error": str(e)}
    if "notAfter" not in txt:
        cmd2 = ("echo | openssl s_client -connect %s:%d -servername %s 2>/dev/null | "
                "openssl x509 -noout -subject -issuer -dates -text 2>/dev/null" % (host, port, host))
        try:
            p = subprocess.run(["sh", "-c", cmd2], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
            txt = p.stdout.decode("utf-8", "replace")
        except Exception as e:
            return {"_error": str(e)}
    if "notAfter" not in txt:
        return {"_error": "no certificate presented"}
    info = {}
    for key in ("subject", "issuer", "notBefore", "notAfter"):
        m = re.search(r"^%s\s*=\s*(.*)$" % key, txt, re.M)
        if m:
            info[key] = m.group(1).strip()
    m = re.search(r"Fingerprint=([0-9A-Fa-f:]+)", txt, re.I)
    if m:
        info["sha256_fingerprint"] = m.group(1).upper()
    info["san"] = sorted(set(x.strip() for x in re.findall(r"DNS:([^,\s]+)", txt)))
    info["san_ip"] = sorted(set(x.strip() for x in re.findall(r"IP Address:([^,\s]+)", txt)))
    info["days_left"] = days_until(info.get("notAfter"))
    return info


def tls_sweep(out, targets):
    res = {}
    for i, h in enumerate(sorted(set(targets)), 1):
        res[h] = tls_info(h)
        if not DRY and (i % 10 == 0 or i == len(targets)):
            log("  %d/%d" % (i, len(targets)))
    write_json(out, "tls_sweep", res)
    for h, v in sorted(res.items()):
        if v.get("_error"):
            bp("tls", "%s presents a certificate" % h, "SKIP", v["_error"])
            continue
        d = v.get("days_left")
        if d is None:
            bp("tls", "%s certificate expiry" % h, "SKIP", v.get("notAfter"))
        elif d < 14:
            bp("tls", "%s certificate expiry" % h, "FAIL", "%d days (%s)" % (d, v.get("notAfter")))
        elif d < 60:
            bp("tls", "%s certificate expiry" % h, "WARN", "%d days (%s)" % (d, v.get("notAfter")))
        else:
            bp("tls", "%s certificate expiry" % h, "PASS", "%d days" % d)
        if v.get("san") and h.lower() not in [x.lower() for x in v["san"]]:
            bp("tls", "%s SAN includes its FQDN" % h, "WARN", "SAN=%s" % v["san"][:4])
        elif v.get("san"):
            bp("tls", "%s SAN includes its FQDN" % h, "PASS")
    return res


# ---------------------------------------------------------------- vCenter (SSO credentials)
def collect_vcenter(out, fqdn, user, pw):
    basic = base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()
    st, tok = http("https://%s/api/session" % fqdn, method="POST",
                   headers={"Authorization": "Basic " + basic}, timeout=30)
    if DRY:
        for path in ("/api/appliance/system/version", "/api/appliance/health/system",
                     "/api/appliance/ntp", "/api/appliance/timesync",
                     "/api/appliance/local-accounts/root", "/api/vcenter/certificate-management/vcenter/tls",
                     "/api/appliance/services"):
            PLAN.append("GET  https://%s%s" % (fqdn, path))
        return
    if (st != 201 and st != 200 or not isinstance(tok, str)) and st in (401, 403) and not DRY:
        pw2 = reprompt(fqdn, "'%s' password" % user)
        if pw2:
            return collect_vcenter(out, fqdn, user, pw2)
    if st != 201 and st != 200 or not isinstance(tok, str):
        write_json(out, "vcenter_%s" % fqdn, {"_error": "session HTTP %s" % st})
        bp("vcenter", "%s API login with SSO credentials" % fqdn, "FAIL", "HTTP %s" % st)
        return
    H = {"vmware-api-session-id": tok}
    data = {}
    for nm, path in (("version", "/api/appliance/system/version"),
                     ("health_system", "/api/appliance/health/system"),
                     ("health_db", "/api/appliance/health/database-storage"),
                     ("health_storage", "/api/appliance/health/storage"),
                     ("health_mem", "/api/appliance/health/mem"),
                     ("health_swap", "/api/appliance/health/swap"),
                     ("health_applmgmt", "/api/appliance/health/applmgmt"),
                     ("ntp", "/api/appliance/ntp"), ("timesync", "/api/appliance/timesync"),
                     ("root_account", "/api/appliance/local-accounts/root"),
                     ("tls", "/api/vcenter/certificate-management/vcenter/tls"),
                     ("services", "/api/appliance/services")):
        st2, b = http("https://%s%s" % (fqdn, path), headers=H, timeout=40)
        data[nm] = {"status": st2, "body": b}
    # placement inventory: networks, datastores, clusters, folders (for GM/VDI planning)
    pl = {}
    for nm, path in (("networks", "/api/vcenter/network"), ("datastores", "/api/vcenter/datastore"),
                     ("clusters", "/api/vcenter/cluster"), ("folders", "/api/vcenter/folder?type=VIRTUAL_MACHINE")):
        st2, b = http("https://%s%s" % (fqdn, path), headers=H, timeout=40)
        pl[nm] = b if isinstance(b, list) else []
    data["placement"] = pl
    write_json(out, "vcenter_%s" % fqdn, data)
    bp("vcenter", "%s API login with SSO credentials" % fqdn, "PASS")
    v = data["version"]["body"] if isinstance(data["version"]["body"], dict) else {}
    bp("vcenter", "%s version" % fqdn, "INFO", "%s build %s" % (v.get("version"), v.get("build")))
    for nm in ("health_system", "health_db", "health_storage", "health_mem", "health_swap", "health_applmgmt"):
        val = data[nm]["body"]
        val = val if isinstance(val, str) else (val.get("_raw") if isinstance(val, dict) else str(val))
        val = str(val).strip('"').lower()
        bp("vcenter", "%s %s" % (fqdn, nm.replace("health_", "health: ")),
           "PASS" if val == "green" else ("WARN" if val in ("yellow", "orange", "gray") else
                                          ("FAIL" if val == "red" else "SKIP")), val)
    ntp = data["ntp"]["body"]
    bp("vcenter", "%s NTP servers configured" % fqdn, "PASS" if isinstance(ntp, list) and ntp else "WARN", ntp)
    ts = data["timesync"]["body"]
    bp("vcenter", "%s time sync mode" % fqdn, "PASS" if str(ts).strip('"').upper() == "NTP" else "WARN", ts)
    ra = data["root_account"]["body"] if isinstance(data["root_account"]["body"], dict) else {}
    exp = ra.get("password_expires_at")
    d = days_until(exp) if exp else None
    if exp is None:
        bp("vcenter", "%s root password expiry" % fqdn, "INFO", "no expiry set")
    elif d is not None and d < 14:
        bp("vcenter", "%s root password expiry" % fqdn, "FAIL", "%d days (%s)" % (d, exp))
    elif d is not None and d < 45:
        bp("vcenter", "%s root password expiry" % fqdn, "WARN", "%d days (%s)" % (d, exp))
    else:
        bp("vcenter", "%s root password expiry" % fqdn, "PASS", "%s days" % d)
    tls = data["tls"]["body"] if isinstance(data["tls"]["body"], dict) else {}
    d = days_until(tls.get("valid_to"))
    if d is not None:
        bp("vcenter", "%s machine certificate expiry" % fqdn, "FAIL" if d < 14 else ("WARN" if d < 60 else "PASS"),
           "%d days" % d)
    svcs = data["services"]["body"]
    if isinstance(svcs, dict):
        stopped = [k for k, v_ in svcs.items() if isinstance(v_, dict) and v_.get("state") == "STOPPED"
                   and v_.get("startup_type") == "AUTOMATIC"]
        bp("vcenter", "%s automatic services running" % fqdn, "PASS" if not stopped else "WARN", stopped[:10])


def vcenter_session(fqdn, user, pw):
    basic = base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()
    st, tok = http("https://%s/api/session" % fqdn, method="POST", headers={"Authorization": "Basic " + basic}, timeout=30)
    return {"vmware-api-session-id": tok} if st in (200, 201) and isinstance(tok, str) else None


def vcenter_vm_placement(fqdn, H, vm_name, placement):
    """Where an existing VM lives: network name(s), datastore name, folder, cluster. Or None."""
    st, vms = http("https://%s/api/vcenter/vm?names=%s" % (fqdn, vm_name), headers=H, timeout=30)
    vms = vms if isinstance(vms, list) else []
    if not vms:
        return None
    vmid = vms[0].get("vm")
    st, info = http("https://%s/api/vcenter/vm/%s" % (fqdn, vmid), headers=H, timeout=40)
    info = info if isinstance(info, dict) else {}
    net_by_id = {n.get("network"): n.get("name") for n in placement.get("networks") or []}
    nets = []
    for k, nic in (info.get("nics") or {}).items():
        b = (nic or {}).get("backing") or {}
        nets.append(net_by_id.get(b.get("network"), b.get("network")))
    ds = None
    for k, disk in (info.get("disks") or {}).items():
        f = ((disk or {}).get("backing") or {}).get("vmdk_file") or ""
        m = re.match(r"\[([^\]]+)\]", f)
        if m:
            ds = m.group(1)
            break
    folder = None
    for fo in placement.get("folders") or []:
        st, hit = http("https://%s/api/vcenter/vm?folders=%s&names=%s" % (fqdn, fo.get("folder"), vm_name), headers=H, timeout=30)
        if isinstance(hit, list) and hit:
            folder = fo.get("name")
            break
    cluster = None
    for cl in placement.get("clusters") or []:
        st, hit = http("https://%s/api/vcenter/vm?clusters=%s&names=%s" % (fqdn, cl.get("cluster"), vm_name), headers=H, timeout=30)
        if isinstance(hit, list) and hit:
            cluster = cl.get("name")
            break
    return {"vm": vm_name, "networks": [n for n in nets if n], "datastore": ds, "folder": folder, "cluster": cluster,
            "cpu": info.get("cpu", {}).get("count") if isinstance(info.get("cpu"), dict) else None,
            "memory_mib": info.get("memory", {}).get("size_MiB") if isinstance(info.get("memory"), dict) else None}


def vcenter_vm_exists(fqdn, H, vm_name):
    st, vms = http("https://%s/api/vcenter/vm?names=%s" % (fqdn, vm_name), headers=H, timeout=30)
    return bool(isinstance(vms, list) and vms)


# ---------------------------------------------------------------- leaf switches (optional, read-only)
def collect_leaves(out, hosts, user, pw, vlan, cidr, mtu_min, site):
    """`ip -j addr show` on each leaf: is the RTEP VLAN SVI present, what MTU, what address."""
    res = {}
    for h in hosts:
        if DRY:
            PLAN.append("SSH  %s@%s  ip -j addr show  (RTEP VLAN %s present, MTU, address)" % (user, h, vlan))
            continue
        ok, o = ssh_exec(h, user, pw, "ip -j addr show", timeout=20)
        if not ok:
            res[h] = {"_error": o}
            bp("leaf:%s" % site, "%s reachable over SSH" % h, "FAIL" if is_auth_failure(o) else "SKIP", o[:100])
            continue
        try:
            ifs = json.loads(o)
        except Exception as e:
            res[h] = {"_error": "bad json: %s" % e}
            bp("leaf:%s" % site, "%s interface list parses" % h, "SKIP", str(e)[:80])
            continue
        want = [i for i in ifs if re.fullmatch(r"vlan%s(-v0)?" % vlan, str(i.get("ifname")))]
        res[h] = [{"ifname": i.get("ifname"), "mtu": i.get("mtu"), "state": i.get("operstate"),
                   "addrs": [a.get("local") for a in i.get("addr_info") or [] if a.get("family") == "inet"]} for i in want]
        if not want:
            bp("leaf:%s" % site, "%s has VLAN %s SVI" % (h, vlan), "FAIL", "no vlan%s interface" % vlan)
            continue
        for i in res[h]:
            bp("leaf:%s" % site, "%s %s up" % (h, i["ifname"]), "PASS" if str(i["state"]).upper() == "UP" else "WARN", i["state"])
            bp("leaf:%s" % site, "%s %s MTU >= %s" % (h, i["ifname"], mtu_min),
               "PASS" if (i["mtu"] or 0) >= int(mtu_min) else "FAIL", "mtu %s" % i["mtu"])
            try:
                net = ipaddress.ip_network(cidr, strict=False)
                inside = [a for a in i["addrs"] if ipaddress.ip_address(a) in net]
                bp("leaf:%s" % site, "%s %s addressed in %s" % (h, i["ifname"], cidr), "PASS" if inside else "WARN",
                   i["addrs"] or "no IPv4 address")
            except Exception:
                pass
    write_json(out, "leaves_%s" % SAFE.sub("_", site), res)
    return res


# ---------------------------------------------------------------- OVA descriptor (optional, local file)
def check_ova(path, lm_version):
    """Read the .ovf inside the OVA: product, version, and the role options offered."""
    if DRY:
        PLAN.append("FILE read OVF descriptor from %s" % path)
        return {}
    info = {"path": path}
    try:
        with tarfile.open(path) as t:
            ovf = next((m for m in t.getmembers() if m.name.lower().endswith(".ovf")), None)
            if not ovf:
                info["_error"] = "no .ovf inside"
                return info
            x = t.extractfile(ovf).read().decode("utf-8", "replace")
    except Exception as e:
        info["_error"] = str(e)
        return info
    m = re.search(r"<Version>([^<]+)</Version>", x)
    info["version"] = m.group(1).strip() if m else None
    m = re.search(r"<Product>([^<]+)</Product>", x)
    info["product"] = m.group(1).strip() if m else None
    info["roles"] = sorted(set(re.findall(r'ovf:key="nsx_role"[^>]*>|<Value ovf:value="([^"]+)"', x)))
    info["roles"] = [r for r in re.findall(r'ovf:value="(NSX [A-Za-z ]+Manager[^"]*)"', x)] or info["roles"]
    info["sizes"] = sorted(set(re.findall(r'ovf:id="([A-Za-z]+)"[^>]*>\s*<Label', x)))
    def key(v):
        return [int(p) for p in re.findall(r"\d+", v or "")]
    if info.get("version") and lm_version:
        info["newer_or_equal_to_lm"] = key(info["version"]) >= key(lm_version)
    return info


# ---------------------------------------------------------------- ESXi (root over SSH)
ESX_SCRIPT = r"""
echo '@@VER'; esxcli --formatter=keyvalue system version get
echo '@@NTP'; esxcli --formatter=keyvalue system ntp get
echo '@@TIME'; esxcli system time get
echo '@@IF'; esxcli --formatter=keyvalue network ip interface list
echo '@@IP4'; esxcli --formatter=keyvalue network ip interface ipv4 get
echo '@@PING'
"""


def _kv(block):
    """Parse esxcli keyvalue output into a list of dicts (one per record)."""
    recs, cur = [], {}
    for ln in block.splitlines():
        m = re.match(r"^[A-Za-z0-9_]+\.([A-Za-z0-9_]+)\.[\w\[\]]+\s*=\s*(.*)$", ln.strip())
        if not m:
            continue
        key, val = m.group(1), m.group(2).strip()
        if key in cur and cur:
            recs.append(cur)
            cur = {}
        cur[key] = val
    if cur:
        recs.append(cur)
    return recs


def collect_esxi(out, domains, host_ips, pw_for_domain, pool_mtu, ops_epoch):
    """domains: {domain: [fqdn]}, host_ips: {fqdn: {"VMOTION": ip, "VSAN": ip}},
    pw_for_domain(domain) -> password or None, pool_mtu: {(domain, 'VMOTION'|'VSAN'): mtu}."""
    results = {}
    for dom, hosts in sorted(domains.items()):
        pw = pw_for_domain(dom)
        if not pw:
            for h in hosts:
                bp("esxi", "%s host checks" % h, "SKIP", "no ESXi root password for %s" % dom)
            continue
        retried = False
        for h in hosts:
            if DRY:
                PLAN.append("SSH  root@%s  esxcli version/ntp/time/interfaces + vmkping jumbo mesh" % h)
                continue
            mine = host_ips.get(h, {})
            pings = []
            for peer in hosts:
                if peer == h:
                    continue
                pi = host_ips.get(peer, {})
                for net, stack in (("VMOTION", "vmotion"), ("VSAN", "")):
                    if pi.get(net) and mine.get(net):
                        pings.append((net, stack, pi[net]))
            script = ESX_SCRIPT
            for net, stack, ip in pings:
                sflag = ("-S " + stack) if stack else ""
                script += ("VMK=$(esxcli --formatter=keyvalue network ip interface ipv4 get | "
                           "awk -F' = ' '/\\.Name\\./{n=$2} /\\.IPv4Address\\./ && $2==\"%s\"{print n; exit}')\n"
                           % mine[net])
                script += ("[ -n \"$VMK\" ] && echo \"PING %s %s $VMK $(vmkping -I $VMK %s -d -s 8972 -c 2 -W 2 %s 2>&1 "
                           "| grep -o '[0-9]*%% packet loss' | head -1)\"\n" % (net, ip, sflag, ip))
            ok, o = ssh_exec(h, "root", pw, "sh -s", stdin_data=script, timeout=120)
            if not ok and is_auth_failure(o) and not retried:
                retried = True
                pw2 = reprompt("hosts in %s" % dom, "ESXi root password")
                if pw2:
                    pw = pw2
                    _CRED_CACHE["esxi_root_password_%s" % dom] = pw2
                    ok, o = ssh_exec(h, "root", pw, "sh -s", stdin_data=script, timeout=120)
            if not ok:
                results[h] = {"_error": o}
                bp("esxi", "%s SSH as root" % h, "FAIL" if is_auth_failure(o) else "SKIP", o[:120])
                if is_auth_failure(o):
                    for rest in hosts[hosts.index(h) + 1:]:
                        results[rest] = {"_error": "skipped after auth failure on %s" % h}
                        bp("esxi", "%s SSH as root" % rest, "SKIP", "skipped after auth failure in %s" % dom)
                    break
                continue
            secs = {}
            cur = None
            for ln in o.splitlines():
                if ln.startswith("@@"):
                    cur = ln[2:].strip()
                    secs[cur] = []
                elif cur:
                    secs[cur].append(ln)
            ver = _kv("\n".join(secs.get("VER", [])))
            ntp = _kv("\n".join(secs.get("NTP", [])))
            ifs = _kv("\n".join(secs.get("IF", [])))
            ip4 = _kv("\n".join(secs.get("IP4", [])))
            tline = " ".join(secs.get("TIME", [])).strip()
            pingres = [ln for ln in secs.get("PING", []) if ln.startswith("PING ")]
            r = {"version": ver[0] if ver else {}, "ntp": ntp[0] if ntp else {}, "time": tline,
                 "interfaces": ifs, "ipv4": ip4, "pings": pingres}
            results[h] = r
            bp("esxi", "%s SSH as root" % h, "PASS")
            b_ = (ver[0].get("Build") if ver else None)
            bp("esxi", "%s build" % h, "INFO", "%s %s" % (ver[0].get("Version") if ver else "?", b_))
            en = (ntp[0].get("Enabled") if ntp else "").lower()
            srv = (ntp[0].get("NTPServers") if ntp else "")
            bp("esxi", "%s NTP enabled with servers" % h, "PASS" if en == "true" and srv else "WARN",
               "enabled=%s servers=%s" % (en, srv))
            d = days_until(tline.replace("Z", "")) if tline else None
            if tline:
                try:
                    hw = datetime.datetime.strptime(tline.strip()[:19], "%Y-%m-%dT%H:%M:%S")
                    skew = abs((hw - datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None)).total_seconds())
                    bp("esxi", "%s clock skew vs Operations node" % h, "PASS" if skew < 30 else "WARN", "%.0fs" % skew)
                except Exception:
                    pass
            for net in ("VMOTION", "VSAN"):
                ip = mine.get(net)
                if not ip:
                    continue
                vmk = next((x.get("Name") for x in ip4 if x.get("IPv4Address") == ip), None)
                mtu = next((x.get("MTU") for x in ifs if x.get("Name") == vmk), None)
                want = pool_mtu.get((dom, net))
                if vmk is None:
                    bp("esxi", "%s %s vmk present" % (h, net), "FAIL", "no vmk with %s" % ip)
                elif want and str(mtu) != str(want):
                    bp("esxi", "%s %s MTU matches network pool" % (h, net), "WARN", "vmk %s MTU %s, pool %s" % (vmk, mtu, want))
                else:
                    bp("esxi", "%s %s vmk %s MTU %s" % (h, net, vmk, mtu), "PASS")
            for ln in pingres:
                parts = ln.split()
                net, ip, vmk = parts[1], parts[2], parts[3]
                loss = re.search(r"(\d+)% packet loss", ln)
                if not loss:
                    bp("esxi", "%s jumbo %s -> %s" % (h, net, ip), "FAIL", ln[-80:])
                elif loss.group(1) != "0":
                    bp("esxi", "%s jumbo %s -> %s" % (h, net, ip), "FAIL", "%s%% loss at 8972 bytes" % loss.group(1))
                else:
                    bp("esxi", "%s jumbo %s -> %s" % (h, net, ip), "PASS", "0% loss at 8972 bytes")
    write_json(out, "esxi_checks", results)
    return results


# ---------------------------------------------------------------- NSX (optional admin)
def collect_nsx(out, fqdn, user, pw):
    basic = base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()
    H = {"Authorization": "Basic " + basic}
    data = {}
    for nm, path in (("cluster_status", "/api/v1/cluster/status"),
                     ("version", "/api/v1/node/version"),
                     ("nodes", "/api/v1/cluster/nodes"),
                     ("certs", "/api/v1/trust-management/certificates"),
                     ("alarms", "/api/v1/alarms?page_size=200&status=OPEN"),
                     ("alarms_recent", "/api/v1/alarms?page_size=200&status=RESOLVED"),
                     ("licenses", "/api/v1/licenses"),
                     ("edge_clusters", "/api/v1/edge-clusters?page_size=1000"),
                     ("transport_nodes", "/api/v1/transport-nodes?page_size=1000"),
                     ("transport_zones", "/api/v1/transport-zones"),
                     ("uplink_profiles", "/api/v1/host-switch-profiles?include_system_owned=true"),
                     ("ip_pools", "/policy/api/v1/infra/ip-pools"),
                     ("tier0s", "/policy/api/v1/infra/tier-0s"),
                     ("segments", "/policy/api/v1/infra/segments"),
                     ("sites", "/policy/api/v1/infra/sites"),
                     ("projects", "/policy/api/v1/orgs/default/projects")):
        st, b = http("https://%s%s" % (fqdn, path), headers=H, timeout=60)
        data[nm] = {"status": st, "body": b}
    # IP pools come back without their ranges. Follow each one to /ip-subnets so RTEP
    # and TEP allocations can be verified from the archive instead of the UI.
    if not DRY:
        for p_ in _res(data.get("ip_pools", {}).get("body")):
            pid = p_.get("id")
            if not pid:
                continue
            st, sn = http("https://%s/policy/api/v1/infra/ip-pools/%s/ip-subnets" % (fqdn, pid),
                          headers=H, timeout=40)
            p_["subnets"] = [{"cidr": s_.get("cidr"), "gateway_ip": s_.get("gateway_ip"),
                              "allocation_ranges": s_.get("allocation_ranges")}
                             for s_ in _res(sn)]
    else:
        PLAN.append("GET  https://%s/policy/api/v1/infra/ip-pools/<id>/ip-subnets  (pool ranges)" % fqdn)
    # BGP neighbour state for every Tier-0 on this Local Manager
    bgp, bgp_debug = [], {}
    uplinks = []          # every EXTERNAL interface, resolved to segment/VLAN/edge node
    bgpcfg = {}           # (tier0, locale) -> local AS and knobs
    nbrcfg = []           # full neighbour configuration, not just live state
    if not DRY:
        for t0 in _res((data.get("tier0s") or {}).get("body")):
            t0id = t0.get("id")
            if not t0id:
                continue
            # prefix lists and route maps, so a route filter resolves to its contents
            st, pls = http("https://%s/policy/api/v1/infra/tier-0s/%s/prefix-lists" % (fqdn, t0id),
                           headers=H, timeout=40)
            plmap = {p.get("path"): {"name": p.get("display_name") or p.get("id"),
                                     "entries": ["%s %s%s" % (e.get("action", "?"), e.get("network", "?"),
                                                              (" le %s" % e["le"]) if e.get("le") else "")
                                                 for e in (p.get("prefixes") or [])]}
                     for p in _res(pls)}
            st, rms = http("https://%s/policy/api/v1/infra/tier-0s/%s/route-maps" % (fqdn, t0id),
                           headers=H, timeout=40)
            rmmap = {r.get("path"): (r.get("display_name") or r.get("id")) for r in _res(rms)}
            st, ls = http("https://%s/policy/api/v1/infra/tier-0s/%s/locale-services" % (fqdn, t0id), headers=H, timeout=40)
            dbg = {"locale_http": st, "locale_ids": [l.get("id") for l in _res(ls)], "neighbors": {}}
            if not _res(ls):
                dbg["locale_raw"] = str(ls)[:400]
            for l in _res(ls):
                lid = l.get("id")
                # ---- uplink interfaces
                st, ifs = http("https://%s/policy/api/v1/infra/tier-0s/%s/locale-services/%s/interfaces"
                               % (fqdn, t0id, lid), headers=H, timeout=40)
                for i in _res(ifs):
                    sub = (i.get("subnets") or [{}])[0]
                    addrs = sub.get("ip_addresses") or []
                    uplinks.append({
                        "tier0": t0.get("display_name"), "tier0_id": t0id, "locale": lid,
                        "name": i.get("display_name"), "type": i.get("type") or "EXTERNAL",
                        "address": addrs[0] if addrs else None, "prefix_len": sub.get("prefix_len"),
                        "segment_path": i.get("segment_path"), "edge_path": i.get("edge_path"),
                        "mtu": i.get("mtu"), "urpf": i.get("urpf_mode")})
                # ---- BGP configuration (local AS lives here, not on the neighbour)
                st, bc = http("https://%s/policy/api/v1/infra/tier-0s/%s/locale-services/%s/bgp"
                              % (fqdn, t0id, lid), headers=H, timeout=40)
                if isinstance(bc, dict) and bc:
                    gr = bc.get("graceful_restart_config") or {}
                    bgpcfg["%s|%s" % (t0.get("display_name"), lid)] = {
                        "tier0": t0.get("display_name"), "locale": lid,
                        "local_as": bc.get("local_as_num"), "enabled": bc.get("enabled"),
                        "ecmp": bc.get("ecmp"), "inter_sr_ibgp": bc.get("inter_sr_ibgp"),
                        "multipath_relax": bc.get("multipath_relax"),
                        "graceful_restart": gr.get("mode"),
                        "edge_cluster_path": l.get("edge_cluster_path"),
                        "redistribution": [
                            {"name": r_.get("name"), "types": r_.get("route_redistribution_types")}
                            for r_ in ((l.get("route_redistribution_config") or {})
                                       .get("redistribution_rules") or [])]}
                st, nb = http("https://%s/policy/api/v1/infra/tier-0s/%s/locale-services/%s/bgp/neighbors"
                              % (fqdn, t0id, lid), headers=H, timeout=40)
                dbg["neighbors"][lid] = {"http": st, "count": len(_res(nb)), "raw": str(nb)[:300] if not _res(nb) else ""}
                for n in _res(nb):
                    nid = n.get("id")
                    filt = []
                    for rf in (n.get("route_filtering") or []):
                        for d_ in ("in_route_filters", "out_route_filters"):
                            for f_ in (rf.get(d_) or []):
                                if f_ in rmmap:
                                    filt.append("%s route-map %s" % (d_, rmmap[f_]))
                                elif f_ in plmap:
                                    filt.append("%s prefix-list %s [%s]"
                                                % (d_, plmap[f_]["name"], "; ".join(plmap[f_]["entries"]) or "empty"))
                                else:
                                    filt.append("%s %s" % (d_, str(f_).rsplit("/", 1)[-1]))
                    nbrcfg.append({
                        "tier0": t0.get("display_name"), "locale": lid,
                        "peer": n.get("neighbor_address"), "remote_as": n.get("remote_as_num"),
                        "sources": n.get("source_addresses") or [],
                        "max_hop": n.get("maximum_hop_limit"),
                        "bfd": (n.get("bfd") or {}).get("enabled"),
                        "graceful_restart": n.get("graceful_restart_mode"),
                        "hold_down": n.get("hold_down_time"), "keepalive": n.get("keep_alive_time"),
                        "password_set": bool(n.get("password")), "allow_as_in": n.get("allow_as_in"),
                        "filters": filt})
                    base_ = "https://%s/policy/api/v1/infra/tier-0s/%s/locale-services/%s/bgp/neighbors/%s/status" % (fqdn, t0id, lid, nid)
                    st, stt = http(base_, headers=H, timeout=40)
                    if not _res(stt):
                        st, stt = http(base_ + "?enforcement_point_path=/infra/sites/default/enforcement-points/default",
                                       headers=H, timeout=40)
                    # 9.1 returns 404 on both of the above in this environment. Two more
                    # shapes, cheapest first: the per-Tier-0 summary, then the MP API.
                    # Without one of these no BGP session is ever machine-verified and
                    # 'get bgp neighbor summary' on the edge is the only source of truth.
                    if not _res(stt):
                        st, stt = http("https://%s/policy/api/v1/infra/tier-0s/%s/locale-services/%s/bgp/neighbors/status"
                                       % (fqdn, t0id, lid), headers=H, timeout=40)
                        stt = {"results": [r__ for r__ in _res(stt)
                                           if str(r__.get("neighbor_address") or
                                                  r__.get("source_address") or "") ==
                                           str(n.get("neighbor_address")) or not r__.get("neighbor_address")]}
                    if not _res(stt):
                        st, stt = http("https://%s/api/v1/logical-routers/%s/routing/bgp/neighbors/status"
                                       % (fqdn, t0id), headers=H, timeout=40)
                    dbg["neighbors"][lid][nid] = {"http": st, "rows": len(_res(stt)), "raw": str(stt)[:300] if not _res(stt) else ""}
                    for r_ in _res(stt):
                        bgp.append({"tier0": t0.get("display_name"), "neighbor": n.get("neighbor_address"),
                                    "remote_as": n.get("remote_as_num"), "edge": r_.get("transport_node") or r_.get("edge_node"),
                                    "state": r_.get("connection_state"),
                                    "in_prefixes": r_.get("total_in_prefix_count"),
                                    "out_prefixes": r_.get("total_out_prefix_count"),
                                    "uptime": r_.get("time_since_established")})
            bgp_debug[t0id] = dbg
        # TEP addresses per transport node from the node state: the reliable signal for
        # "is this edge's TEP on the host TEP network", independent of how the VLAN is tagged
        teps = {}
        for t in _res(data["transport_nodes"]["body"]):
            tid = t.get("id")
            kind = (t.get("node_deployment_info") or {}).get("resource_type") or ""
            if not tid or kind not in ("EdgeNode", "HostNode"):
                continue
            st, stt = http("https://%s/api/v1/transport-nodes/%s/state" % (fqdn, tid), headers=H, timeout=40)
            ips = []
            for hs in (stt.get("host_switch_states") or []) if isinstance(stt, dict) else []:
                for ep in hs.get("endpoints") or []:
                    if ep.get("ip"):
                        ips.append(ep["ip"])
            teps[t.get("display_name") or tid] = {"kind": kind, "teps": ips, "http": st}
        data["tn_teps"] = teps
    else:
        PLAN.append("GET  https://%s/policy/api/v1/infra/tier-0s/<t0>/locale-services/<ls>/interfaces  (uplinks)" % fqdn)
        PLAN.append("GET  https://%s/policy/api/v1/infra/tier-0s/<t0>/locale-services/<ls>/bgp  (local AS)" % fqdn)
        PLAN.append("GET  https://%s/policy/api/v1/infra/tier-0s/<t0>/prefix-lists, /route-maps  (route filters)" % fqdn)
        PLAN.append("GET  https://%s/policy/api/v1/infra/tier-0s/<t0>/locale-services/<ls>/bgp/neighbors/<n>/status  (per neighbour)" % fqdn)
        PLAN.append("GET  https://%s/api/v1/transport-nodes/<id>/state  (TEP addresses, per edge and host)" % fqdn)
    data["bgp_status"] = bgp
    data["bgp_debug"] = bgp_debug
    data["uplinks"] = uplinks
    data["bgp_config"] = bgpcfg
    data["bgp_neighbor_config"] = nbrcfg
    if not DRY and data["cluster_status"]["status"] in (401, 403):
        pw2 = reprompt(fqdn, "NSX '%s' password" % user)
        if pw2:
            return collect_nsx(out, fqdn, user, pw2)
    write_json(out, "nsx_%s" % fqdn, data)
    if DRY:
        return
    cs = data["cluster_status"]["body"] if isinstance(data["cluster_status"]["body"], dict) else {}
    if data["cluster_status"]["status"] != 200:
        bp("nsx", "%s API login" % fqdn, "FAIL", "HTTP %s" % data["cluster_status"]["status"])
        return
    overall = (cs.get("detailed_cluster_status") or {}).get("overall_status") or cs.get("mgmt_cluster_status", {}).get("status")
    bp("nsx", "%s cluster status" % fqdn, "PASS" if str(overall).upper() == "STABLE" else "WARN", overall)
    v = data["version"]["body"] if isinstance(data["version"]["body"], dict) else {}
    bp("nsx", "%s version" % fqdn, "INFO", v.get("product_version") or v.get("node_version"))
    tzs = _res(data["transport_zones"]["body"])
    dflt = [t.get("display_name") for t in tzs if t.get("is_default") and str(t.get("transport_type", "")).upper() == "OVERLAY"]
    bp("nsx", "%s default overlay transport zone" % fqdn, "PASS" if dflt else "FAIL",
       dflt or "none flagged is_default; Federation requires one per site")
    st, node = http("https://%s/api/v1/node" % fqdn, headers=H, timeout=30)
    stime = (node or {}).get("system_time") if isinstance(node, dict) else None
    if isinstance(stime, (int, float)):
        skew = abs(time.time() * 1000 - stime) / 1000.0
        bp("nsx", "%s clock within 60s of this host" % fqdn, "PASS" if skew < 60 else "FAIL", "%.0fs skew" % skew)
    data["node"] = {"status": st, "body": node}
    for b_ in bgp:
        est = str(b_.get("state") or "").upper() == "ESTABLISHED"
        label = "%s %s -> %s AS%s" % (fqdn, b_.get("tier0"), b_.get("neighbor"), b_.get("remote_as"))
        bp("nsx", "%s BGP established" % label, "PASS" if est else "FAIL", b_.get("state"))
        if est and (b_.get("in_prefixes") in (0, "0", None)) and (b_.get("out_prefixes") in (0, "0", None)):
            bp("nsx", "%s exchanges prefixes" % label, "WARN", "session up but 0 prefixes in and 0 out")
    # edge TEP must not sit on the host TEP network when edges run on prepared hosts.
    # Compared by TEP address (/24), which holds whether the VLAN is tagged by NSX or by the portgroup.
    def net24(ip):
        try:
            return str(ipaddress.ip_network(ip + "/24", strict=False))
        except Exception:
            return None
    teps = data.get("tn_teps") or {}
    host_nets = set(n_ for v in teps.values() if v["kind"] == "HostNode" for n_ in map(net24, v["teps"]) if n_)
    if not teps:
        bp("nsx", "%s edge/host TEP addresses readable" % fqdn, "SKIP", "transport-node state not returned")
    for name, v in sorted(teps.items()):
        if v["kind"] != "EdgeNode":
            continue
        if not v["teps"]:
            bp("nsx", "%s edge %s TEP separate from host TEP network" % (fqdn, name), "SKIP",
               "no TEP address in node state (HTTP %s)" % v.get("http"))
            continue
        clash = sorted(set(n_ for n_ in map(net24, v["teps"]) if n_ and n_ in host_nets))
        bp("nsx", "%s edge %s TEP separate from host TEP network" % (fqdn, name),
           "FAIL" if clash else "PASS",
           ("TEP %s is on host TEP network %s" % (v["teps"], clash)) if clash else
           ("edge TEP %s; host TEP networks %s" % (v["teps"], sorted(host_nets))))


# ---------------------------------------------------------------- federation readiness
FED_DCI_FLOWS = [
    ("Global Manager", "Local Manager", "TCP", "443", "Policy sync and API"),
    ("Global Manager", "Local Manager", "TCP", "1234", "GM to LM async replication"),
    ("Local Manager", "Global Manager", "TCP", "1235", "LM to GM async replication"),
    ("Edge RTEP", "Edge RTEP", "UDP", "6081", "Geneve, cross-site overlay"),
    ("Edge RTEP", "Edge RTEP", "UDP", "3784/3785", "BFD between remote tunnel endpoints"),
    ("Global Manager", "Global Manager", "TCP", "1234", "GM cluster sync, if a standby GM is deployed"),
]


def _res(obj):
    if isinstance(obj, dict) and isinstance(obj.get("results"), list):
        return obj["results"]
    return obj if isinstance(obj, list) else []


def _nb(d, k):
    v = (d.get(k) or {}).get("body")
    return v if v is not None else {}


def _rtep_vlan(rtep):
    """rtep_vlan is an int on some builds and {"vlan_id": N} on others."""
    if not isinstance(rtep, dict):
        return None
    v = rtep.get("rtep_vlan")
    if isinstance(v, dict):
        v = v.get("vlan_id")
    if isinstance(v, (list, tuple)):
        v = v[0] if v else None
    try:
        return int(v) if v is not None else None
    except (TypeError, ValueError):
        return None


def _rtep_ips(rtep):
    """Addresses appear under different keys depending on how the RTEP was assigned."""
    if not isinstance(rtep, dict):
        return []
    out = []
    for k in ("rtep_ips", "ip_addresses"):
        v = rtep.get(k)
        if isinstance(v, list):
            out.extend(str(x) for x in v if x)
    spec = rtep.get("ip_assignment_spec")
    if isinstance(spec, dict):
        for k in ("ip_list", "ip_addresses"):
            v = spec.get(k)
            if isinstance(v, list):
                out.extend(str(x) for x in v if x)
    for v in rtep.values():
        if isinstance(v, str) and re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", v):
            out.append(v)
    return sorted(set(out))


def fed_edge_nodes(nsx, only=None):
    tn = {t.get("id"): t for t in _res(_nb(nsx, "transport_nodes"))}
    out = []
    for ec in _res(_nb(nsx, "edge_clusters")):
        name = ec.get("display_name")
        if only and name not in only:
            continue
        for m in ec.get("members") or []:
            node = tn.get(m.get("transport_node_id")) or {}
            out.append({"cluster": name, "node_id": m.get("transport_node_id"),
                        "name": node.get("display_name") or m.get("transport_node_id"),
                        "fqdn": ((node.get("node_deployment_info") or {}).get("node_settings") or {}).get("hostname"),
                        "rtep": node.get("remote_tunnel_endpoint"),
                        "rtep_ips": _rtep_ips(node.get("remote_tunnel_endpoint")),
                        "rtep_vlan": _rtep_vlan(node.get("remote_tunnel_endpoint"))})
    return out


def fed_assess(cfg, sites, tls):
    """sites: OrderedDict tag -> {"fqdn": lm_fqdn, "data": nsx_data}. Returns dict of outputs."""
    ck, dns, ips, decisions, plan = [], [], [], [], {}

    def c(area, item, state, detail=""):
        ck.append({"area": area, "item": item, "state": state, "detail": str(detail)[:300]})

    tags = list(sites)
    vers = {t: (_nb(sites[t]["data"], "version") or {}).get("product_version") for t in tags}
    if all(vers.values()):
        c("prereq", "Local Manager versions match", "PASS" if len(set(vers.values())) == 1 else "FAIL", vers)
    else:
        c("prereq", "Local Manager versions readable", "SKIP", vers)
    for t in tags:
        d = sites[t]["data"]
        cs = _nb(d, "cluster_status")
        overall = ((cs.get("detailed_cluster_status") or {}).get("overall_status")
                   or (cs.get("mgmt_cluster_status") or {}).get("status"))
        c("prereq", "%s manager cluster stable" % t, "PASS" if str(overall).upper() == "STABLE" else "WARN", overall)
        lic = _res(_nb(d, "licenses"))
        names = [l.get("description") or l.get("product_name") or "" for l in lic]
        evals = [l for l in lic if l.get("is_eval") or "eval" in " ".join(names).lower()]
        c("prereq", "%s licence permits Federation" % t, "WARN" if evals or not lic else "INFO",
          "Enterprise Plus or higher required. Found: %s" % (names or "none reported"))
        extra = [x.get("display_name") for x in _res(_nb(d, "sites")) if str(x.get("id", "")).lower() != "default"]
        if cfg.get("nsx_gm_host"):
            c("state", "%s registered with a Global Manager" % t, "PASS" if extra else "WARN",
              "sites: %s" % (extra or "default only; not federated"))
        else:
            c("state", "%s not already federated" % t, "WARN" if extra else "PASS",
              "sites: %s" % (extra or "default only"))
        projs = [x.get("display_name") for x in _res(_nb(d, "projects"))
                 if str(x.get("id", "")).lower() not in ("default", "infra")]
        c("conflict", "%s has no NSX Projects in use" % t, "FAIL" if projs else "PASS",
          "Projects/VPCs are not supported with Federation. Found: %s" % (projs or "none"))
        for t0 in _res(_nb(d, "tier0s")):
            c("inventory", "%s Tier-0 %s" % (t, t0.get("display_name")), "INFO",
              "ha_mode=%s failover=%s" % (t0.get("ha_mode"), t0.get("failover_mode")))
        fp = (tls.get(sites[t]["fqdn"]) or {}).get("sha256_fingerprint")
        c("gm", "%s Local Manager API thumbprint captured" % t, "PASS" if fp else "SKIP",
          fp or "TLS sweep did not return a fingerprint")
        sites[t]["thumbprint"] = fp
        only = cfg.get("fed_edge_clusters_%s" % t) or None
        lm_clusters = [ec.get("display_name") for ec in _res(_nb(d, "edge_clusters"))]
        for want in (only or []):
            c("rtep", "%s edge cluster %s exists on the Local Manager" % (t, want),
              "PASS" if want in lm_clusters else "FAIL",
              "LM has: %s" % (lm_clusters or "none"))
        nodes = fed_edge_nodes(d, only)
        if not nodes:
            c("rtep", "%s edge nodes discovered" % t, "FAIL", "no edge cluster members found")
            continue
        c("rtep", "%s edge nodes discovered" % t, "PASS", "%d: %s" % (len(nodes), ", ".join(n["name"] for n in nodes)))
        vlan = cfg.get("fed_rtep_vlan_%s" % t)
        cidr = cfg.get("fed_rtep_cidr_%s" % t)
        gw = cfg.get("fed_rtep_gateway_%s" % t)
        plan[t] = {"vlan": vlan, "cidr": cidr, "gateway": gw, "nodes": nodes}
        done = [n for n in nodes if n.get("rtep")]
        if cfg.get("nsx_gm_host"):
            c("rtep", "%s RTEP configured on edges" % t,
              "PASS" if len(done) == len(nodes) else ("WARN" if done else "FAIL"),
              "%d of %d node(s) have a remote tunnel endpoint" % (len(done), len(nodes)))
        else:
            c("rtep", "%s RTEP configured on edges" % t, "PASS" if len(done) == len(nodes) else "INFO",
              "%d of %d node(s); configured in runbook Phase 2 / Phase 5" % (len(done), len(nodes)))
        if not (vlan and cidr and gw):
            decisions.append("%s: RTEP VLAN, subnet and gateway (fed_rtep_vlan_%s / _cidr_ / _gateway_)" % (t, t))
            c("rtep", "%s RTEP addressing planned" % t, "DECIDE", "needs VLAN, subnet, gateway")
        else:
            c("rtep", "%s RTEP addressing planned" % t, "PASS", "VLAN %s  %s  gw %s" % (vlan, cidr, gw))
            try:
                usable = sum(1 for _ in ipaddress.ip_network(str(cidr), strict=False).hosts())
                c("rtep", "%s RTEP subnet large enough" % t, "PASS" if usable >= len(nodes) + 1 else "FAIL",
                  "%d usable, %d node(s) plus gateway" % (usable, len(nodes)))
            except Exception as e:
                c("rtep", "%s RTEP subnet parses" % t, "FAIL", str(e))
        for n in nodes:
            ips.append({"site": t, "purpose": "Edge RTEP", "object": n["name"], "vlan": vlan or "TBD",
                        "subnet": cidr or "TBD", "gateway": gw or "TBD",
                        "address": "configured" if n.get("rtep") else "",
                        "status": "configured" if n.get("rtep") else "to allocate"})

    if cfg.get("nsx_gm_host"):
        c("gm", "Global Manager already deployed", "INFO",
          "%s; GM addressing worksheet not generated. See the federation health checks." % cfg["nsx_gm_host"])
        c("gm", "Global Manager lifecycle is manual", "INFO",
          "VCF does not deploy or upgrade Global Managers; GM upgrades precede any LM upgrade.")
        return {"checks": ck, "dns": dns, "ips": ips, "decisions": decisions, "plan": plan, "sites": sites}
    n_gm = int(cfg.get("fed_gm_node_count") or 3)
    dom = cfg.get("fed_gm_domain") or ""

    def gm_cluster(prefix, label, site):
        """Rows for one GM cluster (active or standby). prefix: 'fed_gm' or 'fed_gm_standby'."""
        have_any = False
        mask, gw = cfg.get(prefix + "_netmask") or cfg.get("fed_gm_netmask"), cfg.get(prefix + "_gateway")
        entries = []
        for i in range(1, n_gm + 1):
            f, ip = cfg.get("%s_node%d_fqdn" % (prefix, i)), cfg.get("%s_node%d_ip" % (prefix, i))
            have_any = have_any or bool(f or ip)
            entries.append((f, ip, "%s node %d" % (label, i)))
        if n_gm > 1:
            vf, vip = cfg.get(prefix + "_vip_fqdn"), cfg.get(prefix + "_vip_ip")
            have_any = have_any or bool(vf or vip)
            entries.append((vf, vip, "%s cluster VIP" % label))
        for f, ip, purpose in entries:
            dns.append({"record": f or "TBD", "type": "A", "value": ip or "TBD", "purpose": purpose,
                        "status": "supplied" if (f and ip) else "to allocate"})
            ips.append({"site": site, "purpose": purpose, "object": f or "TBD", "vlan": "management",
                        "subnet": mask or "TBD", "gateway": gw or "TBD", "address": ip or "",
                        "status": "supplied" if ip else "to allocate"})
            if f and ip and not DRY:
                # pre-checks: forward and reverse DNS agree, and nothing already answers on 443
                try:
                    fwd = socket.gethostbyname(f)
                    c("gm-precheck", "%s resolves to %s" % (f, ip), "PASS" if fwd == ip else "FAIL", "DNS A -> %s" % fwd)
                except Exception as e:
                    c("gm-precheck", "%s resolves to %s" % (f, ip), "FAIL", "no A record: %s" % str(e)[:60])
                try:
                    rev = socket.gethostbyaddr(ip)[0]
                    c("gm-precheck", "%s reverse-resolves to %s" % (ip, f), "PASS" if rev.lower() == f.lower() else "WARN", "PTR -> %s" % rev)
                except Exception as e:
                    c("gm-precheck", "%s reverse-resolves to %s" % (ip, f), "FAIL", "no PTR: %s" % str(e)[:60])
                try:
                    sk = socket.create_connection((ip, 443), timeout=3)
                    sk.close()
                    c("gm-precheck", "%s not already in use" % ip, "FAIL", "something answers on 443; GM not deployed yet?")
                except Exception:
                    c("gm-precheck", "%s not already in use" % ip, "PASS", "no listener on 443")
        return have_any, gw, mask

    gm_site = cfg.get("fed_gm_site") or (tags[0] if tags else "")
    have, gw_a, mask_a = gm_cluster("fed_gm", "Active Global Manager", gm_site)
    c("gm", "Active Global Manager addressing supplied", "PASS" if have else "DECIDE",
      "%d node(s)%s at %s" % (n_gm, " plus VIP" if n_gm > 1 else "", gm_site))
    if not have:
        decisions.append("Active Global Manager FQDNs and IPs (fed_gm_node1_fqdn / _ip ...)")
    if not gw_a:
        decisions.append("Active Global Manager gateway and netmask (fed_gm_gateway / fed_gm_netmask)")
    sb_site = cfg.get("fed_gm_standby_site")
    if sb_site or any(cfg.get("fed_gm_standby_node%d_fqdn" % i) for i in range(1, n_gm + 1)):
        have_sb, gw_b, _ = gm_cluster("fed_gm_standby", "Standby Global Manager", sb_site or "?")
        c("gm", "Standby Global Manager addressing supplied", "PASS" if have_sb else "DECIDE",
          "%d node(s)%s at %s" % (n_gm, " plus VIP" if n_gm > 1 else "", sb_site or "?"))
        if not have_sb:
            decisions.append("Standby Global Manager FQDNs and IPs (fed_gm_standby_node1_fqdn / _ip ...)")
    else:
        c("gm", "Standby Global Manager planned", "WARN", "no fed_gm_standby_* keys; a single GM has no failover")
    for row in list(dns):
        if row["type"] == "A":
            dns.append({"record": row["value"], "type": "PTR", "value": row["record"],
                        "purpose": row["purpose"] + " (reverse)", "status": row["status"]})
    c("gm", "Global Manager lifecycle is manual", "INFO",
      "VCF does not deploy or upgrade Global Managers; GM upgrades precede any LM upgrade.")
    return {"checks": ck, "dns": dns, "ips": ips, "decisions": decisions, "plan": plan, "sites": sites}


def fed_runbook(cfg, fed, ctx):
    """Concrete, ordered procedure following the VCF 9.1 'Configuring NSX Federation' sequence,
    with every value this run knows filled in and every unknown marked <CONFIRM>."""
    n = int(cfg.get("fed_gm_node_count") or 3)
    tags = list(fed["sites"])
    a = cfg.get("fed_gm_site") or (tags[0] if tags else "site-a")
    b = cfg.get("fed_gm_standby_site") or (tags[1] if len(tags) > 1 else "site-b")
    g = lambda k, d="<CONFIRM>": cfg.get(k) or d
    mtu = int(cfg.get("fed_rtep_mtu") or 1700)
    sa, sb = ctx.get(a, {}), ctx.get(b, {})
    pa_, pb_ = ctx.get(a, {}).get("placement") or {}, ctx.get(b, {}).get("placement") or {}
    pa, pb = fed["plan"].get(a, {}), fed["plan"].get(b, {})
    L = []
    A = L.append
    A("NSX FEDERATION RUNBOOK   generated %s" % now())
    A("Path B: active Global Manager at %s, standby at %s, RTEP at both sites." % (a, b))
    A("Sequence follows VCF 9.1 'Configuring NSX Federation for the VCF Management Components'.")
    A("Anything marked <CONFIRM> was not available to this run and must be filled in before use.")
    A("")
    A("=" * 74); A(" 0. GATE  --  every line PASS in readiness.txt before Phase 1"); A("=" * 74)
    for line in ("Local Manager versions match on both sites",
                 "Licence entitles Federation on both LMs and on the GM (eval expiry blocks this)",
                 "No NSX Projects on either Local Manager",
                 "All Global Manager A and PTR records resolve; no address already answers on 443",
                 "RTEP VLAN present on the leaves at both sites",
                 "DCI carries MTU %d between the two RTEP subnets (measured, not assumed); 1700 is the minimum" % mtu,
                 "DCI routes the two RTEP subnets with no NAT; flows in dci_firewall.csv are open",
                 "One default overlay transport zone per site",
                 "Change window agreed: GM deployment is non-disruptive; RTEP config touches edges"):
        A("  [ ] " + line)
    A("")
    def gm_block(prefix, site, sctx, title):
        A("=" * 74); A(" %s" % title); A("=" * 74)
        pl_ = sctx.get("placement") or {}
        A("  Compute manager : %s   (management vCenter for %s)" % (sctx.get("mgmt_vcenter", "<CONFIRM>"), site))
        A("  vCenter thumbprint (Add Compute Manager asks for it): %s" % (sctx.get("vc_thumbprint") or "<accept in UI>"))
        A("  Cluster         : %s" % (pl_.get("cluster") or sctx.get("mgmt_cluster", "<CONFIRM>")))
        A("  Portgroup       : %s   (same as %s)" % ((pl_.get("networks") or ["<CONFIRM>"])[0], pl_.get("vm", "the LM node")))
        A("  Datastore       : %s" % (pl_.get("datastore") or "<CONFIRM>"))
        A("  VM folder       : %s" % (pl_.get("folder") or "same as the LM VMs"))
        A("  Size            : %s" % g("fed_gm_size", "Medium"))
        A("                    Medium is the VCF design default for a GM serving a management domain; Large mirrors the")
        A("                    existing reference. Confirm capacity on the cluster above before choosing Large.")
        A("  Netmask / GW    : %s / %s" % (g(prefix + "_netmask", g("fed_gm_netmask")), g(prefix + "_gateway")))
        A("  DNS             : %s" % ", ".join(sctx.get("dns", [])) or "<CONFIRM>")
        A("  NTP             : %s" % ", ".join(sctx.get("ntp", [])) or "<CONFIRM>")
        for i in range(1, n + 1):
            A("  Node %d          : %-32s %s" % (i, g("%s_node%d_fqdn" % (prefix, i)), g("%s_node%d_ip" % (prefix, i))))
        A("  VIP             : %-32s %s" % (g(prefix + "_vip_fqdn"), g(prefix + "_vip_ip")))
        A("")
        A("  1. Deploy node 1 from the NSX unified appliance OVA, role = NSX Global Manager, size as above.")
        A("  2. Log in to node 1  ->  System > Fabric > Compute Managers  ->  add %s." % sctx.get("mgmt_vcenter", "<CONFIRM>"))
        A("  3. System > Appliances > Add NSX Appliance  x2  ->  nodes 2 and 3 with the values above.")
        A("  4. System > Appliances > Set Virtual IP  ->  %s." % g(prefix + "_vip_ip"))
        A("  5. In vCenter, create an anti-affinity rule keeping the three GM VMs on separate hosts.")
        A("  6. System > Licenses  ->  apply the licence that entitles Federation.")
        A("  7. Verify: https://%s  logs in; System > Appliances shows 3 nodes STABLE." % g(prefix + "_vip_fqdn"))
        A("")
    gm_block("fed_gm", a, sa, "PHASE 1  --  Global Manager cluster at %s (active)" % a)
    def rtep_block(site, sctx, plan, phase, title):
        A("=" * 74); A(" %s  --  %s" % (phase, title)); A("=" * 74)
        A("  Local Manager   : %s" % sctx.get("lm", "<CONFIRM>"))
        A("  LM thumbprint   : %s" % (fed["sites"].get(site, {}).get("thumbprint") or "<CONFIRM: readiness.txt>"))
        ecs = cfg.get("fed_edge_clusters_%s" % site) or sorted(set(nd["cluster"] for nd in plan.get("nodes", [])))
        A("  Edge cluster(s) : %s" % (", ".join(ecs) if ecs else "<CONFIRM>"))
        A("  RTEP VLAN       : %s" % (plan.get("vlan") or "<CONFIRM>"))
        A("  RTEP subnet/GW  : %s / %s" % (plan.get("cidr") or "<CONFIRM>", plan.get("gateway") or "<CONFIRM>"))
        A("  RTEP pool range : %s" % g("fed_rtep_range_%s" % site))
        A("  Inter-site MTU  : %s   (what the DCI carries; 1700 is the minimum, raise only after the path is measured)" % mtu)
        A("  Edge nodes      : %s" % (", ".join(nd["name"] for nd in plan.get("nodes", [])) or "<CONFIRM>"))
        A("")
        A("  1. On the LM: Networking > IP Address Pools > Add  ->  name rtep-pool-%s, subnet above, gateway above, range above." % site)
        A("  2. System > Fabric > Edges > Edge Clusters > %s > Actions > Configure Remote Tunnel Endpoint" % (ecs[0] if ecs else "<cluster>"))
        A("       host switch: the edge N-VDS, teaming: default, VLAN %s, pool rtep-pool-%s, Inter Location MTU %s." % (plan.get("vlan") or "<CONFIRM>", site, mtu))
        A("  3. Verify on every edge:  ssh admin@<edge>  ->  get remote-tunnel-endpoint  (address from the pool, state Up).")
        A("")
    rtep_block(a, sa, pa, "PHASE 2", "prepare %s Local Manager (RTEP)" % a)
    A("=" * 74); A(" PHASE 3  --  enable Federation at %s" % a); A("=" * 74)
    A("  1. On the GM VIP https://%s : System > Location Manager > MAKE ACTIVE  (name: %s-gm)." % (g("fed_gm_vip_fqdn"), a))
    A("  2. Location Manager > Locations > ADD LOCATION:")
    A("       name %s, FQDN %s, admin credentials, thumbprint %s" % (a, sa.get("lm", "<CONFIRM>"), fed["sites"].get(a, {}).get("thumbprint") or "<CONFIRM>"))
    A("  3. When prompted, confirm the edge nodes' RTEP mapping.")
    A("  4. Wait until Location Manager shows %s registered and SYNCED." % a)
    A("")
    gm_block("fed_gm_standby", b, sb, "PHASE 4  --  Global Manager cluster at %s (standby)" % b)
    A("  8. On the ACTIVE GM: Location Manager > Standby Global Manager > ADD:")
    A("       FQDN %s, admin credentials, thumbprint of %s." % (g("fed_gm_standby_vip_fqdn"), g("fed_gm_standby_vip_fqdn")))
    A("  9. Confirm the standby shows SYNCED.")
    A("")
    rtep_block(b, sb, pb, "PHASE 5", "prepare %s Local Manager (RTEP) and add location" % b)
    A("  4. On the ACTIVE GM: Location Manager > ADD LOCATION: name %s, FQDN %s, thumbprint %s." % (b, sb.get("lm", "<CONFIRM>"), fed["sites"].get(b, {}).get("thumbprint") or "<CONFIRM>"))
    A("  5. Run validation.txt: remote tunnel endpoints Up both sides; DF-bit pings at %d bytes pass every direction." % (mtu - 28))
    A("")
    A("=" * 74); A(" PHASE 6  --  first stretched objects (from the GM, Policy mode)"); A("=" * 74)
    A("  1. Networking > Tier-0 Gateways > ADD: name T0-STRETCHED-%s-%s, HA Active-Active," % (a.upper(), b.upper()))
    A("       Locations: %s PRIMARY (edge cluster %s), %s PRIMARY (edge cluster %s)." % (
        a, (cfg.get("fed_edge_clusters_%s" % a) or ["<CONFIRM>"])[0], b, (cfg.get("fed_edge_clusters_%s" % b) or ["<CONFIRM>"])[0]))
    A("       Active-Active cannot host stateful services (NAT/FW); use Active-Standby if those are required.")
    A("       Interfaces and BGP per site as the design dictates, or keep egress on the existing local Tier-0s.")
    A("  2. Tier-1 Gateway > ADD: name T1-STRETCHED-01, linked to the stretched Tier-0,")
    A("       locations %s PRIMARY, %s SECONDARY  (this is where failover lives)." % (a, b))
    A("  3. Segment > ADD: connected to T1-STRETCHED-01, span both locations, subnet from the customer plan.")
    A("  4. Place ONE low-risk VM on the segment. Fail the Tier-1 over to %s; confirm the VM keeps its address and connectivity." % b)
    A("     Only after that succeeds: production workloads.")
    A("")
    A("=" * 74); A(" PHASE 7  --  validate and hand over"); A("=" * 74)
    A("  - Location Manager: both sites SYNCED; realization SUCCESS on every stretched object at both sites.")
    A("  - Re-run fleetparity with nsx_gm_host = %s : federation health section all PASS." % g("fed_gm_vip_fqdn"))
    A("  - Record for operations: VCF does not upgrade Global Managers. GM is upgraded manually, before any LM upgrade.")
    A("  - Kubernetes stays site-local on the Local Managers; stretched segments carry VMs, not Supervisor networks.")
    A("")
    A("=" * 74); A(" ROLLBACK"); A("=" * 74)
    A("  Remove the location from the GM; remove RTEP from the edge cluster; power off the GM appliances.")
    A("  LM-local Tier-0s, edges and segments are unaffected throughout.")
    return "\n".join(L)


# ---------------------------------------------------------------- north-south (stretched Tier-0 uplinks)
def _ipsort(addrs):
    """Sort dotted quads numerically, not lexically."""
    def k(a):
        try:
            return (0, int(ipaddress.ip_address(a)))
        except Exception:
            return (1, 0)
    return sorted(addrs, key=k)


def _tz_names(nsx):
    """transport-zone id -> display name, from the Local Manager."""
    out = {}
    for t in _res(_nb(nsx, "transport_zones")):
        out[t.get("id")] = t.get("display_name") or t.get("id")
    return out


def _seg_map(nsx):
    """segment path -> {name, vlans, tz, attached}"""
    m = {}
    for s in _res(_nb(nsx, "segments")):
        m[s.get("path")] = {
            "name": s.get("display_name") or s.get("id"),
            "vlans": ",".join(str(v) for v in (s.get("vlan_ids") or [])) or "",
            "tz": str(s.get("transport_zone_path") or "").rsplit("/", 1)[-1],
            "attached": str(s.get("connectivity_path") or "").rsplit("/", 1)[-1] or None,
            "kind": "VLAN" if s.get("vlan_ids") else "OVERLAY",
            "advanced_config": s.get("advanced_config") or {},
            "teaming": (s.get("advanced_config") or {}).get("uplink_teaming_policy_name")}
    return m


def _edge_map(nsx):
    m = {}
    for t in _res(_nb(nsx, "transport_nodes")):
        m[t.get("id")] = t.get("display_name") or t.get("id")
    return m


def fed_uplinks(cfg, sites, gm_data=None):
    """Derive the north-south plan: existing uplink subnets per site, free addresses for the
    stretched Tier-0, peers and AS numbers, and what the Global Manager still needs.

    sites: OrderedDict tag -> {"fqdn": lm_fqdn, "data": nsx_data}   (same shape as fed_assess)
    Returns {"checks", "sites", "alloc", "neighbors", "gm", "decisions"}."""
    ck, alloc, nbr_rows, decisions = [], [], [], []
    out_sites = collections.OrderedDict()
    want = int(cfg.get("fed_ns_uplinks_per_node") or 1)  # informational only

    def c(area, item, state, detail=""):
        ck.append({"area": area, "item": item, "state": state, "detail": str(detail)[:300]})

    stretched = (cfg.get("fed_ns_tier0_name") or "").strip()

    for tag, sd in sites.items():
        d = sd.get("data") or {}
        segs, edges = _seg_map(d), _edge_map(d)
        ref = (cfg.get("fed_ns_reference_tier0_%s" % tag) or "").strip()
        ups = [u for u in (d.get("uplinks") or []) if (u.get("type") or "EXTERNAL") == "EXTERNAL"]
        if ref:
            ups = [u for u in ups if u.get("tier0") == ref]
        if not ups:
            c("uplink", "%s reference Tier-0 uplinks readable" % tag, "FAIL",
              "no external interfaces found%s" % (" on %s" % ref if ref else ""))
            continue
        seen_t0 = sorted(set(u["tier0"] for u in ups))
        if not ref and len(seen_t0) > 1:
            c("uplink", "%s reference Tier-0 is unambiguous" % tag, "DECIDE",
              "several Tier-0s have uplinks: %s -- set fed_ns_reference_tier0_%s" % (seen_t0, tag))
            decisions.append("%s: which Tier-0 to copy uplink design from (fed_ns_reference_tier0_%s)" % (tag, tag))
        ref = ref or seen_t0[0]
        c("uplink", "%s reference Tier-0" % tag, "PASS", "%s, %d external interface(s)" % (ref, len(ups)))

        # local AS of the reference Tier-0
        local_as = None
        for k, v in (d.get("bgp_config") or {}).items():
            if v.get("tier0") == ref and v.get("local_as") is not None:
                local_as = v["local_as"]
        c("uplink", "%s reference Tier-0 local AS" % tag, "PASS" if local_as else "FAIL", local_as or "not returned")

        nbrs = [n for n in (d.get("bgp_neighbor_config") or []) if n.get("tier0") == ref]
        for n in nbrs:
            nbr_rows.append(dict(n, site=tag))
            if n.get("password_set"):
                c("uplink", "%s peer %s uses a BGP password" % (tag, n.get("peer")), "DECIDE",
                  "the API will not return it; the new session needs the same value")
                decisions.append("%s: BGP password for peer %s (from the leaf configuration)" % (tag, n.get("peer")))
            for f in n.get("filters") or []:
                if "prefix-list" not in f:
                    continue
                c("uplink", "%s peer %s route filter" % (tag, n.get("peer")), "INFO", f)
                if not f.startswith("out_route_filters"):
                    continue
                want = str(cfg.get("fed_ns_test_subnet") or "").strip()
                if not want:
                    continue
                nets = re.findall(r"(\d+\.\d+\.\d+\.\d+/\d+)", f)
                covered = False
                try:
                    w = ipaddress.ip_network(want, strict=False)
                    for n_ in nets:
                        try:
                            if w.subnet_of(ipaddress.ip_network(n_, strict=False)):
                                covered = True
                        except Exception:
                            pass
                except Exception:
                    continue
                denies_rest = bool(re.search(r"DENY\s+any", f, re.I))
                if not covered and denies_rest:
                    _built = [u for u in ((gm_data or {}).get("gm_uplinks") or [])
                              if stretched and u.get("tier0") == stretched]
                    if _built:
                        c("uplink", "%s outbound filter on %s" % (tag, stretched), "WARN",
                          "%s carries no outbound prefix filter, so it advertises everything "
                          "redistributed to it. The local Tier-0 %s filters with %s, which "
                          "denies %s. Not a planning decision any more -- confirm what is "
                          "actually leaving with 'get route bgp' in the SR VRF."
                          % (stretched, ref, f.split("[")[0].strip(), want))
                    else:
                        c("uplink", "%s reference Tier-0 advertises %s" % (tag, want), "DECIDE",
                          "%s denies it. The new Tier-0 is created with NO outbound filter, so it "
                          "would advertise everything. Decide: mirror this filter with %s added, or "
                          "leave the new sessions unfiltered." % (f.split("[")[0].strip(), want))
                        decisions.append("%s: outbound prefix policy for the stretched Tier-0 -- "
                                         "%s is not in the reference filter" % (tag, want))

        # group interfaces into uplink subnets
        _gm = gm_data if isinstance(gm_data, dict) else {}
        _gmsegs = {sg.get("path"): sg for sg in _res((_gm.get("segments") or {}).get("body"))}
        ups_stretched = [u for u in (_gm.get("gm_uplinks") or [])
                         if stretched and u.get("tier0") == stretched
                         and u.get("locale") == tag]
        bysub = collections.OrderedDict()
        ref_teaming, ref_adv = {}, {}
        for u in ups:
            if not (u.get("address") and u.get("prefix_len")):
                continue
            try:
                net = str(ipaddress.ip_network("%s/%s" % (u["address"], u["prefix_len"]), strict=False))
            except Exception:
                continue
            sm = segs.get(u.get("segment_path")) or {}
            key = (net, sm.get("name") or "?", sm.get("vlans") or "?")
            bysub.setdefault(key, {"used": [], "mtu": set(), "urpf": set(),
                                   "segment_path": u.get("segment_path"), "nodes": []})
            bysub[key]["used"].append(u["address"])
            bysub[key]["mtu"].add(u.get("mtu"))
            bysub[key]["urpf"].add(u.get("urpf"))
            bysub[key]["nodes"].append(edges.get(str(u.get("edge_path") or "").rsplit("/", 1)[-1],
                                                 str(u.get("edge_path") or "").rsplit("/", 1)[-1]))
            ref_teaming[key] = sm.get("teaming")
            ref_adv[key] = sm.get("advanced_config") or {}

        tzn = _tz_names(d)
        used_tz = collections.Counter()
        for u in ups:
            sm = segs.get(u.get("segment_path")) or {}
            if sm.get("tz"):
                used_tz[tzn.get(sm["tz"], sm["tz"])] += 1
        uplink_tz = used_tz.most_common(1)[0][0] if used_tz else None
        if uplink_tz:
            c("uplink", "%s uplink transport zone" % tag, "PASS",
              "%s (from %s's own uplink segments)" % (uplink_tz, ref))
        site_plan = {"lm": sd.get("fqdn"), "reference_tier0": ref, "local_as": local_as,
                     "uplink_tz": uplink_tz, "subnets": [], "neighbors": nbrs}
        # The planner copies the reference Tier-0's uplink design. That is right only
        # while the stretched Tier-0 mirrors it. Once the design moves to its own VLANs,
        # its own transport zone or its own peers, copying silently proposes the OLD
        # ones. fed_ns_expect_vlans_<tag> makes that mismatch loud instead of silent.
        want_vlans = [str(x).strip() for x in (cfg.get("fed_ns_expect_vlans_%s" % tag) or [])
                      if str(x).strip()]
        # Once the stretched Tier-0 has its own uplinks it IS the source of truth, and the
        # reference Tier-0 stops being relevant. Judge what is built; only fall back to
        # comparing the reference when there is nothing built yet to compare.
        built_vlans = sorted(set(
            str(v) for u in ups_stretched
            for v in (((_gmsegs.get(u.get("segment_path")) or {}).get("vlan_ids")) or [])))
        if want_vlans and built_vlans:
            if sorted(want_vlans) == built_vlans:
                c("uplink", "%s uplink VLANs" % tag, "PASS",
                  "%s is built on VLAN %s, as designed. Reference Tier-0 %s is on VLAN %s "
                  "and is no longer used as a source -- it is the untouched local gateway."
                  % (stretched, ",".join(built_vlans), ref,
                     ",".join(sorted(set(str(vl) for (_n, _s, vl) in bysub.keys()
                                         if vl is not None))) or "none"))
            else:
                c("uplink", "%s uplink VLANs" % tag, "FAIL",
                  "design expects VLAN %s but %s is built on VLAN %s"
                  % (",".join(want_vlans), stretched, ",".join(built_vlans) or "none"))
        elif want_vlans:
            got_vlans = sorted(set(str(vl) for (_n, _s, vl) in bysub.keys() if vl is not None))
            if sorted(want_vlans) != got_vlans:
                c("uplink", "%s uplink VLANs" % tag, "FAIL",
                  "nothing is built on %s yet, and the planner would copy reference Tier-0 "
                  "%s, which is on VLAN %s -- not the %s the design calls for. Build the "
                  "first uplink by hand, or point fed_ns_reference_tier0_%s at a Tier-0 "
                  "that already uses the new VLANs."
                  % (stretched, ref, ",".join(got_vlans) or "none",
                     ",".join(want_vlans), tag))
                decisions.append("%s: uplink VLAN mismatch, planner output is not safe to "
                                 "apply (fed_ns_expect_vlans_%s)" % (tag, tag))
            else:
                c("uplink", "%s uplink VLANs" % tag, "PASS", ",".join(got_vlans))
        edge_nodes = sorted(set(n for v in bysub.values() for n in v["nodes"] if n))
        n_nodes = len(edge_nodes) or int(cfg.get("fed_ns_edge_nodes_%s" % tag) or 4)
        for (net, sname, vlan), v in bysub.items():
            peers = []
            for n in nbrs:
                try:
                    if ipaddress.ip_address(n["peer"]) in ipaddress.ip_network(net):
                        peers.append(n)
                except Exception:
                    pass
            taken = set(v["used"]) | set(p["peer"] for p in peers)
            free = []
            try:
                for ip in ipaddress.ip_network(net).hosts():
                    if str(ip) not in taken:
                        free.append(str(ip))
                    if len(free) >= n_nodes:
                        break
            except Exception:
                pass
            mtus = sorted(x for x in v["mtu"] if x)
            row = {"subnet": net, "segment": sname, "vlan": vlan,
                   "teaming": ref_teaming.get((net, sname, vlan)),
                   "adv": ref_adv.get((net, sname, vlan)) or {},
                   "in_use": _ipsort(taken),
                   "free": free, "mtu": mtus[0] if mtus else None,
                   "urpf": sorted(x for x in v["urpf"] if x)[:1],
                   "peers": [p["peer"] for p in peers],
                   "remote_as": sorted(set(p["remote_as"] for p in peers)),
                   "nodes": sorted(set(v["nodes"]))}
            site_plan["subnets"].append(row)
            tm = ref_teaming.get((net, sname, vlan))
            c("uplink", "%s %s uplink teaming policy" % (tag, net),
              "PASS" if tm else "INFO",
              tm or "reference segment has no named teaming policy; the new segment "
                    "will not set one either")
            c("uplink", "%s %s free addresses" % (tag, net),
              "PASS" if len(free) >= n_nodes else "FAIL",
              "%d free, %d edge node(s) need addresses; next: %s"
              % (len(free), n_nodes, ", ".join(free) or "none"))
            for i, a_ in enumerate(free[:n_nodes]):
                alloc.append({"site": tag, "purpose": "stretched Tier-0 uplink",
                              "object": "%s-%s" % (stretched or "T0-STRETCHED",
                                                   (edge_nodes[i] if i < len(edge_nodes) else "edge%d" % (i + 1))),
                              "vlan": vlan, "subnet": net, "address": a_,
                              "peer": ", ".join(row["peers"]) or "TBD",
                              "remote_as": ", ".join(str(x) for x in row["remote_as"]) or "TBD",
                              "mtu": row["mtu"] or "TBD", "status": "proposed -- confirm free"})
        if len(set(r["mtu"] for r in site_plan["subnets"] if r["mtu"])) > 1:
            c("uplink", "%s uplink MTU consistent" % tag, "WARN",
              "mixed: %s" % sorted(set(r["mtu"] for r in site_plan["subnets"] if r["mtu"])))
        out_sites[tag] = site_plan

    # ---- Global Manager side
    gm = {"vlan_segments": [], "sites": {}, "tz_pick": {}, "tier0": None}
    if gm_data:
        gsegs = _seg_map(gm_data)
        gm["vlan_segments"] = [v["name"] for v in gsegs.values() if v["kind"] == "VLAN"]
        c("gm-uplink", "Global Manager owns VLAN segments for uplinks",
          "PASS" if gm["vlan_segments"] else "FAIL",
          gm["vlan_segments"] or "none. A stretched Tier-0's external interfaces can only attach "
                                 "to segments the GM owns; Local Manager segments are not selectable "
                                 "from the GM. Create them on the GM first (runbook Phase 8).")
        gm["tz_pick"] = {}
        for sid, v in (gm_data.get("site_transport_zones") or {}).items():
            vlans = v.get("vlan") or []
            gm["sites"][sid] = [z["name"] for z in vlans]
            c("gm-uplink", "%s VLAN transport zones visible to the GM" % sid,
              "PASS" if vlans else "FAIL",
              gm["sites"][sid] or "none; uplink segments cannot be created on the GM for this site")
            # prefer an explicit override, else the TZ the site's own uplink segments use
            want = (cfg.get("fed_ns_uplink_tz_%s" % sid)
                    or (out_sites.get(sid) or {}).get("uplink_tz"))
            hit = next((z for z in vlans if z.get("name") == want), None)
            if hit is None and len(vlans) == 1:
                hit = vlans[0]
            if hit:
                gm["tz_pick"][sid] = hit
                c("gm-uplink", "%s uplink transport zone resolved on the GM" % sid, "PASS",
                  "%s" % hit.get("name"))
            elif want:
                c("gm-uplink", "%s uplink transport zone resolved on the GM" % sid, "DECIDE",
                  "the LM uses '%s'; the GM offers %s. Set fed_ns_uplink_tz_%s"
                  % (want, gm["sites"][sid], sid))
                decisions.append("%s: uplink transport zone as the GM names it "
                                 "(fed_ns_uplink_tz_%s)" % (sid, sid))
        for t0 in _res(_nb(gm_data, "tier0s")):
            if stretched and t0.get("display_name") != stretched:
                continue
            gm["tier0"] = t0.get("display_name")
            ls = (gm_data.get("locale_services") or {}).get(t0.get("path")) or []
            c("gm-uplink", "%s has a locale service per location" % t0.get("display_name"),
              "PASS" if len(ls) >= 2 else "FAIL", "%d locale service(s)" % len(ls))
    else:
        c("gm-uplink", "Global Manager read", "SKIP",
          "set nsx_gm_host / nsx_gm_password to assess the stretched Tier-0 side")
    return {"checks": ck, "sites": out_sites, "alloc": alloc, "neighbors": nbr_rows,
            "gm": gm, "decisions": decisions}


def fed_northsouth_runbook(cfg, up, ctx):
    """Phases 8-11: give the stretched Tier-0 uplinks and BGP so stretched segments
    reach the physical network. Same format as fed_runbook; <CONFIRM> marks unknowns."""
    tags = list(up["sites"])
    a = cfg.get("fed_gm_site") or (tags[0] if tags else "site-a")
    b = cfg.get("fed_gm_standby_site") or (tags[1] if len(tags) > 1 else "site-b")
    t0 = cfg.get("fed_ns_tier0_name") or "T0-STRETCHED-%s-%s" % (a.upper(), b.upper())
    t1 = cfg.get("fed_ns_tier1_name") or "T1-STRETCHED-01"
    seg = cfg.get("fed_ns_test_segment") or "seg-stretched-test"
    subnet = cfg.get("fed_ns_test_subnet") or "<CONFIRM: allocated by the customer>"
    as_ = cfg.get("fed_ns_local_as") or "<CONFIRM>"
    L = []
    A = L.append
    A("NSX FEDERATION -- NORTH-SOUTH RUNBOOK   generated %s" % now())
    A("Continues federation_runbook.txt. Phases 1-7 stretch layer 2 between %s and %s;" % (a, b))
    A("these phases give the stretched Tier-0 uplinks and BGP so those segments reach")
    A("the physical network. East-west works without any of this.")
    A("Anything marked <CONFIRM> was not available to this run and must be filled in before use.")
    A("")
    A("=" * 74); A(" 0. GATE  --  before Phase 8"); A("=" * 74)
    for line in ("Phases 1-7 complete: both locations SYNCED, RTEP up, DF-bit validation recorded",
                 "East-west proven: a VM at each site on the stretched segment pings the other",
                 "Uplink addresses in uplink_allocation.csv confirmed free on the leaves",
                 "Matching BGP neighbours added on the leaves",
                 "Test subnet %s is allocated to us -- it will be advertised into their fabric" % subnet,
                 "Route filters on the existing sessions permit the test subnet",
                 "Change window: adding a second Tier-0 peering touches the leaves"):
        A("  [ ] " + line)
    A("")
    A("=" * 74); A(" WHAT THIS RUN FOUND"); A("=" * 74)
    for t in tags:
        s = up["sites"][t]
        A("  %s" % t)
        A("    Local Manager       : %s" % (s.get("lm") or "<CONFIRM>"))
        A("    Reference Tier-0    : %s   local AS %s" % (s.get("reference_tier0"), s.get("local_as")))
        for r in s["subnets"]:
            A("    uplink %-18s segment %-24s vlan %-5s mtu %s"
              % (r["subnet"], r["segment"], r["vlan"], r["mtu"]))
            A("      in use : %s" % ", ".join(r["in_use"]))
            A("      peers  : %s   remote AS %s" % (", ".join(r["peers"]) or "<CONFIRM>",
                                                    ", ".join(str(x) for x in r["remote_as"]) or "<CONFIRM>"))
            A("      free   : %s" % (", ".join(r["free"]) or "NONE -- ask for a new range"))
        A("")
    gmseg = up["gm"].get("vlan_segments")
    A("=" * 74); A(" PHASE 8  --  uplink segments on the Global Manager"); A("=" * 74)
    A("  A stretched Tier-0's external interfaces can only attach to segments the GM owns.")
    A("  Local Manager segments do not appear in the GM picker.")
    A("  GM currently owns these VLAN segments: %s" % (", ".join(gmseg) if gmseg else "NONE"))
    A("")
    if not gmseg:
        A("  On the ACTIVE GM https://%s : Networking > Segments > ADD SEGMENT, once per site per uplink VLAN:"
          % (cfg.get("fed_gm_vip_fqdn") or "<CONFIRM>"))
        A("")
        A("    %-28s %-8s %-6s %-30s" % ("NAME", "TYPE", "VLAN", "TRANSPORT ZONE"))
        for t in tags:
            for r in up["sites"][t]["subnets"]:
                pk = (up["gm"].get("tz_pick") or {}).get(t)
                tzl = [pk["name"]] if pk else ((up["gm"].get("sites") or {}).get(t) or [])
                A("    %-28s %-8s %-6s %-30s"
                  % ("seg-uplink-%s-vlan%s" % (t, r["vlan"]), "VLAN", r["vlan"],
                     tzl[0] if len(tzl) == 1 else
                     ("<CONFIRM: one of %s>" % ", ".join(tzl) if tzl
                      else "<CONFIRM: %s VLAN transport zone as the GM sees it>" % t)))
        A("")
        A("    No subnet and no connected gateway -- these carry external interfaces only.")
    else:
        A("  Reuse the segments above if they match the uplink VLANs; otherwise create the missing ones.")
    A("")
    A("=" * 74); A(" PHASE 9  --  uplink interfaces on %s" % t0); A("=" * 74)
    A("  GM > Networking > Tier-0 Gateways > %s > EDIT > INTERFACES > Set > ADD INTERFACE." % t0)
    A("  Every row: Type External, ND Profile default, MTU and URPF as the reference Tier-0.")
    A("")
    A("  %-6s %-30s %-20s %-26s %-16s %-5s" % ("SITE", "NAME", "IP / MASK", "SEGMENT", "EDGE NODE", "MTU"))
    for t in tags:
        s = up["sites"][t]
        for r in s["subnets"]:
            nodes = r["nodes"] or ["<CONFIRM>"]
            for i, ip in enumerate(r["free"]):
                node = nodes[i] if i < len(nodes) else "<CONFIRM>"
                A("  %-6s %-30s %-20s %-26s %-16s %-5s"
                  % (t, "str-%s-%s-vlan%s" % (t, node.split(".")[0][-5:], r["vlan"]),
                     "%s/%s" % (ip, r["subnet"].split("/")[-1]),
                     ("seg-uplink-%s-vlan%s" % (t, r["vlan"])) if not gmseg else "<GM segment>",
                     node, r["mtu"] or "<CONFIRM>"))
    A("")
    A("  Set Location on each row to the matching site. SAVE.")
    A("  Every interface must show Success before Phase 10.")
    A("")
    A("=" * 74); A(" PHASE 10  --  BGP on %s" % t0); A("=" * 74)
    A("  GM > %s > BGP." % t0)
    A("  Local AS: %s   (one gateway spanning both sites presents one AS; there is no per-location override)" % as_)
    A("  Confirm remote-as %s is configured on the leaves at BOTH sites." % as_)
    A("")
    A("  BGP Neighbors > Set > ADD BGP NEIGHBOR:")
    A("")
    A("  %-6s %-18s %-10s %-8s %-6s %-14s %s" % ("SITE", "PEER", "REMOTE AS", "MAX HOP", "BFD", "GR", "SOURCE ADDRESSES"))
    for t in tags:
        for r in up["sites"][t]["subnets"]:
            ex = next((n for n in up["sites"][t]["neighbors"] if n["peer"] in r["peers"]), {})
            A("  %-6s %-18s %-10s %-8s %-6s %-14s %s"
              % (t, ", ".join(r["peers"]) or "<CONFIRM>",
                 ", ".join(str(x) for x in r["remote_as"]) or "<CONFIRM>",
                 ex.get("max_hop", 1), "Off" if not ex.get("bfd") else "On",
                 ex.get("graceful_restart") or "HELPER_ONLY",
                 ", ".join(r["free"]) or "<CONFIRM>"))
            if ex.get("password_set"):
                A("         ^ the reference session uses a BGP PASSWORD; the API will not return it.")
                A("           Take the value from the leaf configuration before creating this neighbour.")
    A("")
    A("  Match the reference sessions: Allowas-in No, Local AS not overridden, timers as found above.")
    A("  SAVE.")
    A("")
    A("  ROUTE FILTERS. The reference Tier-0s carry an NSX-side outbound prefix list. The")
    A("  neighbours created here have NONE, so they advertise every prefix the Tier-0 knows.")
    A("  Decide before Phase 11:")
    A("    (a) leave unfiltered  -- simplest; the stretched segment is advertised, so is anything")
    A("        else later attached to this Tier-0, and")
    A("    (b) mirror the reference list with %s added -- matches the existing design."
      % (cfg.get("fed_ns_test_subnet") or "the stretched subnet"))
    A("  See readiness/uplink checks for the exact contents of the reference lists.")
    A("")
    A("=" * 74); A(" PHASE 11  --  verify north-south and hand over"); A("=" * 74)
    A("  1. GM > %s > BGP > Neighbors: every session Success." % t0)
    A("  2. On an edge at each site:  get gateways ; get bgp neighbor summary")
    A("       sessions established, and %s present in what is advertised." % subnet)
    A("  3. From a VM on %s at %s:" % (seg, a))
    A("       ping <its gateway>            # distributed router, always works")
    A("       ping <the VM at %s>           # east-west, proven in Phase 6" % b)
    A("       ping <an address off-overlay> # north-south -- this is the finish line")
    A("     Repeat from the %s VM." % b)
    A("  4. Start a continuous north-south ping. On the GM, swap %s primary from %s to %s and SAVE." % (t1, a, b))
    A("     The ping keeps running and the VM keeps its address. Swap back.")
    A("  5. Record every result with timestamps; the DF-bit and failover output is the deliverable.")
    A("")
    A("  Clean up: delete the test VMs, then %s. Keep %s and %s if production moves onto them." % (seg, t0, t1))
    A("")
    A("=" * 74); A(" ROLLBACK"); A("=" * 74)
    A("  Delete the BGP neighbours on %s, then its interfaces, then the GM uplink segments." % t0)
    A("  The reference Tier-0s and their sessions are untouched throughout; east-west survives.")
    return "\n".join(L)


# ---------------------------------------------------------------- edge datapath verification
RX_GW = re.compile(
    r"^([0-9a-f]{8}-[0-9a-f-]+|[0-9]{8}-[0-9a-f-]+)\s+(\d+)\s+(\d+)\s+(.*?)\s+"
    r"(TUNNEL|DISTRIBUTED_ROUTER_TIER[01]|SERVICE_ROUTER_TIER[01]|"
    r"VRF_DISTRIBUTED_ROUTER_TIER0|VRF_SERVICE_ROUTER_TIER0|RTEP_TUNNEL)\s+(\d+)\s+(\S+)",
    re.M)
RX_RTEP_IP = re.compile(r"(?:Local\s+RTEP\s+IP|RTEP\s+IP)\s*:?\s*"
                        r"(\d{1,3}(?:\.\d{1,3}){3})", re.I)
RX_ANY_IP = re.compile(r"\b(\d{1,3}(?:\.\d{1,3}){3})\b")


def parse_gateways(text):
    """`get gateways` (or the deprecated `get logical-routers`) -> list of dicts.
    Handles names containing spaces, e.g. 'DR-VRF-Default Transit Gateway'."""
    out = []
    for m in RX_GW.finditer(text or ""):
        out.append({"uuid": m.group(1), "vrf": int(m.group(2)), "gw_id": int(m.group(3)),
                    "name": m.group(4).strip(), "type": m.group(5),
                    "ports": int(m.group(6)), "neighbors": m.group(7)})
    return out


def parse_rteps(text):
    ips = RX_RTEP_IP.findall(text or "")
    return ips or ([] if "not configured" in str(text).lower() else RX_ANY_IP.findall(text or ""))


RX_BGP_LOCAL_AS = re.compile(r"Local\s+AS\s*:\s*(\d+)", re.I)
RX_BGP_ROW = re.compile(
    r"^\s*(\d{1,3}(?:\.\d{1,3}){3})\s+(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+"
    r"(\d+)\s+(\d+)\s+(\d+)\s+(\d+)", re.M)


def parse_bgp_summary(text):
    """`get bgp neighbor summary` inside a Tier-0 SR VRF.

    This is the only place BGP state can actually be read on 9.1 -- the policy
    status endpoint 404s, which is why no session was ever machine-verified."""
    t = text or ""
    m = RX_BGP_LOCAL_AS.search(t)
    rows = []
    for r in RX_BGP_ROW.finditer(t):
        rows.append({"peer": r.group(1), "remote_as": int(r.group(2)), "state": r.group(3),
                     "uptime": r.group(4), "bfd": r.group(5),
                     "in_msgs": int(r.group(6)), "out_msgs": int(r.group(7)),
                     "in_prefixes": int(r.group(8)), "out_prefixes": int(r.group(9))})
    return {"local_as": int(m.group(1)) if m else None, "neighbors": rows}


def fed_ns_verify_edges(cfg, sites, out=None, user="admin", pw_for_site=None):
    """SSH each edge node in the stretched Tier-0's cluster and compare the DATAPATH with
    what the Local Manager reports. This is the check that distinguishes 'the manager thinks
    it pushed it' from 'the edge actually has it'. Read-only: `get rteps`, `get gateways`.

    Stops at a site after one auth failure so no account is locked out."""
    t0 = cfg.get("fed_ns_tier0_name") or "T0-STRETCHED"
    t1 = cfg.get("fed_ns_tier1_name") or ""
    results, checks = {}, []

    def c(item, state, detail=""):
        checks.append({"area": "edge-datapath", "item": item, "state": state,
                       "detail": str(detail)[:300]})

    for tag, sd in sites.items():
        d = sd.get("data") or {}
        ec = (cfg.get("fed_edge_clusters_%s" % tag) or [None])[0]
        nodes = fed_edge_nodes(d, [ec] if ec else None)
        if not nodes:
            c("%s edge nodes discoverable" % tag, "SKIP", "no members for cluster %s" % ec)
            continue
        pw = pw_for_site(tag) if pw_for_site else None
        if not pw:
            c("%s edge SSH" % tag, "SKIP", "no edge password supplied for %s" % tag)
            continue
        stop = False
        for n in nodes:
            target = n.get("fqdn") or n.get("name")
            if stop:
                c("%s %s datapath" % (tag, n["name"]), "SKIP",
                  "skipped after an auth failure at this site")
                continue
            if DRY:
                PLAN.append("SSH  %s@%s  get rteps ; get gateways" % (user, target))
                continue
            log("   %s %s (%d of %d)" % (tag, n["name"], nodes.index(n) + 1, len(nodes)))
            ok, o = ssh_exec(target, user, pw, "get rteps", timeout=25)
            if not ok:
                if is_auth_failure(o):
                    stop = True
                    c("%s %s SSH" % (tag, n["name"]), "FAIL",
                      "authentication failed; not retrying other nodes at this site")
                else:
                    c("%s %s SSH" % (tag, n["name"]), "SKIP", str(o)[:120])
                continue
            rt_ips = parse_rteps(o)
            ok2, g = ssh_exec(target, user, pw, "get gateways", timeout=25)
            if not ok2 or "Gateway" not in g:
                ok2, g = ssh_exec(target, user, pw, "get logical-routers", timeout=25)
            gws = parse_gateways(g)
            names = [x["name"] for x in gws]
            results[n["name"]] = {"site": tag, "rtep_ips": rt_ips, "gateways": gws}

            # 1. RTEP present on the datapath, and matching the LM's view
            api_ips = n.get("rtep_ips") or []
            if not rt_ips:
                c("%s %s RTEP on the datapath" % (tag, n["name"]), "FAIL",
                  "edge reports no remote tunnel endpoint")
            elif api_ips and sorted(api_ips) != sorted(rt_ips):
                c("%s %s RTEP matches the Local Manager" % (tag, n["name"]), "FAIL",
                  "edge %s, manager %s" % (rt_ips, api_ips))
            else:
                c("%s %s RTEP on the datapath" % (tag, n["name"]), "PASS", ", ".join(rt_ips))

            # 2. the check that matters: is the stretched Tier-0 actually instantiated?
            dr = any(x == "DR-" + t0 for x in names)
            sr = any(x == "SR-" + t0 for x in names)
            # VCF 9.1 allows ONE Tier-0 gateway per edge node. If another Tier-0
            # already has a service router here, this one never will, and every
            # external interface on it fails to realize with an error that says
            # nothing. Name the incumbent -- that is the whole diagnosis.
            incumbent = sorted(set(
                x["name"][3:] for x in gws
                if x.get("type") == "SERVICE_ROUTER_TIER0"
                and x.get("name", "").startswith("SR-")
                and x["name"][3:] != t0))
            if dr and sr:
                c("%s %s hosts %s" % (tag, n["name"], t0), "PASS", "DR and SR present")
            elif incumbent:
                c("%s %s hosts %s" % (tag, n["name"], t0), "FAIL",
                  "SR MISSING and this edge already backs Tier-0 %s. VCF 9.1 allows one "
                  "Tier-0 per edge node, so %s cannot instantiate a service router here "
                  "no matter what the manager reports. It needs its own edge cluster."
                  % (", ".join(incumbent), t0))
            elif dr:
                c("%s %s hosts %s" % (tag, n["name"], t0), "FAIL",
                  "DR present, SR MISSING -- the Tier-0 has no service router on this edge, "
                  "so no external interface can realize")
            else:
                c("%s %s hosts %s" % (tag, n["name"], t0), "FAIL",
                  "neither DR nor SR present -- the Tier-0 was never instantiated here")
            # 3. BGP, read where it is true: inside the Tier-0 SR's VRF on the edge
            sr_vrf = next((g.get("vrf") for g in gws
                           if g.get("type") == "SERVICE_ROUTER_TIER0"
                           and g.get("name") == "SR-" + t0), None)
            if sr_vrf is not None and not cfg.get("_no_edge_bgp"):
                log("     vrf %d: get bgp neighbor summary" % sr_vrf)
                try:
                    okb, bout = ssh_exec(target, user, pw, "",
                                         stdin_data="vrf %d\nget bgp neighbor summary\nexit\n" % sr_vrf,
                                         timeout=20, tty=True)
                except Exception as e:
                    okb, bout = False, str(e)
                bsum = parse_bgp_summary(bout if okb else "")
                if not bsum.get("neighbors"):
                    c("%s %s BGP read" % (tag, n["name"]), "SKIP",
                      "no summary returned over SSH; read it by hand with 'vrf %d' then "
                      "'get bgp neighbor summary', or re-run with --no-edge-bgp to skip"
                      % sr_vrf)
                results[n["name"]]["bgp"] = bsum
                want_as = str(cfg.get("fed_ns_local_as") or "").strip()
                if bsum.get("local_as") and want_as and str(bsum["local_as"]) != want_as:
                    c("%s %s local AS" % (tag, n["name"]), "FAIL",
                      "edge reports AS %s, config fed_ns_local_as says %s -- one of them is "
                      "wrong, and the switch requirements follow "
                      "the config" % (bsum["local_as"], want_as))
                elif bsum.get("local_as"):
                    c("%s %s local AS" % (tag, n["name"]), "PASS", bsum["local_as"])
                nb = bsum.get("neighbors") or []
                up = [x for x in nb if str(x["state"]).upper().startswith("ESTAB")]
                if not nb:
                    c("%s %s BGP sessions" % (tag, n["name"]), "WARN",
                      "no neighbours parsed from the edge" if okb else "could not read BGP")
                elif len(up) == len(nb):
                    c("%s %s BGP sessions" % (tag, n["name"]), "PASS",
                      ", ".join("%s AS%s %s in=%d out=%d"
                                % (x["peer"], x["remote_as"], x["uptime"],
                                   x["in_prefixes"], x["out_prefixes"]) for x in nb))
                else:
                    c("%s %s BGP sessions" % (tag, n["name"]), "FAIL",
                      "%d of %d established: %s" % (len(up), len(nb),
                       ", ".join("%s=%s" % (x["peer"], x["state"]) for x in nb)))
                silent = [x for x in up if x["out_prefixes"] == 0]
                if silent:
                    c("%s %s prefixes advertised" % (tag, n["name"]), "FAIL",
                      "established but advertising nothing to %s -- check route "
                      "re-distribution at this location"
                      % ", ".join(x["peer"] for x in silent))
            if t1:
                c("%s %s hosts %s" % (tag, n["name"], t1),
                  "PASS" if any(x.endswith(t1) for x in names) else "WARN",
                  ", ".join(x for x in names if x.endswith(t1)) or "not present")
            c("%s %s gateway inventory" % (tag, n["name"]), "INFO",
              ", ".join(names) or "empty")
    if out is not None and not DRY:
        write_json(out, "edge_datapath", {"nodes": results, "checks": checks})
    return checks, results


# ---------------------------------------------------------------- north-south pre-flight
# Broadcom, "Configure Edge Nodes for Stretched Networking" (VCF 9.x Advanced Network
# Management): "When you configure an RTEP, do it on an Edge cluster basis. All Edge nodes
# in the cluster must have an RTEP configured. RTEPs are required only if the Edge cluster
# is used to configure a gateway that spans more than one location."
#
# Nothing on the stretched Tier-0 realizes on an edge cluster whose members are not all
# RTEP-configured, so this is asserted BEFORE any interface is written.

def fed_ns_preflight(cfg, up, sites, gm_data=None, host=None, user=None, pw=None):
    """Validate the prerequisites a stretched Tier-0 needs at each location.
    Returns (checks, blockers, rtep_gaps). Read-only."""
    ck, blockers, gaps = [], [], []

    def c(area, item, state, detail=""):
        ck.append({"area": area, "item": item, "state": state, "detail": str(detail)[:300]})

    t0 = cfg.get("fed_ns_tier0_name") or "T0-STRETCHED"
    H = None
    if host and user is not None:
        H = {"Authorization": "Basic " + base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()}

    for tag, sd in sites.items():
        d = sd.get("data") or {}
        # which edge cluster does the stretched Tier-0 use at this location?
        ec_name = (cfg.get("fed_edge_clusters_%s" % tag) or [None])[0]
        if H and not ec_name:
            st, ls = gm_get(host, H, "/tier-0s/%s/locale-services/%s" % (t0, tag))
            if isinstance(ls, dict):
                ec_name = None
                ecp = ls.get("edge_cluster_path") or ""
                # resolve the cluster id to a name via the LM inventory
                ecid = str(ecp).rsplit("/", 1)[-1]
                for e in _res(_nb(d, "edge_clusters")):
                    if e.get("id") == ecid:
                        ec_name = e.get("display_name")
        if not ec_name:
            c("preflight", "%s edge cluster for %s resolved" % (tag, t0), "SKIP",
              "set fed_edge_clusters_%s or make the locale service readable" % tag)
            continue
        c("preflight", "%s edge cluster for %s" % (tag, t0), "PASS", ec_name)

        tnb = (d.get("transport_nodes") or {}).get("body")
        if isinstance(tnb, dict) and tnb.get("cursor"):
            c("preflight", "%s transport-node list complete" % tag, "WARN",
              "the Local Manager paginated the node list; some nodes may not have been read")
        nodes = fed_edge_nodes(d, [ec_name])
        if not nodes:
            c("preflight", "%s edge cluster %s has members" % (tag, ec_name), "FAIL",
              "no members returned from the Local Manager")
            blockers.append("%s: edge cluster %s has no readable members" % (tag, ec_name))
            continue

        with_rtep = [n for n in nodes if n.get("rtep")]
        without = [n for n in nodes if not n.get("rtep")]
        state = "PASS" if not without else "FAIL"
        c("preflight", "%s RTEP on every node of %s" % (tag, ec_name), state,
          "%d of %d configured%s" % (len(with_rtep), len(nodes),
                                     ("; missing: " + ", ".join(n["name"] for n in without))
                                     if without else ""))
        for n in nodes:
            if not n.get("rtep"):
                continue
            ips = n.get("rtep_ips") or []
            cidr = cfg.get("fed_rtep_cidr_%s" % tag)
            want_vlan = cfg.get("fed_rtep_vlan_%s" % tag)
            det = "%s vlan %s" % (", ".join(ips) or
                                  "configured; address not exposed by the API, "
                                  "confirmed from the datapath with --verify-edges",
                                  n.get("rtep_vlan"))
            state = "PASS"
            if cidr and ips:
                try:
                    net = ipaddress.ip_network(str(cidr), strict=False)
                    if not all(ipaddress.ip_address(x) in net for x in ips):
                        state, det = "FAIL", det + " -- outside %s" % cidr
                except Exception:
                    pass
            if want_vlan and n.get("rtep_vlan") and str(n["rtep_vlan"]) != str(want_vlan):
                state, det = "FAIL", det + " -- expected vlan %s" % want_vlan
            c("preflight", "%s %s RTEP" % (tag, n["name"]), state, det)
        if without:
            blockers.append(
                "%s: RTEP missing on %s. Broadcom requires an RTEP on EVERY node of an edge "
                "cluster that hosts a gateway spanning more than one location; nothing on the "
                "stretched Tier-0 will realize until this is fixed."
                % (tag, ", ".join(n["name"] for n in without)))
            gaps.append({"site": tag, "cluster": ec_name, "lm": sd.get("fqdn"),
                         "nodes": [{"name": n["name"], "id": n["node_id"]} for n in without],
                         "vlan": cfg.get("fed_rtep_vlan_%s" % tag),
                         "pool": cfg.get("fed_rtep_pool_%s" % tag) or ("rtep-pool-%s" % tag),
                         "mtu": int(cfg.get("fed_rtep_mtu") or 1700)})

    # uRPF: all-primary active-active is an asymmetric-routing topology, and Broadcom
    # requires uRPF deactivated on external interfaces when routing is asymmetric.
    want_urpf = (cfg.get("fed_ns_urpf") or "NONE").upper()
    modes = []
    if gm_data:
        for gw in _res(_nb(gm_data, "tier0s")):
            if gw.get("display_name") != t0:
                continue
            for l in (gm_data.get("locale_services") or {}).get(gw.get("path")) or []:
                modes.append(l.get("id"))
            ha = str(gw.get("ha_mode") or "").upper()
            if ha == "ACTIVE_ACTIVE" and want_urpf != "NONE":
                c("preflight", "%s uRPF suits an all-primary Tier-0" % t0, "WARN",
                  "ha_mode=ACTIVE_ACTIVE with fed_ns_urpf=%s. Broadcom: deactivate uRPF on "
                  "all external Tier-0 interfaces when routing is asymmetric." % want_urpf)
            elif ha == "ACTIVE_ACTIVE":
                # This reads the DESIGN value from config. What is on the interfaces
                # can differ, and on this environment it did -- every interface came
                # back STRICT while the config said NONE. Check reality too.
                _real = sorted(set(str(u.get("urpf") or "?").upper()
                                   for u in (gm_data.get("gm_uplinks") or [])
                                   if u.get("tier0") == t0))
                _allprim = not (gw.get("intersite_config") or {}).get("primary_site_path")
                _sym = str(cfg.get("fed_ns_urpf_symmetry_assured") or "").lower() in ("1", "true", "yes")
                if _real and _real != [want_urpf]:
                    c("preflight", "%s uRPF on the interfaces" % t0, "FAIL",
                      "design says %s, built interfaces are %s -- one of the two is wrong"
                      % (want_urpf, ", ".join(_real)))
                elif _real == ["STRICT"] and _allprim and _sym:
                    c("preflight", "%s uRPF on the interfaces" % t0, "PASS",
                      "STRICT on an all-primary Tier-0. Valid while return traffic enters "
                      "the location it left; each location advertises its own prefixes only. "
                      "Re-check after any Tier-1 failover -- if both locations advertise the "
                      "same prefix, ingress can land at the wrong site and STRICT drops it.")
                elif _real == ["STRICT"] and _allprim:
                    c("preflight", "%s uRPF on the interfaces" % t0, "WARN",
                      "STRICT with fed_ns_urpf_symmetry_assured unset. All-primary requires "
                      "return traffic to enter the location it left; if that is not assured "
                      "(both sites advertising a prefix, no AS-path prepend or location NAT) "
                      "uRPF must be NONE.")
                elif _real == ["STRICT"]:
                    c("preflight", "%s uRPF on the interfaces" % t0, "WARN",
                      "STRICT on a primary/secondary Tier-0. Documentation: if you choose "
                      "asymmetric routing, deactivate uRPF on all external interfaces.")
                else:
                    c("preflight", "%s uRPF on the interfaces" % t0, "PASS",
                      ", ".join(_real) or "design %s, no interfaces to check" % want_urpf)
    return ck, blockers, gaps


def fed_ns_fix_rtep(gaps, cfg, user, pw, commit=False):
    """Configure RTEP on edge nodes that lack it, per Broadcom's cluster-wide requirement.
    Writes to the LOCAL MANAGER, not the GM, and only with commit=True. Idempotent: a node
    that already has an RTEP is skipped."""
    out = []
    for g in gaps:
        lm, vlan, pool = g["lm"], g.get("vlan"), g.get("pool")
        H = {"Authorization": "Basic " + base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()}
        if not (vlan and pool):
            for n in g["nodes"]:
                out.append(dict(n, site=g["site"], action="BLOCKED",
                                detail="need fed_rtep_vlan_%s and an RTEP IP pool" % g["site"]))
            continue
        # resolve the pool id once
        st, pools = http("https://%s/policy/api/v1/infra/ip-pools" % lm, headers=H, timeout=40)
        pid = next((p.get("id") for p in _res(pools)
                    if (p.get("display_name") or p.get("id")) == pool), None)
        if not pid:
            for n in g["nodes"]:
                out.append(dict(n, site=g["site"], action="BLOCKED",
                                detail="IP pool '%s' not found on %s" % (pool, lm)))
            continue
        for n in g["nodes"]:
            st, tn = http("https://%s/api/v1/transport-nodes/%s" % (lm, n["id"]), headers=H, timeout=40)
            if not isinstance(tn, dict) or st != 200:
                out.append(dict(n, site=g["site"], action="ERROR",
                                detail="could not read transport node (HTTP %s)" % st))
                continue
            if tn.get("remote_tunnel_endpoint"):
                out.append(dict(n, site=g["site"], action="UNCHANGED", detail="RTEP already set"))
                continue
            hs = ((tn.get("host_switch_spec") or {}).get("host_switches") or [{}])[0]
            body = dict(tn)
            body["remote_tunnel_endpoint"] = {
                "host_switch_name": hs.get("host_switch_name"),
                "rtep_vlan": {"vlan_id": int(vlan)},
                "ip_assignment_spec": {"resource_type": "StaticIpPoolSpec", "ip_pool_id": pid}}
            if not commit:
                out.append(dict(n, site=g["site"], action="ADD",
                                detail="vlan %s pool %s switch %s"
                                       % (vlan, pool, hs.get("host_switch_name"))))
                continue
            st2, b2 = http("https://%s/api/v1/transport-nodes/%s" % (lm, n["id"]),
                           method="PUT", headers=H, body=body, timeout=120)
            out.append(dict(n, site=g["site"],
                            action="ADD" if st2 in (200, 201, 202) else "ERROR",
                            detail="HTTP %s%s" % (st2, "" if st2 in (200, 201, 202)
                                                  else " " + str(b2)[:160])))
    return out


# ---------------------------------------------------------------- north-south: declarative apply
# The NSX Policy API is intent-based: PATCH to a deterministic path with a stable id is
# idempotent by construction. Every object below gets an id derived from the intent, so
# re-running converges instead of duplicating. `run` never writes; only `fedapply --commit` does.

def ns_id(*parts):
    """Deterministic, API-safe object id from intent."""
    return SAFE.sub("-", "-".join(str(p) for p in parts if p is not None)).strip("-").lower()


def gm_get(host, H, sub, timeout=40):
    st, b = http("https://%s/global-manager/api/v1/global-infra%s" % (host, sub), headers=H, timeout=timeout)
    return st, b


def gm_patch(host, H, sub, body, timeout=60):
    return http("https://%s/global-manager/api/v1/global-infra%s" % (host, sub),
                method="PATCH", headers=H, body=body, timeout=timeout)


def _same(desired, live, keys):
    """True if every key in `desired` already matches `live`."""
    for k in keys:
        d, l = desired.get(k), (live or {}).get(k)
        if isinstance(d, list) and isinstance(l, list):
            if [str(x) for x in d] != [str(x) for x in l]:
                return False
        elif str(d) != str(l):
            return False
    return True


def fed_ns_desired(cfg, up):
    """Compute the full desired state for the stretched Tier-0's north-south configuration.
    Pure function: no network calls. Returns a list of objects, each with a stable id."""
    tags = list(up["sites"])
    t0 = cfg.get("fed_ns_tier0_name") or "T0-STRETCHED"
    local_as = str(cfg.get("fed_ns_local_as") or "").strip()
    objs = []
    for tag in tags:
        s = up["sites"][tag]
        tzs = (up["gm"].get("sites") or {}).get(tag) or []
        pick = (up["gm"].get("tz_pick") or {}).get(tag)
        for r in s["subnets"]:
            vlan = r["vlan"]
            # override wins, else whatever the reference segment uses (often nothing)
            _tm = (cfg.get("fed_ns_teaming_%s_vlan%s" % (tag, vlan))
                   or cfg.get("fed_ns_teaming_%s" % tag) or r.get("teaming"))
            seg_id = ns_id("seg-uplink", tag, "vlan%s" % vlan)
            objs.append({"kind": "segment", "site": tag, "id": seg_id,
                         "path": "/segments/%s" % seg_id,
                         "body": dict({"display_name": seg_id, "vlan_ids": [str(vlan)],
                                       "transport_zone_path": (pick or {}).get("path")},
                                      **({"advanced_config":
                                          {"uplink_teaming_policy_name": _tm}}
                                         if _tm else {})),
                         "compare": ["display_name", "vlan_ids"],
                         "needs": None if pick else
                                  "transport_zone_path: %s VLAN transport zone -- %d candidates "
                                  "on the GM (%s). Set fed_ns_uplink_tz_%s to the right one."
                                  % (tag, len(tzs), ", ".join(tzs[:4]), tag)})
            nodes = r["nodes"] or []
            for i, ip in enumerate(r["free"]):
                node = nodes[i] if i < len(nodes) else None
                if_id = ns_id("uplink", tag, node or "edge%d" % (i + 1), "vlan%s" % vlan)
                objs.append({"kind": "interface", "site": tag, "id": if_id,
                             "path": "/tier-0s/%s/locale-services/%s/interfaces/%s" % (t0, tag, if_id),
                             "body": {"display_name": if_id, "type": "EXTERNAL",
                                      "segment_path": "/global-infra/segments/%s" % seg_id,
                                      "subnets": [{"ip_addresses": [ip],
                                                   "prefix_len": int(str(r["subnet"]).split("/")[-1])}],
                                      "mtu": r["mtu"],
                                      "urpf_mode": (cfg.get("fed_ns_urpf")
                                                    or (r["urpf"] or ["NONE"])[0]).upper(),
                                      "edge_path": None},
                             "compare": ["display_name", "type", "segment_path", "mtu"],
                             "edge_node": node,
                             "needs": None if node else "edge node for %s in %s" % (ip, tag)})
            for peer in r["peers"]:
                ex = next((n for n in s["neighbors"] if n.get("peer") == peer), {})
                nb_id = ns_id("nbr", tag, peer)
                objs.append({"kind": "neighbor", "site": tag, "id": nb_id,
                             "path": "/tier-0s/%s/locale-services/%s/bgp/neighbors/%s" % (t0, tag, nb_id),
                             "body": {"display_name": nb_id, "neighbor_address": peer,
                                      "remote_as_num": str((r["remote_as"] or [""])[0]),
                                      "source_addresses": list(r["free"]),
                                      "maximum_hop_limit": ex.get("max_hop") or 1,
                                      "graceful_restart_mode": ex.get("graceful_restart") or "HELPER_ONLY",
                                      "hold_down_time": ex.get("hold_down") or 180,
                                      "keep_alive_time": ex.get("keepalive") or 60,
                                      "allow_as_in": bool(ex.get("allow_as_in"))},
                             "compare": ["neighbor_address", "remote_as_num", "source_addresses",
                                         "maximum_hop_limit"],
                             "needs": ("BGP password for %s (the API does not return it)" % peer)
                                      if ex.get("password_set") else None})
        if local_as:
            objs.append({"kind": "bgp", "site": tag, "id": "bgp",
                         "path": "/tier-0s/%s/locale-services/%s/bgp" % (t0, tag),
                         "body": {"local_as_num": local_as, "enabled": True},
                         "compare": ["local_as_num", "enabled"], "needs": None})
    return objs


def fed_ns_apply(cfg, up, host, user, pw, commit=False, outdir=None):
    """Diff desired against live on the Global Manager. Reports ADD / UPDATE / UNCHANGED /
    BLOCKED for every object. Writes only when commit=True. Safe to re-run."""
    H = {"Authorization": "Basic " + base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()}
    t0 = cfg.get("fed_ns_tier0_name") or "T0-STRETCHED"
    desired = fed_ns_desired(cfg, up)

    # Resolve each site tag to the Tier-0's actual locale-service id. The GM names a
    # locale service after its location, but the config tag is ours -- match rather than
    # assume, and say what is available when it does not line up.
    st, allls = gm_get(host, H, "/tier-0s/%s/locale-services" % t0)
    have = {}
    for l in _res(allls):
        lid = l.get("id")
        have[str(lid).lower()] = (lid, l)
        dn = l.get("display_name")
        if dn:
            have[str(dn).lower()] = (lid, l)
    locale_of, unresolved = {}, []
    for tag in up["sites"]:
        hit = have.get(str(tag).lower())
        if hit:
            locale_of[tag] = hit
        else:
            unresolved.append(tag)
    if unresolved and st != 200:
        log("  ! %s has no locale services on %s (HTTP %s)" % (t0, host, st))
    elif unresolved:
        log("  ! site tag(s) %s do not match any locale service on %s."
            % (", ".join(unresolved), t0))
        log("    %s has: %s" % (t0, ", ".join(sorted(set(v[0] for v in have.values())))))
        log("    Rename the nsx_lm_host_<tag> keys to match, or add the location to the Tier-0.")

    # resolve edge nodes per location, so interfaces can be bound to a node
    edge_paths = {}
    for tag, (lid, ls) in locale_of.items():
        ecp = (ls or {}).get("edge_cluster_path")
        if not ecp:
            log("  ! locale service %s on %s has no edge cluster" % (lid, t0))
            continue
        st, en = gm_get(host, H, "%s/edge-nodes" % ecp.replace("/global-infra", "", 1))
        for n in _res(en):
            nm = (n.get("display_name") or "").lower()
            edge_paths.setdefault(tag, {})[nm] = n.get("path")
        if not edge_paths.get(tag):
            log("  ! no edge nodes returned for %s (edge cluster %s)"
                % (tag, str(ecp).rsplit("/", 1)[-1]))

    results, blocked = [], 0
    for o in desired:
        if o["kind"] in ("interface", "neighbor", "bgp"):
            hit = locale_of.get(o["site"])
            if not hit:
                results.append({"kind": o["kind"], "site": o["site"], "id": o["id"],
                                "path": o["path"], "action": "BLOCKED",
                                "detail": "no locale service on %s for site '%s'; available: %s"
                                          % (t0, o["site"],
                                             ", ".join(sorted(set(v[0] for v in have.values()))) or "none")})
                blocked += 1
                continue
            o["path"] = o["path"].replace("/locale-services/%s/" % o["site"],
                                          "/locale-services/%s/" % hit[0])
            if o["path"].endswith("/locale-services/%s" % o["site"]):
                o["path"] = o["path"][: -len(o["site"])] + hit[0]
        row = {"kind": o["kind"], "site": o["site"], "id": o["id"], "path": o["path"],
               "action": None, "detail": ""}
        if o["kind"] == "interface":
            node = (o.get("edge_node") or "").lower()
            ep = (edge_paths.get(o["site"]) or {}).get(node)
            if not ep:
                ep = next((v for k, v in (edge_paths.get(o["site"]) or {}).items()
                           if node and node.split(".")[0] == k.split(".")[0]), None)
            if ep:
                o["body"]["edge_path"] = ep
            else:
                o["needs"] = o.get("needs") or "edge node path for %s on the GM" % (node or "?")
        missing = [k for k, v in o["body"].items() if v is None]
        if o.get("needs") or missing:
            row["action"] = "BLOCKED"
            row["detail"] = o.get("needs") or "unresolved: %s" % ", ".join(missing)
            blocked += 1
            results.append(row)
            continue
        st, live = gm_get(host, H, o["path"])
        if st == 200 and isinstance(live, dict) and _same(o["body"], live, o["compare"]):
            row["action"] = "UNCHANGED"
        elif st == 200:
            row["action"] = "UPDATE"
            row["detail"] = "differs on %s" % ", ".join(
                k for k in o["compare"] if str(o["body"].get(k)) != str(live.get(k)))
        else:
            row["action"] = "ADD"
        if commit and row["action"] in ("ADD", "UPDATE"):
            st2, b2 = gm_patch(host, H, o["path"], o["body"])
            row["http"] = st2
            if st2 not in (200, 201, 202, 204):
                row["action"] = "ERROR"
                row["detail"] = str(b2)[:200]
        results.append(row)

    order = ["segment", "bgp", "interface", "neighbor"]
    results.sort(key=lambda r: (order.index(r["kind"]) if r["kind"] in order else 9, r["site"], r["id"]))
    if outdir:
        write_json(outdir, "northsouth_apply", {"commit": commit, "tier0": t0, "results": results})
    return results, blocked


def fed_switch_spec(cfg, up):
    """The only thing that must happen outside NSX: the leaves must accept BGP from the new
    uplink addresses. Written as a spec, not as commands to run interactively."""
    tags = list(up["sites"])
    local_as = cfg.get("fed_ns_local_as") or "<CONFIRM>"
    t0 = cfg.get("fed_ns_tier0_name") or "T0-STRETCHED"
    L = []
    A = L.append
    A("SWITCH REQUIREMENTS   generated %s" % now())
    A("For %s. This is the complete list of physical-fabric changes." % t0)
    A("")
    A("NOT required: new VLANs, new SVIs, new subnets, trunk changes, MTU changes,")
    A("routing-policy changes. The uplink VLANs already exist and are already trunked to")
    A("the edge hosts, the leaf SVIs already exist, and every new address below sits")
    A("inside a subnet the leaf already owns.")
    A("")
    A("Required: accept BGP from the new addresses. One neighbour statement each.")
    A("")
    total = 0
    for tag in tags:
        s = up["sites"][tag]
        A("=" * 74)
        A(" %s" % tag)
        A("=" * 74)
        for r in s["subnets"]:
            peer = ", ".join(r["peers"]) or "<CONFIRM>"
            ras = ", ".join(str(x) for x in r["remote_as"]) or "<CONFIRM>"
            A("  VLAN %-5s  subnet %-20s  leaf address %s  (leaf AS %s)" % (r["vlan"], r["subnet"], peer, ras))
            A("    the leaf that owns %s must add these neighbours, all remote-as %s:" % (peer, local_as))
            for ip in r["free"]:
                A("      %s" % ip)
                total += 1
            ex = next((n for n in s["neighbors"] if n.get("peer") in r["peers"]), {})
            A("    match the existing session on this SVI: BFD %s, max-hop %s, %s"
              % ("on" if ex.get("bfd") else "off", ex.get("max_hop") or 1,
                 ex.get("graceful_restart") or "graceful-restart helper"))
            if ex.get("password_set"):
                A("    the existing session uses a BGP PASSWORD -- the new neighbours need the same value")
            for f in ex.get("filters") or []:
                side = ("NSX advertises OUT to you" if f.startswith("out_route_filters")
                        else "NSX accepts IN from you")
                A("    for reference, an NSX-SIDE filter on the existing session (%s):" % side)
                A("      %s" % f)
            A("    NOTE: the filters above are configured in NSX, not on your switch. If you")
            A("    apply your own inbound policy to these sessions, confirm it permits %s."
              % (cfg.get("fed_ns_test_subnet") or "the stretched segment subnet"))
            A("")
    A("=" * 74)
    A(" TOTAL: %d neighbour statements" % total)
    A("=" * 74)
    A("")
    A(" The stretched Tier-0 uses AS %s at BOTH sites. It is one gateway spanning two" % local_as)
    A(" locations and NSX has no per-location AS override, so the same remote-as appears")
    A(" on the leaves at each site. If a leaf would then receive its own AS back through")
    A(" the other site, allowas-in or a multipath setting may be needed -- check the")
    A(" existing edge sessions, which already face the same topology.")
    A("")
    A(" Also confirm: %s is allocated to us, and that whatever inbound route policy you"
      % (cfg.get("fed_ns_test_subnet") or "<the stretched segment subnet>"))
    A(" apply to these new sessions accepts it. It is advertised as soon as BGP establishes.")
    A("")
    A(" FRR / Cumulus shape, per leaf (adapt to the existing peer-group if one is in use):")
    A("")
    for tag in tags:
        for r in up["sites"][tag]["subnets"]:
            ras = (r["remote_as"] or ["<AS>"])[0]
            A("   # %s, VLAN %s, on the leaf that owns %s" % (tag, r["vlan"], ", ".join(r["peers"]) or "?"))
            A("   router bgp %s" % ras)
            for ip in r["free"]:
                A("     neighbor %s remote-as %s" % (ip, local_as))
            A("     address-family ipv4 unicast")
            for ip in r["free"]:
                A("       neighbor %s activate" % ip)
            A("")
    return "\n".join(L)


def fed_write(outdir, fed, ctx=None, cfg=None):
    """Write the federation worksheets into outdir."""
    mtu = int((cfg or {}).get("fed_rtep_mtu") or 1700)
    if not os.path.isdir(outdir):
        os.makedirs(outdir)
    order = {"FAIL": 0, "DECIDE": 1, "WARN": 2, "PASS": 3, "INFO": 4, "SKIP": 5}
    R = []
    R.append("=" * 74)
    R.append(" NSX FEDERATION READINESS   %s" % now())
    R.append(" " + "  <->  ".join(fed["sites"]))
    R.append("=" * 74)
    tally = collections.Counter(x["state"] for x in fed["checks"])
    R.append(" " + "   ".join("%s %d" % (k, tally.get(k, 0)) for k in ("FAIL", "DECIDE", "WARN", "PASS", "INFO", "SKIP")))
    last = None
    for x in sorted(fed["checks"], key=lambda z: (order.get(z["state"], 9), z["area"], z["item"])):
        if x["state"] != last:
            R.append("-" * 74)
            last = x["state"]
        R.append(" [%-6s] %-10s %-46s" % (x["state"], x["area"], x["item"][:46]))
        if x["detail"]:
            R.append("           %s" % x["detail"][:150])
    if fed["decisions"]:
        R.append("")
        R.append(" DECISIONS STILL OPEN")
        for d in fed["decisions"]:
            R.append("  - %s" % d)
    R.append("")
    R.append(" LOCAL MANAGER THUMBPRINTS (needed when registering each LM with the GM)")
    for t, sdata in fed["sites"].items():
        R.append("  %-16s %-36s %s" % (t, sdata.get("fqdn"), sdata.get("thumbprint") or "not captured"))
    R.append("")
    R.append(" CONSTRAINTS THAT DO NOT DEPEND ON THIS ENVIRONMENT")
    R.append("  NSX multi-tenancy (Projects and VPCs) is not supported with Federation.")
    R.append("  VCF does not deploy or manage Global Manager lifecycle; upgrades are manual")
    R.append("    and the Global Manager must be upgraded before any Local Manager.")
    R.append("  A Centralized Transit Gateway cannot be imported into a Global Manager later.")
    text = "\n".join(R)
    with open(os.path.join(outdir, "readiness.txt"), "w") as f:
        f.write(text)

    def csvw(name, rows, cols):
        if not rows:
            return
        with open(os.path.join(outdir, name), "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
            w.writeheader()
            for r in rows:
                w.writerow(r)
    csvw("dns_records.csv", fed["dns"], ["record", "type", "value", "purpose", "status"])
    csvw("ip_allocation.csv", fed["ips"], ["site", "purpose", "object", "vlan", "subnet", "gateway", "address", "status"])
    csvw("dci_firewall.csv", [{"source": a, "destination": b, "protocol": p_, "port": pt, "purpose": w}
                              for a, b, p_, pt, w in FED_DCI_FLOWS],
         ["source", "destination", "protocol", "port", "purpose"])
    V = ["Federation pre-flight validation", "=" * 70, "",
         "Run before registering any Local Manager with the Global Manager.",
         "Every test must pass in both directions.", ""]
    tags = list(fed["plan"])
    for t in tags:
        p_ = fed["plan"][t]
        V += ["-" * 70, " %s   RTEP VLAN %s   %s   gateway %s" % (t, p_.get("vlan") or "TBD", p_.get("cidr") or "TBD", p_.get("gateway") or "TBD"), "-" * 70]
        for n in p_["nodes"]:
            V += ["  ssh admin@%s" % (n.get("fqdn") or n["name"]), "    get remote-tunnel-endpoint", "    get tunnel-ports"]
            for o in tags:
                if o != t:
                    V += ["    # to every %s remote tunnel endpoint:" % o, "    ping <%s-rtep> size %d dfbit enable" % (o, mtu - 28)]
            V.append("")
    n = sum(len(p_["nodes"]) for p_ in fed["plan"].values())
    V += ["-" * 70, " Expected", "-" * 70,
          "  Remote tunnel endpoints present and Up at both sites.",
          "  DF-bit test at %d bytes (MTU %d minus 28) succeeds every direction, every node." % (mtu - 28, mtu),
          "  No NAT on the path between RTEP subnets; UDP 6081 open both ways.",
          "  %d edge node(s): %d DF-bit tests to run and record." % (n, n * max(0, len(tags) - 1))]
    with open(os.path.join(outdir, "validation.txt"), "w") as f:
        f.write("\n".join(V))
    full = {k: v for k, v in fed.items() if k != "sites"}
    full["checks"] = [dict(x, check=x["item"], result=x["state"]) for x in fed["checks"]]
    write_json(outdir, "fedready_full", full)
    if cfg is not None and not cfg.get("nsx_gm_host"):
        with open(os.path.join(outdir, "federation_runbook.txt"), "w") as f:
            f.write(fed_runbook(cfg, fed, ctx or {}))
    up = fed.get("uplinks")
    if up:
        csvw("uplink_allocation.csv", up["alloc"],
             ["site", "purpose", "object", "vlan", "subnet", "address", "peer",
              "remote_as", "mtu", "status"])
        csvw("bgp_neighbors.csv",
             [{"site": n.get("site"), "tier0": n.get("tier0"), "peer": n.get("peer"),
               "remote_as": n.get("remote_as"), "sources": ", ".join(n.get("sources") or []),
               "max_hop": n.get("max_hop"), "bfd": n.get("bfd"),
               "graceful_restart": n.get("graceful_restart"), "hold_down": n.get("hold_down"),
               "keepalive": n.get("keepalive"), "password_set": n.get("password_set"),
               "filters": " | ".join(n.get("filters") or [])} for n in up["neighbors"]],
             ["site", "tier0", "peer", "remote_as", "sources", "max_hop", "bfd",
              "graceful_restart", "hold_down", "keepalive", "password_set", "filters"])
        write_json(outdir, "northsouth_full", {k: v for k, v in up.items()})
        if cfg is not None:
            with open(os.path.join(outdir, "northsouth_runbook.txt"), "w") as f:
                f.write(fed_northsouth_runbook(cfg, up, ctx or {}))
            with open(os.path.join(outdir, "switch_requirements.txt"), "w") as f:
                f.write(fed_switch_spec(cfg, up))
            write_json(outdir, "northsouth_desired", fed_ns_desired(cfg, up))
    return text


# ---------------------------------------------------------------- NSX Global Manager (existing Federation)
def collect_gm(out, fqdn, user, pw):
    """Read the Global Manager: GM roles, registered sites, sync state, stretched Tier-0/Tier-1
    and the edge clusters each site presents to the GM."""
    basic = base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()
    H = {"Authorization": "Basic " + basic}
    G = "https://%s/global-manager/api/v1/global-infra" % fqdn
    data = {}
    for nm, url in (("version", "https://%s/api/v1/node/version" % fqdn),
                    ("cluster_status", "https://%s/api/v1/cluster/status" % fqdn),
                    ("licenses", "https://%s/api/v1/licenses" % fqdn),
                    ("backup_config", "https://%s/api/v1/cluster/backups/config" % fqdn),
                    ("alarms", "https://%s/api/v1/alarms?page_size=200&status=OPEN" % fqdn),
                    ("alarms_recent", "https://%s/api/v1/alarms?page_size=200&status=RESOLVED" % fqdn),
                    ("global_managers", G + "/global-managers"),
                    ("sites", G + "/sites"),
                    ("full_sync", G + "/full-sync-states"),
                    ("tier0s", G + "/tier-0s"),
                    ("segments", G + "/segments?page_size=400"),
                    ("tier1s", G + "/tier-1s")):
        st, b = http(url, headers=H, timeout=60)
        data[nm] = {"status": st, "body": b}
    if DRY:
        PLAN.append("GET  %s/tier-0s/<id>/locale-services, tier-1s/<id>/locale-services, sites/<site>/enforcement-points/default/{edge-clusters,transport-zones}" % G)
        write_json(out, "gm_%s" % fqdn, data)
        return data
    if data["cluster_status"]["status"] in (401, 403):
        pw2 = reprompt(fqdn, "Global Manager '%s' password" % user)
        if pw2:
            return collect_gm(out, fqdn, user, pw2)
    locale = {}
    for kind in ("tier0s", "tier1s"):
        for gw in _res(data[kind]["body"]):
            gid = gw.get("id")
            if not gid:
                continue
            st, ls = http("%s/%s/%s/locale-services" % (G, "tier-0s" if kind == "tier0s" else "tier-1s", gid), headers=H, timeout=40)
            locale[gw.get("path") or gid] = _res(ls)
    data["locale_services"] = locale
    # Interfaces, BGP and neighbours for every GM gateway. Without this the tool
    # can see that a stretched Tier-0 exists but not a single thing built on it.
    gm_uplinks, gm_bgp, gm_nbrs = [], {}, []
    log("   reading %d Global Manager gateway(s) for interfaces and BGP"
        % len([k for k in locale if "/tier-0s/" in k]))
    for pth, lss in locale.items():
        if "/tier-0s/" not in pth:
            continue
        gid = pth.rstrip("/").split("/")[-1]
        for ls_ in (lss or []):
            lid = ls_.get("id")
            if not lid:
                continue
            st, ifs = http("%s/tier-0s/%s/locale-services/%s/interfaces" % (G, gid, lid),
                           headers=H, timeout=20)
            for i in _res(ifs):
                sub = (i.get("subnets") or [{}])[0]
                addrs = sub.get("ip_addresses") or []
                gm_uplinks.append({
                    "tier0": gid, "locale": lid, "name": i.get("display_name"),
                    "type": i.get("type") or "EXTERNAL",
                    "address": addrs[0] if addrs else None,
                    "prefix_len": sub.get("prefix_len"),
                    "segment_path": i.get("segment_path"), "edge_path": i.get("edge_path"),
                    "mtu": i.get("mtu"), "urpf": i.get("urpf_mode")})
            st, bc = http("%s/tier-0s/%s/locale-services/%s/bgp" % (G, gid, lid),
                          headers=H, timeout=20)
            if isinstance(bc, dict) and bc:
                gm_bgp["%s|%s" % (gid, lid)] = {
                    "tier0": gid, "locale": lid, "local_as": bc.get("local_as_num"),
                    "enabled": bc.get("enabled"), "ecmp": bc.get("ecmp"),
                    "inter_sr_ibgp": bc.get("inter_sr_ibgp")}
            st, nb = http("%s/tier-0s/%s/locale-services/%s/bgp/neighbors" % (G, gid, lid),
                          headers=H, timeout=20)
            for n_ in _res(nb):
                filt = []
                for d_ in ("in_route_filters", "out_route_filters"):
                    for f_ in (n_.get(d_) or []):
                        filt.append("%s %s" % (d_, f_))
                gm_nbrs.append({
                    "tier0": gid, "locale": lid, "name": n_.get("display_name"),
                    "peer": n_.get("neighbor_address"), "remote_as": n_.get("remote_as_num"),
                    "sources": n_.get("source_addresses") or [],
                    "hold_down": n_.get("hold_down_time"), "keepalive": n_.get("keep_alive_time"),
                    "bfd": (n_.get("bfd") or {}).get("enabled"),
                    "max_hop": n_.get("maximum_hop_limit"), "filters": filt})
    gm_rmaps, gm_plists, gm_t1link = {}, {}, {}
    for pth in list(locale.keys()):
        if "/tier-0s/" not in pth:
            continue
        gid = pth.rstrip("/").split("/")[-1]
        st, rm = http("%s/tier-0s/%s/route-maps" % (G, gid), headers=H, timeout=20)
        for r_ in _res(rm):
            gm_rmaps[r_.get("path") or r_.get("id")] = {
                "name": r_.get("display_name") or r_.get("id"),
                "entries": [{"action": e_.get("action"),
                             "prefix_lists": e_.get("prefix_list_matches") or [],
                             "set": e_.get("set") or {}}
                            for e_ in (r_.get("entries") or [])]}
        st, pl = http("%s/tier-0s/%s/prefix-lists" % (G, gid), headers=H, timeout=20)
        for r_ in _res(pl):
            gm_plists[r_.get("path") or r_.get("id")] = {
                "name": r_.get("display_name") or r_.get("id"),
                "prefixes": [{"network": x_.get("network"), "action": x_.get("action"),
                              "ge": x_.get("ge"), "le": x_.get("le")}
                             for x_ in (r_.get("prefixes") or [])]}
    for t_ in _res(data["tier1s"]["body"]):
        gm_t1link[t_.get("id")] = t_.get("tier0_path")
    data["gm_route_maps"] = gm_rmaps
    data["gm_prefix_lists"] = gm_plists
    data["gm_tier1_links"] = gm_t1link
    data["gm_uplinks"] = gm_uplinks
    data["gm_bgp_config"] = gm_bgp
    data["gm_bgp_neighbors"] = gm_nbrs
    # Route re-distribution is set PER LOCATION on a cross-instance Tier-0. Without it
    # the sessions come up and advertise nothing -- the same shape as the zero-prefix
    # fault on the VKS Tier-0. The data is already here; nobody was reading it.
    for pth, lss in locale.items():
        if "/tier-0s/" not in pth:
            continue
        gw = pth.rstrip("/").split("/")[-1]
        for ls_ in (lss or []):
            site_ = ls_.get("id") or "?"
            rules = ((ls_.get("route_redistribution_config") or {})
                     .get("redistribution_rules") or [])
            bp("federation", "%s route redistribution @ %s" % (gw, site_),
               "PASS" if rules else "FAIL",
               ", ".join(str(r_.get("route_redistribution_types")) for r_ in rules)
               or "no redistribution rules -- BGP will establish and advertise nothing")
            ecp = ls_.get("edge_cluster_path") or ""
            bp("federation", "%s edge cluster @ %s" % (gw, site_),
               "INFO" if ecp else "FAIL",
               ecp.rstrip("/").split("/")[-1] or "no edge cluster on this locale service")
    site_ec = {}
    for site in _res(data["sites"]["body"]):
        sid = site.get("id")
        st, ec = http("%s/sites/%s/enforcement-points/default/edge-clusters" % (G, sid), headers=H, timeout=40)
        site_ec[sid] = {"status": st, "clusters": [{"id": c.get("id"), "name": c.get("display_name"), "path": c.get("path")}
                                                  for c in _res(ec)]}
    data["site_edge_clusters"] = site_ec
    site_tz = {}
    for site in _res(data["sites"]["body"]):
        sid = site.get("id")
        st, tz = http("%s/sites/%s/enforcement-points/default/transport-zones?page_size=400" % (G, sid),
                      headers=H, timeout=40)
        site_tz[sid] = {"status": st,
                        "vlan": [{"name": z.get("display_name"), "path": z.get("path")}
                                 for z in _res(tz)
                                 if str(z.get("tz_type") or "").upper().startswith("VLAN")]}
    data["site_transport_zones"] = site_tz
    realized = {}
    for kind in ("tier0s", "tier1s"):
        for gw in _res(data[kind]["body"]):
            pth = gw.get("path")
            if pth:
                st, rs = http("https://%s/global-manager/api/v1/global-infra/realized-state/status?intent_path=%s"
                              % (fqdn, pth), headers=H, timeout=40)
                realized[pth] = {"status": st, "body": rs}
    data["realized"] = realized
    write_json(out, "gm_%s" % fqdn, data)
    return data


def collect_gm_standby(out, fqdn, user, pw):
    """Read-only health of the standby Global Manager. It holds no writable intent -- this
    only confirms it is up, level with the active, and backed up."""
    basic = base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()
    H = {"Authorization": "Basic " + basic}
    data = {}
    for nm, path in (("version", "/api/v1/node/version"),
                     ("cluster_status", "/api/v1/cluster/status"),
                     ("backup_config", "/api/v1/cluster/backups/config"),
                     ("licenses", "/api/v1/licenses")):
        st, b = http("https://%s%s" % (fqdn, path), headers=H, timeout=40)
        data[nm] = {"status": st, "body": b}
    if DRY:
        write_json(out, "gm_standby_%s" % fqdn, data)
        return data
    write_json(out, "gm_standby_%s" % fqdn, data)
    cs = _nb(data, "cluster_status")
    overall = ((cs.get("detailed_cluster_status") or {}).get("overall_status")
               or (cs.get("mgmt_cluster_status") or {}).get("status"))
    bp("federation", "%s standby GM cluster stable" % fqdn,
       "PASS" if str(overall).upper() == "STABLE" else "WARN", overall)
    v = _nb(data, "version")
    bp("federation", "%s standby GM version" % fqdn, "INFO", v.get("product_version"))
    return data


def gm_backup_check(label, data):
    """A Global Manager is not covered by SDDC Manager's file-based backup."""
    b = _nb(data, "backup_config")
    cfgd = bool(isinstance(b, dict) and (b.get("remote_file_server") or b.get("backup_enabled")))
    bp("federation", "%s backup configured" % label, "PASS" if cfgd else "FAIL",
       "SFTP %s" % (((b.get("remote_file_server") or {}).get("server")) if cfgd else
                    "none. VCF does not back up Global Managers; nothing else covers this."))
    return cfgd


def fed_health(fqdn, gm, lms):
    """Checks for an existing Federation. lms: {site_tag: nsx_data} keyed by LM FQDN or instance."""
    cs = _nb(gm, "cluster_status")
    overall = (cs.get("detailed_cluster_status") or {}).get("overall_status") or (cs.get("mgmt_cluster_status") or {}).get("status")
    bp("federation", "%s Global Manager cluster stable" % fqdn, "PASS" if str(overall).upper() == "STABLE" else "WARN", overall)
    gms = _res(_nb(gm, "global_managers"))
    modes = {g.get("display_name") or g.get("id"): g.get("mode") for g in gms}
    active = [n for n, m in modes.items() if str(m).upper() == "ACTIVE"]
    standby = [n for n, m in modes.items() if str(m).upper() == "STANDBY"]
    bp("federation", "one active Global Manager", "PASS" if len(active) == 1 else "FAIL", modes or "none reported")
    bp("federation", "standby Global Manager present", "PASS" if standby else "WARN", standby or "no standby registered")
    sites = _res(_nb(gm, "sites"))
    names = [s_.get("display_name") or s_.get("id") for s_ in sites]
    bp("federation", "sites registered with the Global Manager", "PASS" if len(sites) >= 2 else "FAIL", names)
    gm_backup_check("%s (active GM)" % fqdn, gm)
    for fs in _res(_nb(gm, "full_sync")):
        bp("federation", "full sync %s" % (fs.get("site_id") or fs.get("id")),
           "PASS" if str(fs.get("full_sync_state") or fs.get("state") or "").upper() in ("SUCCESS", "SUCCEEDED", "IN_SYNC", "COMPLETED") else "WARN",
           fs.get("full_sync_state") or fs.get("state") or str(fs)[:80])
    site_ec = gm.get("site_edge_clusters") or {}
    lm_ec = {}
    for tag, d in lms.items():
        lm_ec[tag] = {c.get("display_name"): c.get("id") for c in _res((d.get("edge_clusters") or {}).get("body"))}
    for kind, label in (("tier0s", "Tier-0"), ("tier1s", "Tier-1")):
        for gw in _res(_nb(gm, kind)):
            nm = gw.get("display_name")
            pth = gw.get("path")
            ls = (gm.get("locale_services") or {}).get(pth) or []
            locs = []
            for l in ls:
                ecp = l.get("edge_cluster_path") or ""
                m = re.search(r"/sites/([^/]+)/", ecp)
                site = m.group(1) if m else "?"
                ecid = ecp.rsplit("/", 1)[-1] if ecp else None
                known = {c["id"]: c["name"] for c in (site_ec.get(site) or {}).get("clusters", [])}
                locs.append({"site": site, "edge_cluster_id": ecid, "edge_cluster_name": known.get(ecid),
                             "present_on_gm_site_view": ecid in known})
            if kind == "tier0s":
                bp("federation", "%s %s stretched across sites" % (label, nm), "PASS" if len(locs) >= 2 else "WARN",
                   "%s  ha_mode=%s" % ([x["site"] for x in locs], gw.get("ha_mode")))
            else:
                bp("federation", "%s %s has a failover location" % (label, nm), "PASS" if len(locs) >= 2 else "WARN",
                   [x["site"] for x in locs] or "no locale services")
            for x in locs:
                bp("federation", "%s %s edge cluster resolves at %s" % (label, nm, x["site"]),
                   "PASS" if x["present_on_gm_site_view"] else "FAIL",
                   "%s (%s)" % (x["edge_cluster_name"] or "unknown", x["edge_cluster_id"]))
            r_ = ((gm.get("realized") or {}).get(pth) or {})
            body_ = r_.get("body") if isinstance(r_, dict) else None
            if isinstance(body_, dict) and body_.get("consolidated_status"):
                cstat = (body_.get("consolidated_status") or {}).get("consolidated_status")
                bp("federation", "%s %s realized" % (label, nm), "PASS" if str(cstat).upper() == "SUCCESS" else "WARN", cstat)
    # GM-visible edge cluster names vs LM edge cluster names, per site
    for site, v in site_ec.items():
        gm_names = sorted(c["name"] for c in v.get("clusters", []) if c.get("name"))
        bp("federation", "%s edge clusters as seen by the GM" % site, "INFO", gm_names or "none")


# ---------------------------------------------------------------- SDDC DB via vcf user + su
def sddc_remote_db(out, host, vcf_user, vcf_pw, root_pw):
    """Copy this script to the SDDC Manager as the vcf user, run it as root with `su -`,
    and keep the JSON it prints (lock table, table counts, credential shape)."""
    if DRY:
        PLAN.append("SSH  %s@%s  cat > /tmp/fp_agent.py ; su - -c 'python3 /tmp/fp_agent.py _sddc_json'" % (vcf_user, host))
        return
    with open(os.path.abspath(sys.argv[0])) as fh:
        me = fh.read()
    log("  ssh %s@%s (45s max)" % (vcf_user, host))
    ok, o = ssh_exec(host, vcf_user, vcf_pw, "cat > /tmp/fp_agent.py && chmod 644 /tmp/fp_agent.py",
                     stdin_data=me, timeout=45)
    if not ok and is_auth_failure(o):
        pw2 = reprompt(host, "'%s' SSH password" % vcf_user)
        if pw2:
            vcf_pw = pw2
            ok, o = ssh_exec(host, vcf_user, vcf_pw, "cat > /tmp/fp_agent.py && chmod 644 /tmp/fp_agent.py",
                             stdin_data=me, timeout=45)
    if not ok:
        write_json(out, "sddcdb_remote", {"_error": "copy failed: %s" % o})
        log("  DB layer over SSH: not collected (%s)" % o[:80])
        return
    # prove `su -` works with this root password before the long run (20s, cheap)
    log("  su - on %s (20s max)" % host)
    ok, o = ssh_exec(host, vcf_user, vcf_pw, "su - -c id", stdin_data=(root_pw or "") + "\n", timeout=20, tty=True)
    if "uid=0" not in o:
        pw2 = reprompt(host, "root password (for su)")
        if pw2:
            root_pw = pw2
            ok, o = ssh_exec(host, vcf_user, vcf_pw, "su - -c id", stdin_data=root_pw + "\n", timeout=20, tty=True)
    if "uid=0" not in o:
        ssh_exec(host, vcf_user, vcf_pw, "rm -f /tmp/fp_agent.py", timeout=15)
        write_json(out, "sddcdb_remote", {"_error": "su failed: %s" % o[-200:]})
        log("  DB layer over SSH: not collected (su to root did not succeed on %s)" % host)
        return
    log("  collecting platform DB on %s (90s max)" % host)
    cmd = "su - -c 'python3 /tmp/fp_agent.py _sddc_json; rm -f /tmp/fp_agent.py'"
    ok, o = ssh_exec(host, vcf_user, vcf_pw, cmd, stdin_data=(root_pw or "") + "\n", timeout=90, tty=True)
    if "{" not in o:
        ssh_exec(host, vcf_user, vcf_pw, "rm -f /tmp/fp_agent.py", timeout=15)
    start, end = o.find("{"), o.rfind("}")
    if start >= 0 and end > start:
        try:
            data = json.loads(o[start:end + 1])
            write_json(out, "sddcdb_remote", data)
            if isinstance(data.get("lock"), list):
                write_json(out, "sddcdb_lock", {"table": "lock", "rows": data["lock"], "_via": "ssh+su"})
            for t, rws in (data.get("tables") or {}).items():
                write_json(out, "sddcdb_%s" % t, {"table": t, "rows": rws, "_via": "ssh+su"})
            write_json(out, "sddcdb_summary", {t: len(v) for t, v in (data.get("tables") or {}).items()})
            log("  DB layer over SSH: %d table(s), lock rows: %s" % (len(data.get("tables") or {}),
                                                                       len(data.get("lock") or [])))
            return
        except Exception as e:
            o = "bad json: %s" % e
    write_json(out, "sddcdb_remote", {"_error": o[-300:]})
    log("  DB layer over SSH: not collected (su or python failed)")


def sddc_agent_json():
    """Runs ON the SDDC Manager as root. Prints one JSON document to stdout."""
    res = {"node": os.uname()[1], "lock": None, "tables": {}}
    ok, r = run_sql("sddc", "platform", "select * from lock;")
    res["lock"] = r if ok else {"_error": str(r)[:200]}
    ok, tables = list_tables("sddc", "platform", SDDC_TABLE_PAT)
    if ok:
        for t in tables:
            ok2, rws = run_sql("sddc", "platform", 'SELECT * FROM "%s" LIMIT 2000;' % t)
            if ok2:
                res["tables"][t] = rws
    else:
        res["_error"] = str(tables)[:200]
    return res


# ---------------------------------------------------------------- collect: ops
def collect_ops(out, cfg, host):
    auth = ops_auth(host, cfg["ops_user"], cfg["ops_password"])
    if not auth:
        return False
    base = "https://%s/suite-api/api" % host
    H = {"Authorization": auth}

    log("Operations API: inventory")
    for nm, path in (("adapters", "/adapters?_no_links=true"),
                     ("collectors", "/collectors?_no_links=true"),
                     ("adapterkinds", "/adapterkinds?_no_links=true"),
                     ("node_status", "/deployment/node/status"),
                     ("version", "/versions/current"),
                     ("solutions", "/solutions?_no_links=true")):
        st, b = http(base + path, headers=H)
        write_json(out, "opsapi_" + nm, {"status": st, "body": b})

    # fleet lifecycle status as seen from Operations (auth model varies; record whatever answers)
    fl = {}
    for path in ("/vcf-operations/plug/ops-lcm/lcm/bootstrap/api/status",
                 "/lcm/bootstrap/api/status", "/lcm/lcops/api/environments"):
        st, b = http("https://%s%s" % (host, path), headers=H)
        fl[path] = {"status": st, "body": b if isinstance(b, dict) and len(json.dumps(b)) < 20000 else str(b)[:2000]}
    write_json(out, "opsapi_fleet_lifecycle", fl)

    # CaSA cluster roles (basic auth, separate service)
    basic = base64.b64encode(("%s:%s" % (cfg["ops_user"], cfg["ops_password"])).encode()).decode()
    st, casa = http("https://%s/casa/cluster/config" % host, headers={"Authorization": "Basic " + basic})
    roles = {s.get("node_name"): s.get("node_type") for s in rows(casa) if isinstance(s, dict)}
    write_json(out, "opsapi_casa_roles", {"status": st, "roles": roles,
                                          "online": {s.get("node_name"): s.get("online_state")
                                                     for s in rows(casa) if isinstance(s, dict)}})
    if not DRY:
        log("  CaSA roles: %s" % (roles or "unavailable (HTTP %s)" % st))

    st, adapters = http(base + "/adapters?_no_links=true", headers=H)
    instances, vcenters, fqdn_ids = {}, [], set()
    for a in rows(adapters):
        rk = a.get("resourceKey") or a.get("resourceKind") or {}
        kind, name = rk.get("adapterKindKey") or "", rk.get("name") or ""
        ids = {}
        for i in rk.get("resourceIdentifiers") or []:
            t = (i.get("identifierType") or {}).get("name")
            if t:
                ids[t] = i.get("value")
                v = str(i.get("value") or "").strip().rstrip("/")
                if FQDN.match(v) and "." in v:
                    fqdn_ids.add(v.lower())
        if kind == "VcfAdapter":
            instances[name] = {"sddc": ids.get("SDDCManager_Hostname"),
                               "uuid": ids.get("SDDCManager_uuid"), "adapter_id": a.get("id"),
                               "domain_monitoring_on_creation": ids.get("DomainMonitoringOnCreation")}
        elif kind == "VMWARE" and ids.get("VCURL"):
            vcenters.append(ids["VCURL"].strip().rstrip("/").lower())
    if not DRY:
        log("  instances: %s" % (", ".join(sorted(instances)) or "none"))

    log("Operations API: resources (HostSystem, VCF adapter objects)")
    hosts = paged(base + "/resources?resourceKind=HostSystem", H)
    known_hosts = sorted(set((r.get("resourceKey") or {}).get("name", "").lower()
                             for r in hosts if isinstance(r, dict)) - {""})
    host_states = {}
    for r in hosts:
        if isinstance(r, dict):
            nm = (r.get("resourceKey") or {}).get("name", "").lower()
            host_states[nm] = [{"adapter": x.get("adapterInstanceId"), "status": x.get("resourceStatus"),
                                "state": x.get("resourceState"), "msg": x.get("statusMessage")}
                               for x in r.get("resourceStatusStates") or []]
    write_json(out, "opsapi_resources_hosts", {"count": len(known_hosts), "hosts": known_hosts,
                                               "states": host_states, "raw": hosts})
    vcf_res = paged(base + "/resources?adapterKind=VcfAdapter", H)
    write_json(out, "opsapi_resources_vcf", {
        "count": len(vcf_res),
        "objects": [{"kind": (r.get("resourceKey") or {}).get("resourceKindKey"),
                     "name": (r.get("resourceKey") or {}).get("name"),
                     "id": r.get("identifier"), "health": r.get("resourceHealth"),
                     "states": [{"adapter": x.get("adapterInstanceId"), "status": x.get("resourceStatus"),
                                 "state": x.get("resourceState"), "msg": x.get("statusMessage")}
                                for x in r.get("resourceStatusStates") or []]}
                    for r in vcf_res if isinstance(r, dict)],
        "raw": vcf_res})
    # adapter -> collector mapping
    st, cols = http(base + "/collectors?_no_links=true", headers=H)
    cmap = {c.get("id"): c.get("name") for c in rows(cols) if isinstance(c, dict)}
    amap = []
    for a in rows(adapters):
        rk = a.get("resourceKey") or {}
        if rk.get("adapterKindKey") in ("VcfAdapter", "VMWARE", "VMWARE_INFRA_MANAGEMENT",
                                        "VMWARE_INFRA_HEALTH", "NSXTAdapter"):
            amap.append({"adapter": rk.get("name"), "kind": rk.get("adapterKindKey"),
                         "collector_id": a.get("collectorId"),
                         "collector": cmap.get(a.get("collectorId"), a.get("collectorId")),
                         "last_collected": a.get("lastCollected")})
    write_json(out, "opsapi_adapter_collectors", amap)
    write_json(out, "opsapi_topology", {"instances": instances, "vcenters": sorted(set(vcenters)),
                                        "hosts": known_hosts,
                                        "other_fqdn_identifiers": sorted(fqdn_ids)})

    log("Operations API: fleet password / certificate management")
    pwq = base + "/fleet-management/password-management/accounts/query?page=0&pageSize=2000"
    cq = base + "/fleet-management/certificate-management/certificates/query?page=0&pageSize=2000"
    for nm, url, payload in (("pw_empty", pwq, {}), ("pw_active", pwq, {"status": "ACTIVE"}),
                             ("pw_ssh", pwq, {"credentialType": "SSH"}),
                             ("pw_esx", pwq, {"appliance": "ESX"}),
                             ("cert_empty", cq, {}), ("cert_tls", cq, {"category": "TLS_CERT"}),
                             ("cert_normal", cq, {"status": "NORMAL"})):
        st, b = http(url, method="POST", headers=H, body=payload)
        write_json(out, "opsapi_fm_" + nm, {"status": st, "body": b})
        if not DRY:
            log("  %-12s HTTP %-4s %5d records" % (nm, st, len(rows(b))))

    targets = sorted(set(known_hosts) | set(vcenters) | fqdn_ids)
    log("Operations API: probing %d appliances" % len(targets))
    pq = base + "/fleet-management/password-management/accounts/query?page=0&pageSize=100"
    cqs = base + "/fleet-management/certificate-management/certificates/query?page=0&pageSize=100"
    probes = {}
    for i, fq in enumerate(targets, 1):
        st1, b1 = http(pq, method="POST", headers=H, body={"applianceFqdn": fq})
        st2, b2 = http(cqs, method="POST", headers=H, body={"applianceFqdn": fq})
        probes[fq] = {"pw": len(rows(b1)), "cert": len(rows(b2)), "pw_http": st1, "cert_http": st2,
                      "pw_rows": rows(b1), "cert_rows": rows(b2)}
        if not DRY and (i % 10 == 0 or i == len(targets)):
            log("  %d/%d" % (i, len(targets)))
        if not DRY:
            time.sleep(0.05)
    write_json(out, "opsapi_probes", probes)

    on_node = detect_role() == "ops"
    if on_node and (os.geteuid() == 0 or DRY):
        log("Operations DB: vcopsdb")
        ok, tables = list_tables("ops", "vcopsdb", OPS_TABLE_PAT, 5433)
        if ok:
            log("  %d candidate tables" % len(tables))
            summ = dump_tables("ops", "vcopsdb", tables, out, "opsdb")
            write_json(out, "opsdb_summary", summ)
            presence = {}
            if not DRY:
                for t in tables:
                    p = os.path.join(out, "opsdb_%s.json" % SAFE.sub("_", t))
                    if os.path.exists(p):
                        with open(p) as fh:
                            blob = fh.read().lower()
                        presence[t] = {fq: blob.count(fq) for fq in targets if fq in blob}
            write_json(out, "opsdb_host_presence", presence)
        else:
            log("  ! DB unavailable: %s" % str(tables)[:160])
            write_json(out, "opsdb_summary", {"_error": str(tables)})
        log("Operations logs: vcops-bridge")
        analyse_bridge_logs(out)
        log("Operations logs: other")
        scan_ops_logs(out)
        write_json(out, "ops_clock", local_clock())
        # other cluster nodes (from CaSA) and cloud proxies (from collectors): same analysis over SSH
        others = [n for n in roles if n and n.lower() not in os.uname()[1].lower()]
        if others and (cfg.get("ops_root_password") or DRY):
            log("Operations logs: other cluster nodes over SSH")
            dom = ".".join(os.uname()[1].split(".")[1:])
            for n in others:
                target = n if "." in n else (n + "." + dom if dom else n)
                remote_bridge_analysis(target, "root", cfg.get("ops_root_password"), out, n)
        elif others:
            log("Operations logs: other cluster nodes skipped (no Ops root password given)")
    else:
        log("Operations DB/logs: skipped (not on an Ops node as root)")

    # ---- Operations best practices
    if not DRY:
        online = {s_.get("node_name"): s_.get("online_state") for s_ in rows(casa) if isinstance(s_, dict)}
        vers = {s_.get("node_name"): s_.get("product_version") for s_ in rows(casa) if isinstance(s_, dict)}
        if online:
            bp("ops", "all cluster nodes ONLINE", "PASS" if all(v == "ONLINE" for v in online.values()) else "FAIL", online)
            bp("ops", "all cluster nodes on the same build", "PASS" if len(set(vers.values())) == 1 else "FAIL", vers)
        else:
            bp("ops", "CaSA cluster status", "SKIP", "HTTP %s" % st)
        for s_ in rows(casa):
            for c in (s_.get("certificate_description") or [])[:1]:
                d = days_until(c.get("valid_to"))
                if d is not None:
                    bp("ops", "%s certificate expiry" % s_.get("node_name"),
                       "FAIL" if d < 14 else ("WARN" if d < 90 else "PASS"), "%d days" % d)
        stale_ad = []
        for a in rows(adapters):
            lc = a.get("lastCollected")
            if isinstance(lc, (int, float)) and (time.time() * 1000 - lc) > 2 * 3600 * 1000:
                stale_ad.append((a.get("resourceKey") or {}).get("name"))
        bp("ops", "adapters collected within the last 2h", "PASS" if not stale_ad else "WARN", stale_ad[:8])
        ck = local_clock()
        td, ch = ck.get("timedatectl", ""), ck.get("chronyc", "")
        synced = ("synchronized: yes" in td.lower()) or ("leap status" in ch.lower() and "normal" in ch.lower())
        if (not td or td.startswith("n/a")) and (not ch or ch.startswith("n/a")):
            bp("ops", "%s clock synchronised (NTP)" % os.uname()[1], "SKIP", "no timedatectl/chronyc")
        else:
            bp("ops", "%s clock synchronised (NTP)" % os.uname()[1], "PASS" if synced else "WARN", (td or ch)[:120])
        for key, label in (("opsapi_fm_pw_active", "fleet password accounts"), ("opsapi_fm_cert_tls", "fleet certificates")):
            recs = rows((_read_json(out, key) or {}).get("body"))
            soon = []
            for r in recs:
                if not isinstance(r, dict):
                    continue
                exp = next((r[k] for k in r if re.search(r"expir|valid_?to|validTo|notAfter", k, re.I) and r[k]), None)
                d = days_until(exp) if exp else None
                if d is not None and d < 60:
                    soon.append("%s %s in %dd" % (r.get("applianceFqdn"), r.get("userName") or "", d))
            if recs:
                bp("ops", "%s expiring within 60 days" % label, "PASS" if not soon else "WARN", soon[:10])
    return True


def _read_json(outdir, name):
    p = os.path.join(outdir, SAFE.sub("_", name) + ".json")
    if not os.path.exists(p):
        return None
    with open(p) as fh:
        return json.load(fh)


# ---------------------------------------------------------------- remote helpers
def reachable(host, path="/v1/sddc-managers"):
    """True if the SDDC Manager answers HTTPS at all (401/403 count as reachable)."""
    if DRY:
        return True
    st, _ = http("https://%s%s" % (host, path), timeout=12, retries=0)
    return st != 0


def ssh_lock_query(host, out, cfg):
    """Opportunistic: fetch platform.lock over SSH if keys (or sshpass) allow it.
    Never prompts, never blocks. Silently records why it could not."""
    if DRY:
        PLAN.append("SSH  root@%s  psql platform 'select * from lock' (only if keys/sshpass allow)" % host)
        return
    sql = "select * from lock;"
    remote = ("psql -h localhost -U postgres -d platform -X -q -w --csv -c \"%s\" 2>/dev/null || "
              "/usr/pgsql/13/bin/psql -h localhost -U postgres -d platform -X -q -w --csv -c \"%s\"" % (sql, sql))
    user = cfg.get("sddc_ssh_user") or "root"
    common = ["-o", "StrictHostKeyChecking=accept-new", "-o", "ConnectTimeout=6",
              "-o", "LogLevel=ERROR", "%s@%s" % (user, host), remote]
    cmds = [["ssh", "-o", "BatchMode=yes"] + common]          # key-based, never prompts
    pw = os.environ.get("FLEETPARITY_SDDC_SSH_PASSWORD") or cfg.get("sddc_ssh_password")
    env = dict(os.environ)
    if pw and _first_existing(["sshpass"]):
        env["SSHPASS"] = pw
        cmds.insert(0, ["sshpass", "-e", "ssh", "-o", "PubkeyAuthentication=no"] + common)
    for cmd in cmds:
        try:
            p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=40, env=env)
        except Exception as e:
            write_json(out, "sddcdb_lock", {"table": "lock", "rows": [], "_error": str(e)})
            return
        o = p.stdout.decode("utf-8", "replace")
        if p.returncode == 0 and o.strip():
            recs = [deep_redact(r) for r in csv.DictReader(io.StringIO(o))]
            write_json(out, "sddcdb_lock", {"table": "lock", "rows": recs, "_via": "ssh"})
            log("  lock table via SSH: %d row(s)" % len(recs))
            return
    write_json(out, "sddcdb_lock", {"table": "lock", "rows": [], "_error":
               "not collected: no SSH key/sshpass access from this node (run `collect` on the "
               "SDDC Manager itself for the DB layer)"})
    log("  lock table: not reachable over SSH from here (optional; DB layer skipped)")


# ---------------------------------------------------------------- collect: sddc
def collect_sddc(out, cfg, host, tag):
    auth = sddc_auth(host, cfg["sddc_user"], cfg["sddc_password"])
    if not auth and not DRY:
        pw2 = reprompt(tag, "'%s' password" % cfg["sddc_user"])
        if pw2:
            cfg["sddc_password"] = pw2
            _CRED_CACHE["sddc_password_%s" % tag] = pw2
            auth = sddc_auth(host, cfg["sddc_user"], pw2)
    if not auth:
        return False
    b = "https://%s/v1" % host
    H = {"Authorization": auth}
    log("SDDC API")
    for nm, path in (("sddc_managers", "/sddc-managers"), ("domains", "/domains"),
                     ("clusters", "/clusters"), ("hosts", "/hosts"),
                     ("network_pools", "/network-pools"), ("credentials", "/credentials"),
                     ("credentials_esxi", "/credentials?resourceType=ESXI"),
                     ("credentials_vcenter", "/credentials?resourceType=VCENTER"),
                     ("credential_tasks", "/credentials/tasks"), ("vcenters", "/vcenters"),
                     ("nsxt_clusters", "/nsxt-clusters"), ("tasks_recent", "/tasks?limit=200"),
                     ("upgrades", "/upgrades"), ("ntp", "/system/ntp-configuration"),
                     ("dns", "/system/dns-configuration"),
                     ("backup_config", "/system/backup-configuration")):
        st, body = http(b + path, headers=H)
        write_json(out, "sddcapi_" + nm, {"status": st, "body": body})
        if not DRY:
            log("  %-20s HTTP %-4s %5d" % (nm, st, len(rows(body))))

    st, hosts = http(b + "/hosts", headers=H)
    topo = collections.defaultdict(list)
    for h in rows(hosts):
        fq = (dig(h, "fqdn") or "").lower()
        dom = (h.get("domain") or {}).get("name") or "(unassigned)"
        if fq:
            topo[dom].append(fq)
    ips = {}
    for h in rows(hosts):
        fq = (dig(h, "fqdn") or "").lower()
        if fq:
            ips[fq] = {i.get("type"): i.get("ipAddress") for i in h.get("ipAddresses") or [] if isinstance(i, dict)}
    write_json(out, "sddcapi_topology", {"tag": tag, "domains": dict(topo), "host_ips": ips})

    # per-domain resource certificates
    st, doms = http(b + "/domains", headers=H)
    for d in rows(doms):
        did, dn = d.get("id"), d.get("name")
        if did:
            st2, rc = http(b + "/domains/%s/resource-certificates" % did, headers=H)
            write_json(out, "sddcapi_resource_certs_%s" % SAFE.sub("_", str(dn)), {"status": st2, "body": rc})

    # ---- SDDC best practices (API layer)
    if not DRY:
        bc = _read_json(out, "sddcapi_backup_config")
        bcb = (bc or {}).get("body") if bc else None
        locs = (bcb or {}).get("backupLocations") if isinstance(bcb, dict) else None
        bp("sddc:%s" % tag, "file-based backup configured", "PASS" if locs else "WARN",
           [l_.get("server") for l_ in locs] if locs else "no backup location")
        ntp = ((_read_json(out, "sddcapi_ntp") or {}).get("body") or {})
        bp("sddc:%s" % tag, "NTP servers configured", "PASS" if isinstance(ntp, dict) and ntp.get("ntpServers") else "WARN",
           [x.get("ipAddress") for x in (ntp.get("ntpServers") or []) if isinstance(x, dict)] if isinstance(ntp, dict) else ntp)
        dns = ((_read_json(out, "sddcapi_dns") or {}).get("body") or {})
        bp("sddc:%s" % tag, "DNS configured", "PASS" if isinstance(dns, dict) and (dns.get("primaryDnsServer") or dns.get("dnsServers")) else "WARN")
        for d in rows(doms):
            bp("sddc:%s" % tag, "domain %s status" % d.get("name"), "PASS" if str(d.get("status")).upper() == "ACTIVE" else "WARN", d.get("status"))
        na = [dig(h, "fqdn") for h in rows(hosts) if str(h.get("status", "")).upper() not in ("ASSIGNED", "UNASSIGNED_USEABLE")]
        bp("sddc:%s" % tag, "hosts in a healthy assignment state", "PASS" if not na else "WARN", na[:8])
        pools = rows((_read_json(out, "sddcapi_network_pools") or {}).get("body"))
        low = []
        for p_ in pools:
            for n in p_.get("networks") or []:
                free = n.get("freeIPs") if n.get("freeIPs") is not None else n.get("freeIpCount")
                if isinstance(free, int) and free <= 2:
                    low.append("%s/%s free=%d" % (p_.get("name"), n.get("type"), free))
        bp("sddc:%s" % tag, "network pools have spare IPs", "PASS" if not low else "WARN", low[:8])
        ct = rows((_read_json(out, "sddcapi_credential_tasks") or {}).get("body"))
        failed = [t for t in ct if str(t.get("status", "")).upper() == "FAILED"]
        bp("sddc:%s" % tag, "no failed credential tasks", "PASS" if not failed else "WARN",
           ["%s %s" % (t.get("id"), t.get("name")) for t in failed[:5]])
        creds = rows((_read_json(out, "sddcapi_credentials") or {}).get("body"))
        with_pol = [c for c in creds if c.get("autoRotatePolicy")]
        bp("sddc:%s" % tag, "credentials with an auto-rotate policy", "INFO", "%d of %d" % (len(with_pol), len(creds)))
        soon = []
        for dn in [d.get("name") for d in rows(doms)]:
            rc = (_read_json(out, "sddcapi_resource_certs_%s" % SAFE.sub("_", str(dn))) or {}).get("body")
            for c in rows(rc):
                exp = next((c[k] for k in c if re.search(r"expir|notAfter|validTo", k, re.I) and c[k]), None)
                d_ = days_until(exp) if exp else None
                if d_ is not None and d_ < 60:
                    soon.append("%s %s in %dd" % (dn, c.get("issuedTo") or c.get("resource", {}).get("fqdn") if isinstance(c.get("resource"), dict) else c.get("issuedTo"), d_))
        bp("sddc:%s" % tag, "resource certificates expiring within 60 days", "PASS" if not soon else "WARN", soon[:10])

    if detect_role() == "sddc" and (os.geteuid() == 0 or DRY):
        log("SDDC DB: platform")
        ok, tables = list_tables("sddc", "platform", SDDC_TABLE_PAT)
        if ok:
            log("  %d candidate tables" % len(tables))
            write_json(out, "sddcdb_summary", dump_tables("sddc", "platform", tables, out, "sddcdb"))
        else:
            log("  ! DB unavailable: %s" % str(tables)[:160])
            write_json(out, "sddcdb_summary", {"_error": str(tables)})
    else:
        if cfg.get("sddc_ssh_password") and cfg.get("sddc_root_password"):
            log("SDDC DB: over SSH as %s with su" % (cfg.get("sddc_ssh_user") or "vcf"))
            sddc_remote_db(out, host, cfg.get("sddc_ssh_user") or "vcf",
                           cfg["sddc_ssh_password"], cfg["sddc_root_password"])
        else:
            log("SDDC DB: not local to this node; trying key-based SSH for platform.lock")
            ssh_lock_query(host, out, cfg)
    if not DRY:
        lk = _read_json(out, "sddcdb_lock") or {}
        if isinstance(lk.get("rows"), list) and not lk.get("_error"):
            bp("sddc:%s" % tag, "no rows in platform.lock", "PASS" if not lk["rows"] else "FAIL", len(lk["rows"]))
    return True


# ---------------------------------------------------------------- collect: fleet
def collect_fleet(out):
    log("Fleet Manager DB: vrlcm")
    ok, tables = list_tables("fleet", "vrlcm", FLEET_TABLE_PAT)
    if ok:
        write_json(out, "fleetdb_summary", dump_tables("fleet", "vrlcm", tables, out, "fleetdb"))
        return True
    log("  ! DB unavailable: %s" % str(tables)[:160])
    write_json(out, "fleetdb_summary", {"_error": str(tables)})
    return False


# ---------------------------------------------------------------- collect main
def cmd_collect(a):
    global DRY
    DRY = bool(a.plan)
    cfg = read_config(a.config or os.environ.get("FLEETPARITY_CONFIG"))
    role = a.role or detect_role()
    tag = SAFE.sub("_", a.tag or cfg.get("tag") or role)
    outroot = a.outdir or cfg.get("outdir") or "/tmp/fleetparity"
    out = os.path.join(outroot, "%s_%s_%s" % (TOOL, tag, time.strftime("%Y%m%d-%H%M%S")))
    if not DRY:
        os.makedirs(out)
    log("%s %s collect  role=%s tag=%s%s" % (TOOL, __version__, role, tag,
                                             "  (PLAN ONLY)" if DRY else "  ->  " + out))
    if DRY:
        log("dry run: nothing is executed, no credentials are used")
    else:
        log("read-only: GET / POST ..query / SELECT / log reads only")

    meta = {"role": role, "tag": tag, "hostname": os.uname()[1], "euid": os.geteuid(),
            "site": cfg.get("site_name"), "tool_version": __version__}
    ok = True
    if role in ("ops", "remote"):
        host = a.host or cfg.get("ops_host") or ("localhost" if role == "ops" else None)
        if not host:
            sys.exit("--host required for remote collection")
        cfg["ops_user"] = os.environ.get("FLEETPARITY_OPS_USER") or cfg.get("ops_user") or "admin"
        cfg["ops_password"] = secret("FLEETPARITY_OPS_PASSWORD", cfg, ["ops_password"],
                                     "VCF Operations '%s' password: " % cfg["ops_user"])
        meta["host"] = host
        ok = collect_ops(out, cfg, host)
    elif role == "sddc":
        host = a.host or "localhost"
        cfg["sddc_user"] = (os.environ.get("FLEETPARITY_SDDC_USER") or cfg.get("sddc_user")
                            or "administrator@vsphere.local")
        cfg["sddc_password"] = secret("FLEETPARITY_SDDC_PASSWORD", cfg,
                                      ["sddc_password_%s" % tag, "sddc_password"],
                                      "SDDC Manager '%s' password: " % cfg["sddc_user"])
        meta["host"] = host
        ok = collect_sddc(out, cfg, host, tag)
    elif role == "fleet":
        ok = collect_fleet(out)
    else:
        sys.exit("unknown role %s" % role)

    if DRY:
        print("\nPLAN (%d operations, none executed):" % len(PLAN))
        for p in PLAN:
            print("  " + p)
        return
    tgz = finalize_bundle(out, meta)
    log("bundle: %s" % tgz)
    print("\nNEXT: copy this bundle next to the others, then run:\n"
          "  python3 %s compare /path/to/*.tgz\n" % os.path.basename(sys.argv[0]))
    if not ok:
        sys.exit(2)


# ---------------------------------------------------------------- compare
def load_bundles(paths):
    bundles = []
    for p in paths:
        if os.path.isdir(p):
            d = p
        elif p.endswith(".tgz") or p.endswith(".tar.gz"):
            d = tempfile.mkdtemp(prefix="fp_cmp_")
            with tarfile.open(p) as t:
                # 'data' filter (3.12+) blocks path traversal from a crafted bundle
                try:
                    t.extractall(d, filter="data")
                except TypeError:
                    t.extractall(d)
            sub = [x for x in os.listdir(d) if os.path.isdir(os.path.join(d, x))]
            d = os.path.join(d, sub[0]) if sub else d
        else:
            continue
        mp = os.path.join(d, "manifest.json")
        meta = {"role": "?", "tag": "?"}
        if os.path.exists(mp):
            with open(mp) as fh:
                meta = json.load(fh).get("meta", meta)
        data = {}
        for fn in os.listdir(d):
            if fn.endswith(".json") and fn != "manifest.json":
                try:
                    with open(os.path.join(d, fn)) as fh:
                        data[fn[:-5]] = json.load(fh)
                except Exception:
                    pass
        bundles.append({"path": p, "meta": meta, "data": data})
    return bundles


class Flags(object):
    ORDER = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "INFO": 3}

    def __init__(self):
        self.items = []

    def add(self, sev, title, evidence=None):
        self.items.append({"severity": sev, "title": title, "evidence": list(evidence or [])})

    def render(self):
        out = []
        for f in sorted(self.items, key=lambda x: self.ORDER.get(x["severity"], 9)):
            out.append("  [%-8s] %s" % (f["severity"], f["title"]))
            for e in f["evidence"][:10]:
                out.append("             - %s" % e)
            if len(f["evidence"]) > 10:
                out.append("             - ... %d more" % (len(f["evidence"]) - 10))
        return "\n".join(out) if out else "  (no deltas flagged)"


def body(bundle, key):
    v = bundle["data"].get(key)
    return v["body"] if isinstance(v, dict) and "body" in v else v


def cmd_compare(a):
    cfg = read_config(a.config or os.environ.get("FLEETPARITY_CONFIG"))
    outdir = a.outdir or cfg.get("outdir") or "/tmp/fleetparity"
    text, flags = do_compare(a.bundles, cfg, outdir)
    sys.exit(1 if flags.items else 0)


def do_compare(paths, cfg, outdir):
    warn_days = int(cfg.get("rotation_warn_days") or 30)
    bundles = load_bundles(paths)
    ops = [b for b in bundles if b["meta"].get("role") in ("ops", "remote")]
    comps = [b for b in bundles if b["meta"].get("role") == "components"]
    sddcs = [b for b in bundles if b["meta"].get("role") == "sddc"]
    fleets = [b for b in bundles if b["meta"].get("role") == "fleet"]
    flags = Flags()
    report = []
    R = report.append

    R("=" * 78)
    R(" %s %s  --  parity report  %s" % (TOOL.upper(), __version__, now()))
    site = next((b["meta"].get("site") for b in bundles if b["meta"].get("site")), None)
    if site:
        R(" site: %s" % site)
    R("=" * 78)
    R(" bundles: %d ops, %d sddc, %d fleet" % (len(ops), len(sddcs), len(fleets)))
    for b in bundles:
        R("   %-6s %-14s %s" % (b["meta"].get("role"), b["meta"].get("tag"), os.path.basename(b["path"])))

    # ---- expected topology
    expected = collections.OrderedDict()
    for s in sddcs:
        expected[s["meta"]["tag"]] = (s["data"].get("sddcapi_topology") or {}).get("domains", {})
    if not expected and ops:
        hs = (ops[0]["data"].get("opsapi_resources_hosts") or {}).get("hosts", [])
        expected["(ops-known)"] = {"(ungrouped)": hs}
    all_seen = set()
    for doms in expected.values():
        for lst in doms.values():
            all_seen.update(x.lower() for x in lst)
    exp_cfg = [x.lower() for x in (cfg.get("expected_hosts") or [])]
    never = [x for x in exp_cfg if x not in all_seen]
    if never:
        flags.add("HIGH", "%d configured expected_hosts never discovered anywhere" % len(never), never)

    incomplete = []
    if ops:
        o = ops[0]
        probes = o["data"].get("opsapi_probes") or {}
        R("\n" + "-" * 78)
        R(" OPERATIONS FLEET API  vs  SDDC MANAGER INVENTORY   (per domain)")
        R("-" * 78)
        for inst, doms in expected.items():
            R("\n instance %s" % inst)
            for dom, members in sorted(doms.items()):
                members = [m.lower() for m in members]
                pres = [m for m in members if (probes.get(m) or {}).get("pw", 0) > 0]
                miss = [m for m in members if m not in pres]
                R("   %-24s %2d/%2d%s" % (dom, len(pres), len(members), "" if not miss else "   <-- INCOMPLETE"))
                for m in members:
                    pr = probes.get(m) or {}
                    R("      %-44s pw=%-3s cert=%-3s%s" % (m, pr.get("pw", "-"), pr.get("cert", "-"),
                                                          "" if pr.get("pw") else "   ABSENT"))
                if miss:
                    incomplete.append((inst, dom, len(pres), len(members), miss))
        if incomplete:
            insts = sorted(set(r[0] for r in incomplete))
            flags.add("CRITICAL" if len(insts) > 1 else "HIGH",
                      "Fleet API incomplete for %d domain(s) on %d instance(s)" % (len(incomplete), len(insts)),
                      ["%s/%s %d/%d missing: %s" % (i, d, p, t, ", ".join(m)) for i, d, p, t, m in incomplete])
            if len(insts) > 1:
                flags.add("INFO", "Same shape of incompleteness on more than one instance",
                          ["%s: %s" % (i, d) for i, d, _, _, _ in incomplete])

        # ---- Ops DB vs Ops API
        pres_db = o["data"].get("opsdb_host_presence") or {}
        if pres_db and incomplete:
            R("\n" + "-" * 78)
            R(" OPERATIONS DB (vcopsdb)  vs  OPERATIONS API   (missing hosts only)")
            R("-" * 78)
            nowhere, in_db = [], []
            for i, d, p, t, miss in incomplete:
                for m in miss:
                    hits = {tbl: cnt.get(m, 0) for tbl, cnt in pres_db.items() if cnt.get(m)}
                    R("   %-44s db tables mentioning host: %s" % (m, hits if hits else "NONE"))
                    (in_db if hits else nowhere).append("%s %s" % (m, hits) if hits else m)
            if nowhere:
                flags.add("HIGH", "%d host(s) absent from the fleet API and from every scanned "
                          "vcopsdb table (never collected)" % len(nowhere), nowhere)
            if in_db:
                flags.add("MEDIUM", "%d host(s) present in vcopsdb but absent from the fleet API"
                          % len(in_db), in_db)

        # ---- bridge log collection-cycle coverage
        la = o["data"].get("opslog_bridge_analysis") or {}
        keys = la.get("kv_keys") or []
        if keys:
            R("\n" + "-" * 78)
            R(" OPERATIONS COLLECTION CYCLE (vcops-bridge KV keys)   per expected host")
            R("-" * 78)
            latest = max(k["last_epoch"] for k in keys)
            recent = {}
            for k in keys:
                if k["type"] in ("ESXI", "ESX", "VCENTER") and k["last_epoch"] >= latest - 36 * 3600 * 1000:
                    recent.setdefault(k["fqdn"].lower(), []).append(k)
            R("   latest cycle epoch: %d (%s)" % (latest, datetime.datetime.fromtimestamp(
                latest / 1000, datetime.timezone.utc).isoformat()))
            R("   primary-vim-instance cancel lines: %s" % la.get("primary_cancel_total"))
            cyc_incomplete = []
            for inst, doms in expected.items():
                for dom, members in sorted(doms.items()):
                    members = [m.lower() for m in members]
                    written = [m for m in members if m in recent]
                    R("   %-14s %-24s written in last 36h: %2d/%2d" % (inst, dom, len(written), len(members)))
                    if len(written) < len(members):
                        cyc_incomplete.append("%s/%s %d/%d  never-written: %s" % (
                            inst, dom, len(written), len(members),
                            ", ".join(m for m in members if m not in recent)))
            if cyc_incomplete:
                flags.add("HIGH", "Collection cycle writes fewer hosts than SDDC Manager holds",
                          cyc_incomplete)
            if la.get("adapterinfo_failures"):
                flags.add("INFO", "AdapterInstanceInfo lookup failures in vcops-bridge",
                          ["%s x%d" % (k, v) for k, v in sorted(la["adapterinfo_failures"].items())][:8])

        # ---- VCF adapter objects: per-domain collection state (the Integration > Account view)
        vres = (o["data"].get("opsapi_resources_vcf") or {}).get("objects") or []
        if vres:
            R("\n" + "-" * 78)
            R(" VCF ADAPTER OBJECTS   (collection state per object)")
            R("-" * 78)
            bad = []
            for v in sorted(vres, key=lambda x: (str(x.get("kind")), str(x.get("name")))):
                sts = v.get("states") or []
                summary = ", ".join("%s/%s" % (x.get("state"), x.get("status")) for x in sts) or "no state"
                R("   %-28s %-34s %s" % (str(v.get("kind"))[:28], str(v.get("name"))[:34], summary))
                for x in sts:
                    if (x.get("state") not in (None, "STARTED")) or \
                       (x.get("status") not in (None, "DATA_RECEIVING")):
                        bad.append("%s %s: %s/%s %s" % (v.get("kind"), v.get("name"), x.get("state"),
                                                         x.get("status"), x.get("msg") or ""))
            if bad:
                flags.add("HIGH", "VCF adapter object(s) not started or not receiving data", bad)

        # ---- HostSystem resource state for the missing hosts
        hstates = (o["data"].get("opsapi_resources_hosts") or {}).get("states") or {}
        if incomplete and hstates:
            R("\n" + "-" * 78)
            R(" HOSTSYSTEM RESOURCE STATE   (missing hosts, from the vCenter adapter)")
            R("-" * 78)
            odd = []
            for i, d, p, t, miss in incomplete:
                for m in miss:
                    sts = hstates.get(m) or []
                    summary = ", ".join("%s/%s" % (x.get("state"), x.get("status")) for x in sts) or "not in inventory"
                    R("   %-44s %s" % (m, summary))
                    if not sts or any(x.get("status") != "DATA_RECEIVING" for x in sts):
                        odd.append("%s: %s" % (m, summary))
            if odd:
                flags.add("MEDIUM", "Missing host(s) also unhealthy or absent as HostSystem resources", odd)

        # ---- adapter -> collector placement
        amap = o["data"].get("opsapi_adapter_collectors") or []
        if amap:
            R("\n" + "-" * 78)
            R(" ADAPTER PLACEMENT   (which collector runs each adapter)")
            R("-" * 78)
            for a_ in sorted(amap, key=lambda x: (str(x.get("kind")), str(x.get("adapter")))):
                R("   %-24s %-50s -> %s" % (str(a_.get("kind"))[:24], str(a_.get("adapter"))[:50],
                                            a_.get("collector")))

        # ---- vimInstanceIds seen by the bridge, resolved against adapters
        vims = (o["data"].get("opslog_bridge_analysis") or {}).get("vim_instance_counts") or {}
        if vims:
            ad_by_id = {}
            for ad in rows(body(o, "opsapi_adapters")):
                ad_by_id[ad.get("id")] = ((ad.get("resourceKey") or {}).get("name"),
                                          (ad.get("resourceKey") or {}).get("adapterKindKey"))
            R("\n" + "-" * 78)
            R(" vimInstanceIds SEEN BY vcops-bridge   (resolved against the adapter registry)")
            R("-" * 78)
            unres = []
            for u, n in sorted(vims.items(), key=lambda kv: -kv[1]):
                nm, kd = ad_by_id.get(u, (None, None))
                R("   %s  x%-5d %s" % (u, n, ("%s [%s]" % (nm, kd)) if nm else "UNRESOLVED"))
                if not nm:
                    unres.append("%s x%d" % (u, n))
            if unres:
                flags.add("MEDIUM", "vimInstanceId(s) in the bridge log that resolve to no adapter", unres)

        # ---- staleness window: is the newest KV write inside the 12h threshold?
        la0 = o["data"].get("opslog_bridge_analysis") or {}
        if la0.get("kv_keys"):
            newest = max(k["last_epoch"] for k in la0["kv_keys"])
            scanned = la0.get("scanned_at_epoch_ms") or 0
            if scanned and scanned - newest > 12 * 3600 * 1000:
                flags.add("HIGH", "Newest collection record is older than the 12h staleness threshold",
                          ["newest %s, scanned %s" % (
                              datetime.datetime.fromtimestamp(newest / 1000, datetime.timezone.utc).isoformat(),
                              datetime.datetime.fromtimestamp(scanned / 1000, datetime.timezone.utc).isoformat())])

        # ---- other Operations nodes' bridge analysis
        for k, v in sorted(o["data"].items()):
            if k.startswith("opslog_bridge_analysis_") and isinstance(v, dict):
                node = k[len("opslog_bridge_analysis_"):]
                R("\n" + "-" * 78)
                R(" vcops-bridge ON %s" % node)
                R("-" * 78)
                if v.get("_error"):
                    R("   not collected: %s" % v["_error"])
                    continue
                kk = v.get("kv_keys") or []
                R("   files: %d   distinct keys: %d   primary-cancel lines: %s"
                  % (len(v.get("files_scanned") or []), len(kk), v.get("primary_cancel_total")))
                by_fq = collections.Counter(k_["fqdn"] for k_ in kk if k_.get("type") in ("ESXI", "ESX"))
                for fq, n in sorted(by_fq.items()):
                    R("   %-44s %d key(s)" % (fq, n))
                if kk:
                    flags.add("INFO", "Node %s also writes collection records (see report)" % node,
                              ["%d ESXi hosts, %d keys" % (len(by_fq), len(kk))])

        # ---- other-log error scan
        es = o["data"].get("opslog_error_scan") or {}
        if es.get("per_file"):
            R("\n" + "-" * 78)
            R(" OTHER OPERATIONS LOGS   (ERROR/WARN mentioning fleet/lcm/password/certificate/token)")
            R("-" * 78)
            for f, n in sorted(es["per_file"].items(), key=lambda kv: -kv[1])[:15]:
                R("   %-40s %d" % (f, n))
            for ln in (es.get("sample") or [])[:8]:
                R("     %s" % ln[:150])

        # ---- fleet lifecycle status through Operations
        fl = o["data"].get("opsapi_fleet_lifecycle") or {}
        if fl:
            R("\n" + "-" * 78)
            R(" FLEET LIFECYCLE   (as answered through the Operations endpoint)")
            R("-" * 78)
            for path, v in fl.items():
                R("   HTTP %-4s %s" % (v.get("status"), path))

        # ---- versions
        ver = body(o, "opsapi_version") or {}
        sol = rows(body(o, "opsapi_solutions"))
        R("\n" + "-" * 78)
        R(" VERSIONS")
        R("-" * 78)
        R("   Operations: %s" % (ver.get("releaseName") or ver.get("version") or str(ver)[:80]))
        for s_ in sol:
            nm = s_.get("name") or s_.get("id")
            if nm and re.search(r"infra|health|vcf|vsphere|vmware", str(nm), re.I):
                R("   %-50s %s" % (str(nm)[:50], s_.get("version")))
        for s in sddcs:
            sm = rows(body(s, "sddcapi_sddc_managers"))
            up = rows(body(s, "sddcapi_upgrades"))
            R("   SDDC %-14s %s   upgrades recorded: %d" % (
                s["meta"]["tag"], ", ".join(str(x.get("version")) for x in sm) or "?", len(up)))

        # ---- adapter primary flags vs CaSA roles
        ads = rows(body(o, "opsapi_adapters"))
        casa = (o["data"].get("opsapi_casa_roles") or {}).get("roles") or {}
        prim = collections.defaultdict(dict)
        for ad in ads:
            rk = ad.get("resourceKey") or {}
            kind, name = rk.get("adapterKindKey") or "", rk.get("name") or ""
            ids = {(i.get("identifierType") or {}).get("name"): i.get("value")
                   for i in rk.get("resourceIdentifiers") or []}
            if "LOCAL_PRIMARY" in ids or "PRIMARY" in ids:
                prim[kind][name] = ids.get("LOCAL_PRIMARY", ids.get("PRIMARY"))
        if prim:
            R("\n" + "-" * 78)
            R(" OPERATIONS ADAPTER PRIMARY FLAGS   vs   CaSA cluster roles")
            R("-" * 78)
            if casa:
                R("   CaSA: %s" % ", ".join("%s=%s" % kv for kv in sorted(casa.items())))
            master = next((n for n, r in casa.items() if r == "master"), None)
            wrong = []
            for kind in sorted(prim):
                R("   %s" % kind)
                for name, v in sorted(prim[kind].items()):
                    R("      %-60s %r" % (name, v))
                    if master and v == "enable" and master not in name:
                        wrong.append("%s: '%s' on %s, CaSA master is %s" % (kind, v, name, master))
            if wrong:
                flags.add("HIGH", "Adapter primary flag set on a node CaSA does not report as master", wrong)
            enabled_nodes = set()
            for k, d in prim.items():
                for n, v in d.items():
                    if v == "enable":
                        m = re.search(r"\(([^)]+)\)", n)
                        enabled_nodes.add(m.group(1) if m else n)
            if len(enabled_nodes) > 1:
                flags.add("HIGH", "Adapter kinds disagree on which node is primary",
                          sorted(enabled_nodes))

    # ---- SDDC vs SDDC
    if sddcs:
        R("\n" + "-" * 78)
        R(" SDDC MANAGER  %s  (shape, not size)" % ("vs SDDC MANAGER" if len(sddcs) > 1 else "profile"))
        R("-" * 78)
        shapes = {}
        for s in sddcs:
            tag = s["meta"]["tag"]
            hosts = rows(body(s, "sddcapi_hosts"))
            creds_all = rows(body(s, "sddcapi_credentials"))
            creds = rows(body(s, "sddcapi_credentials_esxi"))
            by_dom_hosts = collections.Counter((h.get("domain") or {}).get("name", "?") for h in hosts)
            by_dom_creds = collections.Counter(((c.get("resource") or {}).get("domainName") or "?") for c in creds)
            lock_tbl = s["data"].get("sddcdb_lock")
            locks = lock_tbl.get("rows", []) if isinstance(lock_tbl, dict) else []
            failed = [t for t in rows(body(s, "sddcapi_credential_tasks"))
                      if str(t.get("status", "")).upper() == "FAILED"]
            pools = rows(body(s, "sddcapi_network_pools"))
            used_pools = set((h.get("networkpool") or {}).get("name") for h in hosts)
            empty_pools = [p.get("name") for p in pools if p.get("name") not in used_pools]
            not_assigned = [dig(h, "fqdn") for h in hosts if str(h.get("status", "")).upper() != "ASSIGNED"]
            due = []
            for c in creds_all:
                pol = c.get("autoRotatePolicy") or {}
                ns = pol.get("nextSchedule")
                if ns:
                    try:
                        when = datetime.datetime.strptime(ns[:19], "%Y-%m-%dT%H:%M:%S")
                        days = (when - datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None)).days
                        if days <= warn_days:
                            due.append("%s %s in %dd (%s)" % ((c.get("resource") or {}).get("resourceName"),
                                                             c.get("username"), days, ns[:10]))
                    except Exception:
                        pass
            shapes[tag] = {"hosts_by_domain": dict(by_dom_hosts), "esxi_creds_by_domain": dict(by_dom_creds),
                           "creds_per_host": {d: round(by_dom_creds.get(d, 0) / n, 2) if n else 0
                                              for d, n in by_dom_hosts.items()},
                           "locks": len(locks), "failed_credential_tasks": len(failed),
                           "network_pools": len(pools), "empty_pools": empty_pools,
                           "hosts_not_assigned": [x for x in not_assigned if x],
                           "rotations_due": due, "db_tables": s["data"].get("sddcdb_summary") or {}}
            R("\n instance %s" % tag)
            for k in ("hosts_by_domain", "esxi_creds_by_domain", "creds_per_host"):
                R("   %-24s %s" % (k, shapes[tag][k]))
            R("   %-24s %s" % ("locks", shapes[tag]["locks"]))
            R("   %-24s %s" % ("failed cred tasks", shapes[tag]["failed_credential_tasks"]))
            R("   %-24s %s (empty: %s)" % ("network pools", shapes[tag]["network_pools"], empty_pools or "none"))
            R("   %-24s %s" % ("rotations due <=%dd" % warn_days, due or "none"))
            ntp = body(s, "sddcapi_ntp") or {}
            if isinstance(ntp, dict) and ntp.get("ntpServers"):
                R("   %-24s %s" % ("ntp", [x.get("ipAddress") for x in ntp.get("ntpServers") if isinstance(x, dict)]))
            if shapes[tag]["locks"]:
                flags.add("HIGH", "%s: %d row(s) in platform.lock" % (tag, shapes[tag]["locks"]),
                          [str({k: v for k, v in r.items() if k in ("resource_type", "resource_name",
                                                                    "lock_type", "resource_id")}) for r in locks[:6]])
            if failed:
                flags.add("MEDIUM", "%s: %d FAILED credential task(s)" % (tag, len(failed)),
                          ["%s %s" % (t.get("id"), t.get("name")) for t in failed[:6]])
            if empty_pools:
                flags.add("INFO", "%s: network pool(s) with no hosts" % tag, empty_pools)
            if shapes[tag]["hosts_not_assigned"]:
                flags.add("MEDIUM", "%s: host(s) not in ASSIGNED state" % tag, shapes[tag]["hosts_not_assigned"])
            if len(set(shapes[tag]["creds_per_host"].values())) > 1:
                flags.add("HIGH", "%s: ESXi credential rows per host differ by domain" % tag,
                          ["%s: %s" % (d, v) for d, v in shapes[tag]["creds_per_host"].items()])
            if due:
                flags.add("INFO", "%s: credential auto-rotation due within %d days" % (tag, warn_days), due)

        tags = list(shapes)
        for t2 in tags[1:]:
            a_t, b_t = shapes[tags[0]]["db_tables"], shapes[t2]["db_tables"]
            if not a_t or not b_t or "_error" in a_t or "_error" in b_t:
                continue   # one side did not collect; absence is not a difference
            only_a, only_b = sorted(set(a_t) - set(b_t)), sorted(set(b_t) - set(a_t))
            if only_a or only_b:
                flags.add("MEDIUM", "DB table sets differ between %s and %s" % (tags[0], t2),
                          ["only in %s: %s" % (tags[0], only_a[:10]), "only in %s: %s" % (t2, only_b[:10])])
            zero = [t for t in set(a_t) & set(b_t) if isinstance(a_t[t], int) and isinstance(b_t[t], int)
                    and (a_t[t] == 0) != (b_t[t] == 0)]
            if zero:
                flags.add("MEDIUM", "Tables empty on one instance and populated on the other",
                          ["%s: %s=%s %s=%s" % (t, tags[0], a_t[t], t2, b_t[t]) for t in sorted(zero)[:12]])

    # ---- Fleet Manager
    for f in fleets:
        summ = f["data"].get("fleetdb_summary") or {}
        R("\n" + "-" * 78)
        R(" FLEET MANAGER DB (vrlcm)  %s" % f["meta"].get("tag"))
        R("-" * 78)
        for t, n in sorted(summ.items()):
            R("   %-40s %s" % (t, n))
        rws = (f["data"].get("fleetdb_vm_lcops_sddc_manager") or {}).get("rows") or []
        if rws and ops:
            names = [r.get("sddcmanagerhostname") for r in rws]
            known = set(v.get("sddc") for v in (ops[0]["data"].get("opsapi_topology") or {}).get("instances", {}).values())
            stale = [n for n in names if n and n not in known]
            if stale:
                flags.add("HIGH", "Fleet Manager registers SDDC Manager(s) unknown to Operations", stale)

    # ---- best practices (from every bundle that carries bp_checks)
    checks = []
    for b_ in bundles:
        checks.extend(b_["data"].get("bp_checks") or [])
    if checks:
        R("\n" + "-" * 78)
        R(" BEST-PRACTICE CHECKS   (%d)" % len(checks))
        R("-" * 78)
        order = {"FAIL": 0, "WARN": 1, "INFO": 2, "PASS": 3, "SKIP": 4}
        tally = collections.Counter(c.get("result") for c in checks)
        R("   " + "   ".join("%s %d" % (k, tally.get(k, 0)) for k in ("FAIL", "WARN", "PASS", "INFO", "SKIP")))
        for c in sorted(checks, key=lambda x: (order.get(x.get("result"), 9), x.get("area", ""), x.get("check", ""))):
            if c.get("result") == "PASS":
                continue
            R("   [%-4s] %-14s %-58s %s" % (c.get("result"), c.get("area", "")[:14], c.get("check", "")[:58],
                                           (c.get("detail") or "")[:90]))
        R("   (PASS lines omitted here; all %d checks are in bp_checks.json)" % len(checks))
        fails = [c for c in checks if c.get("result") == "FAIL"]
        warns = [c for c in checks if c.get("result") == "WARN"]
        if fails:
            flags.add("HIGH", "%d best-practice check(s) failed" % len(fails),
                      ["%s: %s %s" % (c["area"], c["check"], c.get("detail", "")) for c in fails])
        if warns:
            flags.add("MEDIUM", "%d best-practice check(s) need attention" % len(warns),
                      ["%s: %s %s" % (c["area"], c["check"], c.get("detail", "")) for c in warns])

    # ---- output
    R("\n" + "=" * 78)
    R(" FLAGS")
    R("=" * 78)
    R(flags.render())
    R("")
    text = "\n".join(report)
    print(text)
    if not os.path.isdir(outdir):
        os.makedirs(outdir)
    stamp = time.strftime("%Y%m%d-%H%M%S")
    with open(os.path.join(outdir, "parity_report_%s.txt" % stamp), "w") as fh:
        fh.write(text)
    write_json(outdir, "parity_flags_%s" % stamp, flags.items)
    write_json(outdir, "parity_full_%s" % stamp,
               {"bundles": [{"meta": b["meta"], "path": b["path"], "data": b["data"]} for b in bundles]})
    log("report, flags and full JSON written to %s" % outdir)
    return text, flags


# ---------------------------------------------------------------- run (single command)
def cmd_run(a):
    """Everything from the Operations node in one go: Ops API + CaSA + DB + logs,
    every SDDC Manager over the network via API, compare, one tarball."""
    global DRY
    DRY = bool(a.plan)
    cfg = read_config(a.config or os.environ.get("FLEETPARITY_CONFIG"))
    role = detect_role()
    outroot = a.outdir or cfg.get("outdir") or "/tmp/fleetparity"
    stamp = time.strftime("%Y%m%d-%H%M%S")
    run_dir = os.path.join(outroot, "%s_run_%s" % (TOOL, stamp))
    if not DRY:
        os.makedirs(run_dir)

    print("=" * 70)
    print(" fleetparity %s  --  %s" % (__version__, os.uname()[1]))
    print(" read-only. two passwords will be asked; nothing is echoed." if not DRY
          else " plan only: nothing executed, no passwords asked")
    print("=" * 70)
    if role != "ops" and not DRY:
        log("NOTE: this does not look like a VCF Operations node (role=%s); "
            "DB and log layers will be skipped, API layers still run." % role)

    ops_host = a.host or cfg.get("ops_host") or "localhost"
    cfg["ops_user"] = os.environ.get("FLEETPARITY_OPS_USER") or cfg.get("ops_user") or "admin"
    cfg["sddc_user"] = (os.environ.get("FLEETPARITY_SDDC_USER") or cfg.get("sddc_user")
                        or "administrator@vsphere.local")
    print("\n[1/4] VCF Operations login")
    cfg["ops_password"] = secret("FLEETPARITY_OPS_PASSWORD", cfg, ["ops_password"],
                                 "      Enter the VCF Operations '%s' password: " % cfg["ops_user"])
    print("[2/4] SDDC Manager login (SSO)")
    sso_pw = secret("FLEETPARITY_SDDC_PASSWORD", cfg, ["sddc_password"],
                    "      Enter the '%s' password: " % cfg["sddc_user"])
    def optional(envname, key, prompt):
        if getattr(a, "skip_ssh", False) and key != "nsx_admin_password":
            return ""
        v = os.environ.get(envname) or cfg.get(key)
        if v or DRY:
            return v or ""
        return getpass.getpass("      %s (Enter to skip): " % prompt)

    if getattr(a, "skip_ssh", False):
        for k in ("ops_root_password", "sddc_ssh_password", "sddc_root_password", "esxi_root_password", "leaf_password"):
            cfg[k] = ""
            os.environ.pop("FLEETPARITY_" + k.upper(), None)
        for k in list(cfg):
            if k.startswith(("sddc_ssh_password_", "sddc_root_password_", "esxi_root_password_")):
                cfg[k] = ""
        print("      --skip-ssh: SSH layers disabled for this run.")
    print("      Optional credentials. Each one unlocks a layer; Enter skips it.")
    cfg["ops_root_password"] = optional("FLEETPARITY_OPS_ROOT_PASSWORD", "ops_root_password",
                                        "root password of the other VCF Operations nodes")
    cfg["sddc_ssh_user"] = cfg.get("sddc_ssh_user") or "vcf"
    cfg["sddc_ssh_password"] = optional("FLEETPARITY_SDDC_SSH_PASSWORD", "sddc_ssh_password",
                                        "SDDC Manager '%s' SSH password" % cfg["sddc_ssh_user"])
    if cfg["sddc_ssh_password"]:
        cfg["sddc_root_password"] = optional("FLEETPARITY_SDDC_ROOT_PASSWORD", "sddc_root_password",
                                             "SDDC Manager root password (for su)")
    cfg["esxi_root_password"] = optional("FLEETPARITY_ESXI_ROOT_PASSWORD", "esxi_root_password",
                                         "ESXi root password (jumbo-frame and host checks)")
    cfg["nsx_admin_user"] = cfg.get("nsx_admin_user") or "admin"
    cfg["nsx_admin_password"] = optional("FLEETPARITY_NSX_ADMIN_PASSWORD", "nsx_admin_password",
                                         "NSX Manager '%s' password" % cfg["nsx_admin_user"])
    if any(k.startswith("leaf_hosts_") and cfg.get(k) for k in cfg):
        cfg["leaf_user"] = cfg.get("leaf_user") or "cumulus"
        cfg["leaf_password"] = optional("FLEETPARITY_LEAF_PASSWORD", "leaf_password",
                                        "Leaf switch '%s' password (RTEP VLAN check)" % cfg["leaf_user"])
    cfg["nsx_gm_user"] = cfg.get("nsx_gm_user") or cfg["nsx_admin_user"]
    if cfg.get("nsx_gm_host"):
        cfg["nsx_gm_password"] = optional("FLEETPARITY_NSX_GM_PASSWORD", "nsx_gm_password",
                                          "NSX Global Manager %s '%s' password (Enter = same as NSX)"
                                          % (cfg["nsx_gm_host"], cfg["nsx_gm_user"])) or cfg["nsx_admin_password"]

    meta_base = {"site": cfg.get("site_name"), "tool_version": __version__,
                 "hostname": os.uname()[1], "euid": os.geteuid(), "mode": "run"}

    print("\n[3/4] Collecting")
    ops_dir = os.path.join(run_dir, "ops")
    if not DRY:
        os.makedirs(ops_dir)
    log("-- VCF Operations (%s)" % ops_host)
    ok = collect_ops(ops_dir, cfg, ops_host)
    if not ok:
        sys.exit("Operations login failed; nothing else can proceed. Check the admin password.")
    if not DRY:
        write_json(ops_dir, "bp_checks", [b_ for b_ in BP if b_["area"] == "ops"])
    finalize_bundle(ops_dir, dict(meta_base, role="ops", tag="ops", host=ops_host), tar=False)

    # discover SDDC Managers from the Ops adapter inventory; fall back to config
    topo = {}
    tp = os.path.join(ops_dir, "opsapi_topology.json")
    if os.path.exists(tp):
        with open(tp) as fh:
            topo = json.load(fh)
    targets = [(name, d.get("sddc")) for name, d in (topo.get("instances") or {}).items() if d.get("sddc")]
    if not targets:
        targets = [(SAFE.sub("_", h), h) for h in (cfg.get("sddc_hosts") or [])]
    if not targets:
        log("no SDDC Managers discovered; add sddc_hosts to the config if needed")
    bundle_dirs = [ops_dir]
    unreachable = []
    for inst, host in sorted(targets):
        tag = SAFE.sub("_", inst)
        sdir = os.path.join(run_dir, "sddc_" + tag)
        if not DRY:
            os.makedirs(sdir)
        log("-- SDDC Manager %s (%s)" % (inst, host))
        if not reachable(host):
            log("  ! %s is not reachable over HTTPS from this node" % host)
            unreachable.append((inst, host))
            write_json(sdir, "sddcapi_topology", {"tag": tag, "domains": {},
                                                  "_error": "unreachable from %s" % os.uname()[1]})
            continue
        c2 = dict(cfg)
        c2["sddc_password"] = scoped_secret(cfg, "sddc_password", tag, sso_pw,
                                            "'%s' password" % cfg["sddc_user"])
        c2["sddc_ssh_password"] = scoped_secret(cfg, "sddc_ssh_password", tag, cfg.get("sddc_ssh_password"),
                                                "'%s' SSH password" % cfg["sddc_ssh_user"])
        c2["sddc_root_password"] = scoped_secret(cfg, "sddc_root_password", tag, cfg.get("sddc_root_password"),
                                                 "root password (for su)")
        if collect_sddc(sdir, c2, host, tag):
            if not DRY:
                write_json(sdir, "bp_checks", [b_ for b_ in BP if b_["area"] == "sddc:%s" % tag])
            finalize_bundle(sdir, dict(meta_base, role="sddc", tag=tag, host=host), tar=False)
            bundle_dirs.append(sdir)
        else:
            unreachable.append((inst, host + " (login failed)"))

    # ---- component layer: TLS sweep, vCenters, ESXi hosts, NSX
    comp_dir = os.path.join(run_dir, "components")
    if not DRY:
        os.makedirs(comp_dir)
    all_hosts, host_ips, dom_of = {}, {}, {}
    for sd in bundle_dirs[1:]:
        t = _read_json(sd, "sddcapi_topology") if not DRY else None
        if t:
            for dn, hs in (t.get("domains") or {}).items():
                all_hosts[dn] = hs
                for h in hs:
                    dom_of[h] = dn
            host_ips.update(t.get("host_ips") or {})
    pool_mtu = {}
    for sd in bundle_dirs[1:]:
        hb = (_read_json(sd, "sddcapi_hosts") or {}).get("body") if not DRY else None
        pb = (_read_json(sd, "sddcapi_network_pools") or {}).get("body") if not DRY else None
        pools = {p_.get("name"): p_ for p_ in rows(pb)} if pb else {}
        for h in rows(hb) if hb else []:
            dn = (h.get("domain") or {}).get("name")
            pn = (h.get("networkpool") or {}).get("name")
            for n in (pools.get(pn) or {}).get("networks") or []:
                if n.get("type") in ("VMOTION", "VSAN") and n.get("mtu"):
                    pool_mtu[(dn, n.get("type"))] = n.get("mtu")
    vcenters = sorted(set((topo.get("vcenters") or [])))
    nsx = sorted(x for x in (topo.get("other_fqdn_identifiers") or []) if "nsx" in x.lower())
    sddc_fqdns = [h for _, h in targets]
    ops_nodes = []
    cr = _read_json(ops_dir, "opsapi_casa_roles") if not DRY else None
    if cr:
        dom = ".".join(os.uname()[1].split(".")[1:])
        ops_nodes = [n if "." in n else (n + "." + dom if dom else n) for n in (cr.get("roles") or {})]
    tls_targets = sorted(set([h for hs in all_hosts.values() for h in hs] + vcenters + nsx + sddc_fqdns + ops_nodes))
    log("-- TLS sweep: %d endpoints" % len(tls_targets))
    tls_sweep(comp_dir, tls_targets)
    # vCenter -> instance, so each vCenter is checked with its own instance's SSO password
    vc_inst = {}
    for sd in bundle_dirs[1:]:
        t = _read_json(sd, "sddcapi_topology") if not DRY else None
        vb = (_read_json(sd, "sddcapi_vcenters") or {}).get("body") if not DRY else None
        for v in rows(vb) if vb else []:
            fq = (dig(v, "fqdn") or "").lower()
            if fq and t:
                vc_inst[fq] = t.get("tag")
    log("-- vCenters: %d" % len(vcenters))
    for vc in vcenters:
        inst = vc_inst.get(vc)
        pw = _CRED_CACHE.get("sddc_password_%s" % inst, sso_pw) if inst else sso_pw
        collect_vcenter(comp_dir, vc, cfg["sddc_user"], pw)

    # ---- Global Manager placement: mirror the existing Local Manager node 1 on each site's management vCenter
    gm_place = {}
    if not DRY:
        for sd in bundle_dirs[1:]:
            t = _read_json(sd, "sddcapi_topology") or {}
            tg = t.get("tag")
            mvc = None
            for d_ in rows((_read_json(sd, "sddcapi_domains") or {}).get("body")):
                if str(d_.get("type", "")).upper() == "MANAGEMENT":
                    mvc = ((d_.get("vcenters") or [{}])[0] or {}).get("fqdn")
            if not (tg and mvc):
                continue
            ref = cfg.get("fed_reference_vm_%s" % tg)
            if not ref:
                nb_ = (_read_json(sd, "sddcapi_nsxt_clusters") or {}).get("body")
                for cl in rows(nb_) if nb_ else []:
                    nodes = cl.get("nodes") or []
                    if nodes:
                        ref = (nodes[0].get("fqdn") or nodes[0].get("name") or "").split(".")[0]
                    break
            if not ref:
                continue
            pw = _CRED_CACHE.get("sddc_password_%s" % tg, sso_pw)
            H = vcenter_session(mvc, cfg["sddc_user"], pw)
            if not H:
                bp("gm-placement", "%s management vCenter %s session" % (tg, mvc), "FAIL", "login failed")
                continue
            vcd = _read_json(comp_dir, "vcenter_%s" % mvc) or {}
            placement = vcd.get("placement") or {}
            info = vcenter_vm_placement(mvc, H, ref, placement)
            if not info:
                bp("gm-placement", "%s reference VM %s found on %s" % (tg, ref, mvc), "FAIL", "not found")
                continue
            bp("gm-placement", "%s reference VM %s found on %s" % (tg, ref, mvc), "PASS",
               "network %s, datastore %s, folder %s, cluster %s" % (info["networks"], info["datastore"], info["folder"], info["cluster"]))
            ds = next((d for d in placement.get("datastores") or [] if d.get("name") == info["datastore"]), None)
            n_gm = int(cfg.get("fed_gm_node_count") or 3)
            need = n_gm * 300 * 1024 ** 3
            if ds and isinstance(ds.get("free_space"), int):
                bp("gm-placement", "%s datastore %s has room for %d GM nodes" % (tg, info["datastore"], n_gm),
                   "PASS" if ds["free_space"] >= need else "FAIL",
                   "%.0f GB free, %d GB needed (300 GB per node, thin)" % (ds["free_space"] / 1024 ** 3, need / 1024 ** 3))
            prefix = "fed_gm" if tg == cfg.get("fed_gm_site") else ("fed_gm_standby" if tg == cfg.get("fed_gm_standby_site") else None)
            names = []
            if prefix:
                names = [cfg.get("%s_node%d_fqdn" % (prefix, i), "").split(".")[0] for i in range(1, n_gm + 1)]
                names = [n for n in names if n]
            for nm_ in names:
                bp("gm-placement", "%s no existing VM named %s on %s" % (tg, nm_, mvc),
                   "FAIL" if vcenter_vm_exists(mvc, H, nm_) else "PASS")
            gm_place[tg] = dict(info, vcenter=mvc)
        write_json(comp_dir, "gm_placement", gm_place)

    # ---- leaf switches: RTEP VLAN present, MTU, addressed (optional; needs leaf SSH creds)
    if cfg.get("leaf_password") or DRY:
        for sd in bundle_dirs[1:]:
            tg = (_read_json(sd, "sddcapi_topology") or {}).get("tag") if not DRY else None
            for tg2 in ([tg] if tg else [k[len("leaf_hosts_"):] for k in cfg if k.startswith("leaf_hosts_")]):
                hosts = cfg.get("leaf_hosts_%s" % tg2) or []
                if hosts:
                    log("-- leaves %s: %s" % (tg2, ", ".join(hosts)))
                    collect_leaves(comp_dir, hosts, cfg.get("leaf_user") or "cumulus", cfg.get("leaf_password") or "",
                                   cfg.get("fed_rtep_vlan_%s" % tg2), cfg.get("fed_rtep_cidr_%s" % tg2) or "0.0.0.0/0",
                                   int(cfg.get("fed_rtep_mtu") or 1700), tg2)
            if DRY:
                break

    if cfg.get("esxi_root_password") or DRY:
        log("-- ESXi hosts: %d (esxcli + jumbo-frame mesh)" % sum(len(v) for v in all_hosts.values()))
        collect_esxi(comp_dir, all_hosts, host_ips,
                     lambda d: scoped_secret(cfg, "esxi_root_password", d, cfg.get("esxi_root_password"),
                                             "ESXi root password"),
                     pool_mtu, int(time.time() * 1000))
    else:
        log("-- ESXi hosts: skipped (no root password given)")
    if nsx and (cfg.get("nsx_admin_password") or DRY):
        log("-- NSX managers: %d" % len(nsx))
        for n in nsx:
            collect_nsx(comp_dir, n, cfg["nsx_admin_user"],
                        scoped_secret(cfg, "nsx_admin_password", n, cfg["nsx_admin_password"],
                                      "NSX '%s' password" % cfg["nsx_admin_user"]))
    elif nsx:
        log("-- NSX managers: skipped (no admin password given)")
    # ---- planned appliances: DNS both ways, and nothing already answering on 443
    planned = cfg.get("planned_appliances") or []
    if planned and not DRY:
        log("-- planned appliances: %d" % len(planned))
        for entry in planned:
            if "=" not in str(entry):
                bp("planned", "entry %r" % entry, "SKIP", "expected fqdn=ip")
                continue
            f, ip = [x.strip() for x in str(entry).split("=", 1)]
            try:
                fwd = socket.gethostbyname(f)
                bp("planned", "%s resolves to %s" % (f, ip), "PASS" if fwd == ip else "FAIL", "A -> %s" % fwd)
            except Exception as e:
                bp("planned", "%s resolves to %s" % (f, ip), "FAIL", "no A record: %s" % str(e)[:60])
            try:
                rev = socket.gethostbyaddr(ip)[0]
                bp("planned", "%s reverse-resolves to %s" % (ip, f), "PASS" if rev.lower() == f.lower() else "WARN", "PTR -> %s" % rev)
            except Exception as e:
                bp("planned", "%s reverse-resolves to %s" % (ip, f), "FAIL", "no PTR: %s" % str(e)[:60])
            try:
                sk = socket.create_connection((ip, 443), timeout=3)
                sk.close()
                bp("planned", "%s not already in use" % ip, "FAIL", "something answers on 443")
            except Exception:
                bp("planned", "%s not already in use" % ip, "PASS", "no listener on 443")
    elif planned:
        PLAN.append("DNS  resolve + reverse + tcp/443 probe for %d planned appliance(s)" % len(planned))

    # ---- OVA on disk (optional)
    if cfg.get("fed_gm_ova_path"):
        lmv = None
        for fn in os.listdir(comp_dir) if os.path.isdir(comp_dir) else []:
            if fn.startswith("nsx_") and fn.endswith(".json"):
                lmv = ((_read_json(comp_dir, fn[:-5]) or {}).get("version") or {}).get("body", {}).get("product_version")
                if lmv:
                    break
        ov = check_ova(cfg["fed_gm_ova_path"], lmv)
        if not DRY:
            write_json(comp_dir, "gm_ova", ov)
            if ov.get("_error"):
                bp("gm-ova", "OVA readable at %s" % cfg["fed_gm_ova_path"], "FAIL", ov["_error"])
            else:
                bp("gm-ova", "OVA is %s %s" % (ov.get("product"), ov.get("version")), "INFO", "LM %s" % lmv)
                if "newer_or_equal_to_lm" in ov:
                    bp("gm-ova", "OVA version >= Local Manager version", "PASS" if ov["newer_or_equal_to_lm"] else "FAIL",
                       "%s vs %s" % (ov.get("version"), lmv))
                bp("gm-ova", "OVA offers the NSX Global Manager role", "PASS" if any("Global" in r for r in ov.get("roles", [])) else "WARN",
                   ov.get("roles") or "role list not parsed")
    # ---- existing Federation: read the Global Manager if one is configured
    gm_data = None
    if cfg.get("nsx_gm_host") and (cfg.get("nsx_gm_password") or DRY):
        log("-- NSX Global Manager: %s" % cfg["nsx_gm_host"])
        gm_data = collect_gm(comp_dir, cfg["nsx_gm_host"], cfg["nsx_gm_user"], cfg.get("nsx_gm_password") or "")
        if not DRY and gm_data and (gm_data.get("sites") or {}).get("status") == 200:
            lm_by_fqdn = {}
            for fn in sorted(os.listdir(comp_dir)):
                if fn.startswith("nsx_") and fn.endswith(".json"):
                    lm_by_fqdn[fn[4:-5]] = _read_json(comp_dir, fn[:-5]) or {}
            fed_health(cfg["nsx_gm_host"], gm_data, lm_by_fqdn)
            log("  federation health: %d check(s)" % sum(1 for b_ in BP if b_["area"] == "federation"))
        elif not DRY:
            log("  ! Global Manager did not answer (HTTP %s)" % (gm_data or {}).get("sites", {}).get("status"))

    # ---- federation readiness: one NSX Local Manager per instance, from its SDDC Manager
    fed_text = None
    if not DRY and (cfg.get("nsx_admin_password") or _CRED_CACHE) and str(cfg.get("fed_enabled", "true")).lower() != "false":
        fed_sites = collections.OrderedDict()
        for sd in bundle_dirs[1:]:
            t = _read_json(sd, "sddcapi_topology") or {}
            nb = (_read_json(sd, "sddcapi_nsxt_clusters") or {}).get("body")
            for cl in rows(nb) if nb else []:
                vip = (cl.get("vipFqdn") or "").lower()
                if vip:
                    nd = _read_json(comp_dir, "nsx_%s" % vip)
                    if nd:
                        fed_sites[t.get("tag")] = {"fqdn": vip, "data": nd}
                    break
        if len(fed_sites) < 2:
            # fall back to every NSX manager collected, keyed by FQDN
            for fn in sorted(os.listdir(comp_dir)) if os.path.isdir(comp_dir) else []:
                if fn.startswith("nsx_") and fn.endswith(".json"):
                    fq = fn[4:-5]
                    if fq not in [v["fqdn"] for v in fed_sites.values()]:
                        fed_sites[fq] = {"fqdn": fq, "data": _read_json(comp_dir, fn[:-5])}
            if len(fed_sites) >= 2:
                log("-- Federation readiness: instance mapping unavailable from /v1/nsxt-clusters; using NSX FQDNs")
        if len(fed_sites) >= 2:
            log("-- Federation readiness: %s" % " <-> ".join(fed_sites))
            tls_map = _read_json(comp_dir, "tls_sweep") or {}
            fed = fed_assess(cfg, fed_sites, tls_map)
            # per-instance context for the runbook: LM, DNS, NTP, management vCenter and cluster
            fed_ctx = {}
            for sd in bundle_dirs[1:]:
                t = _read_json(sd, "sddcapi_topology") or {}
                tg = t.get("tag")
                if not tg:
                    continue
                dnsb = (_read_json(sd, "sddcapi_dns") or {}).get("body") or {}
                ntpb = (_read_json(sd, "sddcapi_ntp") or {}).get("body") or {}
                prim, sec = dnsb.get("primaryDnsServer"), dnsb.get("secondaryDnsServer")
                prim = prim.get("ipAddress") if isinstance(prim, dict) else prim
                sec = sec.get("ipAddress") if isinstance(sec, dict) else sec
                dns_srv = [x for x in (prim, sec) if x]
                if not dns_srv:
                    lst = [x for x in (dnsb.get("dnsServers") or []) if isinstance(x, dict)]
                    dns_srv = [x.get("ipAddress") for x in sorted(lst, key=lambda x: not x.get("isPrimary"))]
                ntp_srv = [x.get("ipAddress") for x in (ntpb.get("ntpServers") or []) if isinstance(x, dict)]
                mvc, mcl = None, None
                for d_ in rows((_read_json(sd, "sddcapi_domains") or {}).get("body")):
                    if str(d_.get("type", "")).upper() == "MANAGEMENT":
                        mvc = ((d_.get("vcenters") or [{}])[0] or {}).get("fqdn")
                        mcl = ((d_.get("clusters") or [{}])[0] or {}).get("id")
                if not mvc:
                    vcs = rows((_read_json(sd, "sddcapi_vcenters") or {}).get("body"))
                    mvc = next((dig(v, "fqdn") for v in vcs if "m01" in str(v.get("domain", {}).get("name", "")).lower()), None) \
                          or (dig(vcs[0], "fqdn") if vcs else None)
                cls = rows((_read_json(sd, "sddcapi_clusters") or {}).get("body"))
                mcl = next((c_.get("name") for c_ in cls if "m01" in str(c_.get("name", "")).lower()), mcl)
                gp = (_read_json(comp_dir, "gm_placement") or {}).get(tg) or {}
                vct = (tls_map.get(mvc) or {}).get("sha256_fingerprint") if mvc else None
                fed_ctx[tg] = {"lm": fed_sites.get(tg, {}).get("fqdn"), "dns": dns_srv, "ntp": ntp_srv,
                               "mgmt_vcenter": mvc, "mgmt_cluster": mcl, "placement": gp, "vc_thumbprint": vct}
            # ---- north-south: uplinks and BGP for the stretched Tier-0
            if str(cfg.get("fed_ns_enabled", "true")).lower() != "false":
                try:
                    fed["uplinks"] = fed_uplinks(cfg, fed_sites, gm_data)
                    fed["checks"].extend(fed["uplinks"]["checks"])
                    fed["decisions"].extend(fed["uplinks"]["decisions"])
                    log("  north-south: %d uplink check(s), %d proposed address(es)"
                        % (len(fed["uplinks"]["checks"]), len(fed["uplinks"]["alloc"])))
                except Exception as e:
                    log("  ! north-south assessment skipped: %s" % e)
            fed_dir = os.path.join(run_dir, "federation")
            fed_text = fed_write(fed_dir, fed, fed_ctx, cfg)
            for x in fed["checks"]:
                if x["state"] in ("FAIL", "DECIDE"):
                    bp("federation", x["item"], "FAIL" if x["state"] == "FAIL" else "WARN", x["detail"])
            log("  %d check(s); worksheets in %s" % (len(fed["checks"]), fed_dir))
        elif fed_sites:
            log("-- Federation readiness: only one NSX Local Manager collected; skipped")
    if not DRY:
        write_json(comp_dir, "bp_checks", [b_ for b_ in BP if b_["area"] != "ops" and not b_["area"].startswith("sddc:")])
        finalize_bundle(comp_dir, dict(meta_base, role="components", tag="components"), tar=False)
        bundle_dirs.append(comp_dir)

    if DRY:
        print("\nPLAN (%d operations, none executed):" % len(PLAN))
        for p_ in PLAN:
            print("  " + p_)
        return

    print("\n[4/4] Comparing")
    text, flags = do_compare(bundle_dirs, cfg, run_dir)

    tgz = run_dir + ".tgz"
    with tarfile.open(tgz, "w:gz") as t:
        t.add(run_dir, arcname=os.path.basename(run_dir))
    print("\n" + "=" * 70)
    print(" DONE")
    print("=" * 70)
    print(" Flags raised : %d" % len(flags.items))
    if unreachable:
        print(" Not collected: %s" % ", ".join("%s (%s)" % u for u in unreachable))
        print("               -> on that SDDC Manager run: python3 fleetparity.py collect --tag <instance>")
    print(" Report       : %s" % os.path.join(run_dir, "parity_report_*.txt"))
    if fed_text:
        print(" Federation   : %s" % os.path.join(run_dir, "federation"))
        print("               readiness.txt  dns_records.csv  ip_allocation.csv  dci_firewall.csv  validation.txt")
        if os.path.exists(os.path.join(run_dir, "federation", "federation_runbook.txt")):
            print("               federation_runbook.txt  <- the ordered procedure with this environment's values filled in")
        if os.path.exists(os.path.join(run_dir, "federation", "northsouth_runbook.txt")):
            print("               northsouth_runbook.txt  <- Phases 8-11: uplinks and BGP on the stretched Tier-0")
    print("\n Archive to send:\n   %s\n" % tgz)
    sys.exit(1 if flags.items else 0)


def fed_collect_direct(cfg, outdir):
    """Collect only what the federation work needs: each NSX Local Manager and the Global
    Manager. No Operations, no SDDC Manager, no vCenter, no TLS sweep. Returns
    (sites OrderedDict, gm_data)."""
    lm_keys = sorted(k for k in cfg if k.startswith("nsx_lm_host_") and cfg.get(k))
    if not lm_keys:
        sys.exit("no Local Managers configured. Add to the config:\n"
                 "  nsx_lm_host_<site>: <fqdn>      e.g.  nsx_lm_host_site-a: nsx-lm-a.example.com")
    user = cfg.get("nsx_admin_user") or "admin"
    shared = secret("FLEETPARITY_NSX_ADMIN_PASSWORD", cfg, ["nsx_admin_password"],
                    "NSX Local Manager '%s' password: " % user)
    cfg["_lm_password"] = shared
    sites = collections.OrderedDict()
    for k in lm_keys:
        tag = k[len("nsx_lm_host_"):]
        fqdn = str(cfg[k]).strip()
        pw = scoped_secret(cfg, "nsx_admin_password", fqdn, shared, "NSX '%s' password" % user)
        log("-- NSX Local Manager %s (%s)" % (tag, fqdn))
        collect_nsx(outdir, fqdn, user, pw)
        d = _read_json(outdir, "nsx_%s" % fqdn)
        if not d:
            log("   ! not collected")
            continue
        sites[tag] = {"fqdn": fqdn, "data": d}
    gm_data = None
    gm_host = cfg.get("nsx_gm_host")
    if gm_host:
        gu = cfg.get("nsx_gm_user") or "admin"
        gp = secret("FLEETPARITY_NSX_GM_PASSWORD", cfg, ["nsx_gm_password"],
                    "Global Manager '%s' password: " % gu)
        log("-- NSX Global Manager (%s)" % gm_host)
        gm_data = collect_gm(outdir, gm_host, gu, gp)
        cfg["_gm_password"] = gp
        gm_backup_check("%s (active GM)" % gm_host, gm_data or {})
        sb = cfg.get("nsx_gm_standby_host") or cfg.get("fed_gm_standby_vip_fqdn")
        if sb and sb != gm_host:
            log("-- NSX Global Manager, standby (%s)" % sb)
            sbpw = scoped_secret(cfg, "nsx_gm_password", sb, gp, "Global Manager '%s' password" % gu)
            sbd = collect_gm_standby(outdir, sb, gu, sbpw)
            gm_backup_check("%s (standby GM)" % sb, sbd or {})
    return sites, gm_data


def fed_ns_diagnose(cfg, host, user, pw, paths, outdir=None, wait=90):
    """After a commit, wait for realization and report the REAL reason for anything that
    failed -- the Local Manager's own alarm text, not error code 511028. Read-only."""
    H = {"Authorization": "Basic " + base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()}
    G = "https://%s/global-manager/api/v1/global-infra" % host

    def realized(pth):
        st, b = http("%s/realized-state/status?intent_path=%s&include_enforced_status=true" % (G, pth),
                     headers=H, timeout=40)
        if not isinstance(b, dict) or not b:
            st, b = http("%s/realized-state/status?intent_path=%s" % (G, pth), headers=H, timeout=40)
        if not isinstance(b, dict):
            return st, None, []
        cs = (b.get("consolidated_status") or {}).get("consolidated_status")
        msgs = []
        for per in (b.get("consolidated_status_per_enforcement_point") or []):
            for a_ in (per.get("alarms") or []):
                m = a_.get("message") or a_.get("error_message")
                if m:
                    msgs.append("%s: %s" % (per.get("enforcement_point_id") or "?", m))
        for a_ in (b.get("alarms") or []):
            m = a_.get("message") or a_.get("error_message")
            if m:
                msgs.append(m)
        if not msgs:
            # The consolidated status carries no text for a rejected child object.
            # The enforced entity does. This is where 'Found errors in the request'
            # turns into a sentence someone can act on.
            st2, e = http("%s/realized-state/enforced-realized-entities?intent_path=%s" % (G, pth),
                          headers=H, timeout=40)
            for r_ in _res(e):
                for a_ in (r_.get("alarms") or []):
                    m = a_.get("message") or a_.get("error_message")
                    if m:
                        msgs.append("%s: %s" % (r_.get("realization_specific_identifier")
                                                or r_.get("entity_type") or "?", m))
        return st, cs, msgs

    log("waiting up to %ds for realization" % wait)
    deadline = time.time() + wait
    state = {}
    while True:
        pending = []
        for pth in paths:
            st, cs, msgs = realized(pth)
            state[pth] = {"http": st, "status": cs, "messages": msgs}
            if str(cs).upper() in ("", "NONE", "IN_PROGRESS", "UNKNOWN") or cs is None:
                pending.append(pth)
        if not pending or time.time() > deadline:
            break
        time.sleep(10)

    # broad alarm sweep as a fallback -- some rejections only surface here
    alarms = []
    for url in ("%s/realized-state/alarms?page_size=200" % G,
                "https://%s/api/v1/alarms?page_size=200&status=OPEN" % host):
        st, b = http(url, headers=H, timeout=40)
        for a_ in _res(b):
            alarms.append({"entity": a_.get("node_display_name") or a_.get("entity_id")
                                     or a_.get("intent_path"),
                           "feature": a_.get("feature_name") or a_.get("event_type"),
                           "message": a_.get("description") or a_.get("message")
                                      or a_.get("error_message"),
                           "status": a_.get("status") or a_.get("severity")})
    if outdir:
        write_json(outdir, "northsouth_realization",
                   {"per_object": state, "alarms": alarms})

    bad = {p_: v for p_, v in state.items()
           if str(v.get("status")).upper() not in ("SUCCESS", "REALIZED")}
    print("")
    print("=" * 74)
    print(" REALIZATION")
    print("=" * 74)
    ok = len(state) - len(bad)
    print(" %d of %d realized" % (ok, len(state)))
    for p_, v in sorted(bad.items()):
        print("  [%-11s] %s" % (str(v.get("status"))[:11], p_.rsplit("/", 1)[-1]))
        for m in (v.get("messages") or [])[:3]:
            print("                %s" % str(m)[:150])
    if bad and not any(v.get("messages") for v in bad.values()) and alarms:
        print("")
        print(" OPEN ALARMS (no per-object message was returned)")
        seen = set()
        for a_ in alarms:
            k = (a_.get("feature"), str(a_.get("message"))[:80])
            if k in seen:
                continue
            seen.add(k)
            print("  %-22s %s" % (str(a_.get("feature"))[:22], str(a_.get("message"))[:130]))
    if bad:
        print("")
        print(" Common causes, in the order they occur:")
        print("   - segment has no uplink teaming policy while the reference segment does")
        print("   - edge nodes not attached to the segment's VLAN transport zone")
        print("   - the location's locale service points at a different edge cluster")
        print("   Compare against the reference Tier-0's own uplink segments on the LM.")
    return state, alarms


# ---------------------------------------------------------------- verdict (read-only truth)
def fed_verdict(cfg, sites, gm_data, dp_nodes=None, realization=None):
    """Judge the federation as it stands. Proposes nothing, writes nothing.

    Everything here is derived from data already collected. It exists because the
    build is finished: the question stopped being 'what should we configure' and
    became 'is what they configured actually right'."""
    ck = []

    def c(area, item, state, detail=""):
        ck.append({"area": area, "item": item, "state": state, "detail": str(detail)[:400]})

    t0 = (cfg.get("fed_ns_tier0_name") or "").strip()
    dp_nodes = dp_nodes or {}

    # ---- Global Manager -------------------------------------------------
    gms = gm_data if isinstance(gm_data, dict) else {}
    for host, d in (gms.get("_by_host") or {"": gms}).items():
        if not isinstance(d, dict) or not d:
            continue
        label = host or (cfg.get("nsx_gm_host") or "global manager")
        bcfg = ((d.get("backup_config") or {}).get("body")) or {}
        if "backup_enabled" in bcfg:
            c("gm", "%s backup" % label, "PASS" if bcfg.get("backup_enabled") else "FAIL",
              "backup_enabled=%s -- SDDC Manager does not back up a Global Manager"
              % bcfg.get("backup_enabled"))
        lic = ((d.get("licenses") or {}).get("body")) or {}
        if "result_count" in lic:
            c("gm", "%s licence" % label, "PASS" if lic.get("result_count") else "FAIL",
              "%s licence(s) installed" % (lic.get("result_count") or 0))
        opened = _res((d.get("alarms") or {}).get("body"))
        hi = [a_ for a_ in opened if str(a_.get("severity", "")).upper() in ("CRITICAL", "HIGH")]
        if hi:
            c("gm", "%s open alarms" % label, "FAIL",
              "%d high or critical: %s" % (len(hi), "; ".join(
                  "%s/%s" % (a_.get("feature_name"), a_.get("event_type")) for a_ in hi[:4])))
        elif opened:
            c("gm", "%s open alarms" % label, "WARN",
              "%d medium or low: %s" % (len(opened), "; ".join(
                  "%s/%s on %s" % (a_.get("feature_name"), a_.get("event_type"),
                                   a_.get("node_display_name") or "?") for a_ in opened[:4])))
        else:
            c("gm", "%s open alarms" % label, "PASS", "none open")
        # Two we care about by name. A Global Manager sits outside VCF lifecycle,
        # so nothing else configures its syslog or its backup for you.
        vip = [a_ for a_ in opened if "instead of VIP" in str(a_.get("description")
                                                              or a_.get("message") or "")]
        if vip:
            c("gm", "%s locations registered on VIP" % label, "FAIL",
              "%d registered against a node -- re-register with the output of "
              "'get certificate cluster thumbprint', not 'get certificate api thumbprint'"
              % len(vip))
        syslog = [a_ for a_ in opened
                  if "logging" in str(a_.get("feature_name", "")).lower()]
        if syslog:
            c("gm", "%s remote logging" % label, "WARN",
              "%s -- VCF Operations does not cover a Global Manager, so set this with a "
              "Node Profile (System > Fabric > Profiles > Node Profiles > All NSX Nodes) "
              "rather than per node, or it gets missed on one"
              % "; ".join(str(a_.get("node_display_name") or "?") for a_ in syslog))
        degraded = [a_ for a_ in _res((d.get("alarms_recent") or {}).get("body"))
                    if "cluster degraded" in str(a_.get("event_type", "")).lower()]
        if degraded:
            still = [a_ for a_ in degraded if str(a_.get("status", "")).upper() == "OPEN"]
            c("gm", "%s cluster degraded history" % label,
              "FAIL" if still else "INFO",
              "%d events, %d still open -- expected while the cluster was being built; "
              "a rising count between runs is not" % (len(degraded), len(still)))
        gmn = _res((d.get("global_managers") or {}).get("body"))
        if gmn:
            act = [g.get("display_name") for g in gmn if str(g.get("mode")).upper() == "ACTIVE"]
            sby = [g.get("display_name") for g in gmn if str(g.get("mode")).upper() == "STANDBY"]
            c("gm", "%s standby" % label, "PASS" if sby else "WARN",
              "active=%s standby=%s" % (act or "none", sby or "none"))

    # ---- the placement rule, judged against the datapath -----------------
    clusters = {}
    for tag, sd in (sites or {}).items():
        for ec in _res(((sd.get("data") or {}).get("edge_clusters") or {}).get("body")):
            clusters[ec.get("display_name")] = [m.get("display_name")
                                                for m in (ec.get("members") or [])
                                                if m.get("display_name")]
    node_t0 = {}
    for node, v in dp_nodes.items():
        node_t0[node] = set(
            g["name"][3:] for g in (v.get("gateways") or [])
            if isinstance(g, dict) and g.get("type") == "SERVICE_ROUTER_TIER0"
            and str(g.get("name", "")).startswith("SR-"))

    locale = (gms.get("locale_services") or {})
    for pth, lss in locale.items():
        if "/tier-0s/" not in pth:
            continue
        gw = pth.rstrip("/").split("/")[-1]
        for ls_ in (lss or []):
            site_ = ls_.get("id") or "?"
            cname = (ls_.get("edge_cluster_path") or "").rstrip("/").split("/")[-1]
            rules = ((ls_.get("route_redistribution_config") or {})
                     .get("redistribution_rules") or [])
            c("routing", "%s route redistribution @ %s" % (gw, site_),
              "PASS" if rules else "FAIL",
              ", ".join(str(r_.get("route_redistribution_types")) for r_ in rules)
              or "none -- BGP will establish and advertise nothing")
            members = clusters.get(cname)
            if not dp_nodes:
                c("placement", "%s @ %s -> %s" % (gw, site_, cname), "SKIP",
                  "no datapath read; run with --verify-edges to judge Tier-0 placement")
            elif members is None:
                c("placement", "%s @ %s -> %s" % (gw, site_, cname), "WARN",
                  "edge cluster not found on any Local Manager collected")
            else:
                incumbent = sorted(set(x for m in members for x in node_t0.get(m, set()) if x != gw))
                on = [m for m in members if gw in node_t0.get(m, set())]
                if on and not incumbent:
                    c("placement", "%s @ %s -> %s" % (gw, site_, cname), "PASS",
                      "service router on %s" % ", ".join(on))
                elif incumbent:
                    c("placement", "%s @ %s -> %s" % (gw, site_, cname), "FAIL",
                      "cluster also backs Tier-0 %s. VCF 9.1 allows one Tier-0 per edge node."
                      % ", ".join(incumbent))
                else:
                    c("placement", "%s @ %s -> %s" % (gw, site_, cname), "FAIL",
                      "no service router on any member (%s)" % ", ".join(members))

    # ---- uplink interfaces, per site -------------------------------------
    for tag, sd in (sites or {}).items():
        d = sd.get("data") or {}
        ifs = [u for u in (gms.get("gm_uplinks") or [])
               if u.get("tier0") == t0 and u.get("locale") == tag]
        gm_nbrs = [n for n in (gms.get("gm_bgp_neighbors") or [])
                   if n.get("tier0") == t0 and n.get("locale") == tag]
        if not ifs:      # pre-federation fallback: an LM-owned gateway
            ifs = [u for u in (d.get("uplinks") or []) if u.get("tier0") == t0]
            gm_nbrs = [n for n in (d.get("bgp_neighbor_config") or []) if n.get("tier0") == t0]
        want_vl = [str(x) for x in (cfg.get("fed_ns_expect_vlans_%s" % tag) or [])]
        segs = {s.get("path"): s for s in _res((d.get("segments") or {}).get("body"))}
        segs.update({sg.get("path"): sg for sg in _res((gms.get("segments") or {}).get("body"))})
        vlans, bad_mtu, bad_urpf = set(), [], []
        for u in ifs:
            s_ = segs.get(u.get("segment_path")) or {}
            for v in (s_.get("vlan_ids") or []):
                vlans.add(str(v))
            if str(u.get("mtu") or "") != str(cfg.get("fed_uplink_mtu") or 9000):
                bad_mtu.append("%s=%s" % (u.get("name"), u.get("mtu")))
            want_urpf = str(cfg.get("fed_ns_urpf") or "NONE").upper()
            if str(u.get("urpf") or "").upper() not in (want_urpf, ""):
                bad_urpf.append("%s=%s" % (u.get("name"), u.get("urpf")))
        if ifs:
            c("uplink", "%s %s interfaces" % (tag, t0), "PASS", "%d external" % len(ifs))
            c("uplink", "%s uplink MTU" % tag, "FAIL" if bad_mtu else "PASS",
              ", ".join(bad_mtu) if bad_mtu else "all %s" % (cfg.get("fed_uplink_mtu") or 9000))
            c("uplink", "%s uRPF" % tag, "FAIL" if bad_urpf else "PASS",
              (", ".join(bad_urpf) + " -- an all-primary active-active Tier-0 egresses locally "
               "at both sites, so strict uRPF drops the asymmetric return path")
              if bad_urpf else "all %s" % (cfg.get("fed_ns_urpf") or "NONE"))
            if want_vl and vlans:
                c("uplink", "%s uplink VLANs" % tag,
                  "PASS" if sorted(want_vl) == sorted(vlans) else "FAIL",
                  "design %s, built %s" % (",".join(want_vl), ",".join(sorted(vlans))))
        else:
            c("uplink", "%s %s interfaces" % (tag, t0), "FAIL",
              "no external interfaces found for %s at this location" % t0)

        # As-built uplink addressing, checked against the design rather than derived.
        # The customer's as-built note is the source; these keys make it verifiable.
        ifs_by_vlan = {}
        for u in ifs:
            s_ = segs.get(u.get("segment_path")) or {}
            for v in (s_.get("vlan_ids") or []):
                ifs_by_vlan.setdefault(str(v), []).append(u)
        for vl in sorted(vlans):
            want_net = cfg.get("fed_ns_uplink_subnet_%s_vlan%s" % (tag, vl))
            want_peer = cfg.get("fed_ns_uplink_peer_%s_vlan%s" % (tag, vl))
            want_as = str(cfg.get("fed_ns_uplink_peer_as_%s_vlan%s" % (tag, vl)) or "").strip()
            if want_net:
                stray = []
                try:
                    net = ipaddress.ip_network(want_net)
                    for u in ifs_by_vlan.get(vl, []):
                        a = u.get("address")
                        if a and ipaddress.ip_address(a) not in net:
                            stray.append("%s=%s" % (u.get("name"), a))
                        elif a and str(u.get("prefix_len")) != str(net.prefixlen):
                            stray.append("%s=/%s" % (u.get("name"), u.get("prefix_len")))
                except Exception as e:
                    stray.append("could not parse %s: %s" % (want_net, e))
                c("uplink", "%s VLAN %s addressing" % (tag, vl),
                  "FAIL" if stray else "PASS",
                  ", ".join(stray) if stray else
                  "%d interfaces inside %s" % (len(ifs_by_vlan.get(vl, [])), want_net))
            if want_peer:
                nb = [n for n in gm_nbrs if n.get("peer") == want_peer]
                if not nb:
                    have = sorted(set(str(n.get("peer")) for n in gm_nbrs))
                    c("uplink", "%s VLAN %s peer" % (tag, vl), "FAIL",
                      "design peer %s not configured; found %s" % (want_peer, have or "none"))
                elif want_as and str(nb[0].get("remote_as")) != want_as:
                    c("uplink", "%s VLAN %s peer" % (tag, vl), "FAIL",
                      "peer %s configured with AS %s, design says %s"
                      % (want_peer, nb[0].get("remote_as"), want_as))
                else:
                    c("uplink", "%s VLAN %s peer" % (tag, vl), "PASS",
                      "%s AS %s" % (want_peer, nb[0].get("remote_as")))

        # named teaming policies must exist in the uplink profile of these edges
        # A named teaming policy only means anything if it exists in the uplink
        # profile bound to the edge nodes that carry this gateway. Finding the
        # name on some other profile elsewhere on the Local Manager proves nothing.
        _cl = (cfg.get("fed_edge_clusters_%s" % tag) or [None])[0]
        _members = set()
        for _e in _res((d.get("edge_clusters") or {}).get("body")):
            if _e.get("display_name") == _cl:
                _members = set(m.get("display_name") for m in (_e.get("members") or []))
        _profs = {p_.get("id"): p_ for p_ in _res((d.get("uplink_profiles") or {}).get("body"))}
        have, used = set(), set()
        for _tn in _res((d.get("transport_nodes") or {}).get("body")):
            if _tn.get("display_name") not in _members:
                continue
            for _sw in ((_tn.get("host_switch_spec") or {}).get("host_switches") or []):
                for _q in (_sw.get("host_switch_profile_ids") or []):
                    _p = _profs.get(str(_q.get("value") or "").split("/")[-1])
                    if not _p or not isinstance(_p.get("named_teamings"), list):
                        continue
                    used.add(_p.get("display_name"))
                    for _nt in _p["named_teamings"]:
                        if _nt.get("name"):
                            have.add(_nt["name"])
        for vl in sorted(vlans):
            want_tm = cfg.get("fed_ns_teaming_%s_vlan%s" % (tag, vl)) or cfg.get("fed_ns_teaming_%s" % tag)
            if not want_tm:
                continue
            if want_tm in have:
                c("uplink", "%s teaming '%s' for VLAN %s" % (tag, want_tm, vl), "PASS",
                  "defined in %s" % ", ".join(sorted(used)))
            else:
                c("uplink", "%s teaming '%s' for VLAN %s" % (tag, want_tm, vl), "WARN",
                  "not defined in the uplink profile of %s (%s). Those nodes offer %s, so "
                  "NSX falls back to the profile default and the VLAN is not pinned to a "
                  "specific physical uplink. Traffic works; the deterministic "
                  "VLAN-to-uplink mapping the name implies does not happen."
                  % (_cl or "the edge cluster", ", ".join(sorted(used)) or "no profile found",
                     ", ".join(sorted(have)) or "none"))

        # BGP: configured vs actually established
        dp_bgp = [v["bgp"] for nd, v in dp_nodes.items()
                  if v.get("site") == tag and v.get("bgp")]
        if dp_bgp:
            allnb = [x for b in dp_bgp for x in (b.get("neighbors") or [])]
            up = [x for x in allnb if str(x["state"]).upper().startswith("ESTAB")]
            quiet = [x for x in up if x.get("out_prefixes") == 0]
            c("bgp", "%s sessions (from the edge)" % tag,
              "PASS" if allnb and len(up) == len(allnb) else "FAIL",
              "%d of %d established" % (len(up), len(allnb)))
            if quiet:
                c("bgp", "%s prefixes advertised" % tag, "FAIL",
                  "%d established sessions advertising nothing" % len(quiet))
            elif up:
                c("bgp", "%s prefixes advertised" % tag, "PASS",
                  "in/out per session: %s" % ", ".join("%d/%d" % (x["in_prefixes"], x["out_prefixes"])
                                                       for x in up))
            continue
        nbrs = gm_nbrs
        est = [b for b in (d.get("bgp_status") or [])
               if b.get("tier0") == t0 and str(b.get("state", "")).upper().startswith("ESTAB")]
        if nbrs and est:
            c("bgp", "%s sessions established" % tag, "PASS", "%d of %d" % (len(est), len(nbrs)))
        elif nbrs:
            c("bgp", "%s sessions established" % tag, "WARN",
              "%d neighbours configured, none confirmed. The status endpoint 404s here, so "
              "'get bgp neighbor summary' inside the SR VRF is the only proof." % len(nbrs))

        # RTEP, and RTEP kept off the TEP subnet
        teps = (d.get("tn_teps") or {})
        for node, v in dp_nodes.items():
            if v.get("site") != tag:
                continue
            rt = [str(x).rsplit(".", 1)[0] for x in (v.get("rtep_ips") or [])]
            tp = [str(x).rsplit(".", 1)[0] for x in ((teps.get(node) or {}).get("teps") or [])]
            if not rt:
                c("rtep", "%s %s RTEP" % (tag, node), "FAIL", "no remote tunnel endpoint")
            elif set(rt) & set(tp):
                c("rtep", "%s %s RTEP subnet" % (tag, node), "FAIL",
                  "RTEP shares a subnet with the TEPs (%s); they must be separate"
                  % ", ".join(sorted(set(rt) & set(tp))))
            else:
                c("rtep", "%s %s RTEP" % (tag, node), "PASS", ", ".join(v.get("rtep_ips") or []))

    # ---- alarms, per Local Manager --------------------------------------
    # The LM alarm feed is where BGP Down, RTEP BFD and HA alarms actually live.
    # Severity decides the verdict: a soft capacity threshold is not an outage.
    for tag, sd in (sites or {}).items():
        d = sd.get("data") or {}
        opened = _res((d.get("alarms") or {}).get("body"))
        if not opened and not (d.get("alarms") or {}):
            c("alarms", "%s alarm feed" % tag, "SKIP", "not collected")
            continue
        hi = [a_ for a_ in opened
              if str(a_.get("severity", "")).upper() in ("CRITICAL", "HIGH")]
        med = [a_ for a_ in opened if a_ not in hi]

        def _lbl(a_):
            return "%s/%s on %s" % (a_.get("feature_name") or "?",
                                    a_.get("event_type") or "?",
                                    a_.get("node_display_name") or a_.get("entity_id") or "?")
        if hi:
            c("alarms", "%s open alarms" % tag, "FAIL",
              "%d high or critical: %s" % (len(hi), "; ".join(_lbl(a_) for a_ in hi[:4])))
        elif med:
            c("alarms", "%s open alarms" % tag, "WARN",
              "%d medium or low: %s" % (len(med), "; ".join(_lbl(a_) for a_ in med[:4])))
        else:
            c("alarms", "%s open alarms" % tag, "PASS", "none open")
        # History is context, not a verdict -- but a Tier-0 that keeps flapping
        # shows up here and nowhere else.
        recent = _res((d.get("alarms_recent") or {}).get("body"))
        bgpdown = [a_ for a_ in recent
                   if "bgp" in str(a_.get("event_type", "")).lower()
                   and "down" in str(a_.get("event_type", "")).lower()]
        if bgpdown:
            still = [a_ for a_ in bgpdown if str(a_.get("status", "")).upper() == "OPEN"]
            c("alarms", "%s BGP Down history" % tag,
              "FAIL" if still else "INFO",
              "%d BGP Down events, %d still open -- if this count keeps climbing between "
              "runs the sessions are flapping, not stable"
              % (len(bgpdown), len(still)))

    # ---- gateway configuration ------------------------------------------
    for t in _res((gms.get("tier0s") or {}).get("body")):
        if (t.get("display_name") or t.get("id")) != t0:
            continue
        ha = str(t.get("ha_mode") or "").upper()
        c("gateway", "%s HA mode" % t0, "INFO", ha or "unknown")
        if ha == "ACTIVE_ACTIVE":
            c("gateway", "%s stateful services" % t0, "WARN",
              "active-active cannot run stateful services. If a gateway firewall, NAT or load "
              "balancer is applied to this Tier-0, confirm it is stateless or move to "
              "active-standby. Gateway firewall policy is not collected -- verify by hand.")

    # ---- realization -----------------------------------------------------
    if isinstance(realization, dict) and realization.get("per_object"):
        po = realization["per_object"]
        bad = {k: v for k, v in po.items()
               if str(v.get("status")).upper() not in ("SUCCESS", "REALIZED")}
        c("realization", "stretched objects realized", "FAIL" if bad else "PASS",
          "%d of %d" % (len(po) - len(bad), len(po)))
        for k, v in list(bad.items())[:6]:
            c("realization", k.rsplit("/", 1)[-1], str(v.get("status")),
              "; ".join(str(m) for m in (v.get("messages") or [])) or "no message returned")
    return ck


def fed_asbuilt(cfg, sites, gm_data, dp_nodes=None):
    """Write what IS configured, from the Global Manager and the datapath.

    This replaces the plan runbook once the gateway exists. Everything here is
    read, not proposed, so it can go straight into a handover or a support case."""
    gms = gm_data if isinstance(gm_data, dict) else {}
    t0 = (cfg.get("fed_ns_tier0_name") or "").strip()
    dp_nodes = dp_nodes or {}
    L = []
    A = L.append
    A("NSX FEDERATION -- AS BUILT   %s" % now())
    A("Read from the Global Manager and the edge datapath. Nothing here is proposed.")
    A("")
    A("=" * 74)
    A(" GATEWAY")
    A("=" * 74)
    for t in _res((gms.get("tier0s") or {}).get("body")):
        if (t.get("display_name") or t.get("id")) != t0:
            continue
        A("  Tier-0            : %s" % t0)
        A("  HA mode           : %s" % t.get("ha_mode"))
        A("  Transit subnets   : %s" % ", ".join(t.get("transit_subnets") or []))
    for t in _res((gms.get("tier1s") or {}).get("body")):
        _id = t.get("id")
        _ecs = []
        for _p, _ls in (gms.get("locale_services") or {}).items():
            if "/tier-1s/" not in _p or _p.rstrip("/").split("/")[-1] != _id:
                continue
            for _l in (_ls or []):
                _ec = (_l.get("edge_cluster_path") or "").rstrip("/").split("/")[-1]
                _ecs.append("%s=%s" % (_l.get("id"), _ec or "no edge cluster"))
        _link = (gms.get("gm_tier1_links") or {}).get(_id) or t.get("tier0_path") or ""
        A("  Tier-1            : %s   type %s   %s"
          % (t.get("display_name") or _id, t.get("type") or "ROUTED",
             "; ".join(_ecs) if _ecs else "distributed only -- no service router"))
        if _link:
            A("                      linked to %s" % _link.rstrip("/").split("/")[-1])
        _t0ecs = set()
        for _p, _ls in (gms.get("locale_services") or {}).items():
            if "/tier-0s/" in _p and _p.rstrip("/").split("/")[-1] == t0:
                for _l in (_ls or []):
                    _t0ecs.add((_l.get("edge_cluster_path") or "").rstrip("/").split("/")[-1])
        _t1ecs = set(x.split("=", 1)[-1] for x in _ecs if "=" in x)
        if _t1ecs and _t0ecs and not (_t1ecs & _t0ecs):
            A("                      NOTE: its service routers are on %s while %s is on %s."
              % (", ".join(sorted(_t1ecs)), t0, ", ".join(sorted(_t0ecs))))
            A("                      Every north-south packet then crosses the TEP network")
            A("                      between edge clusters instead of staying on one node,")
            A("                      and the stretched Tier-1 depends on the cluster that")
            A("                      backs the LOCAL production Tier-0.")
    for pth, lss in (gms.get("locale_services") or {}).items():
        if "/tier-0s/" not in pth or pth.rstrip("/").split("/")[-1] != t0:
            continue
        for ls_ in (lss or []):
            rules = ((ls_.get("route_redistribution_config") or {})
                     .get("redistribution_rules") or [])
            A("  Location %-9s: edge cluster %s   redistribution %s"
              % (ls_.get("id"),
                 (ls_.get("edge_cluster_path") or "").rstrip("/").split("/")[-1] or "NONE",
                 ", ".join(str(r_.get("route_redistribution_types")) for r_ in rules)
                 or "NONE -- advertises nothing"))
    segs = {sg.get("path"): sg for sg in _res((gms.get("segments") or {}).get("body"))}
    A("")
    A("=" * 74)
    A(" UPLINK INTERFACES")
    A("=" * 74)
    A("  %-10s %-30s %-20s %-7s %-6s %s"
      % ("SITE", "NAME", "ADDRESS", "VLAN", "MTU", "uRPF"))
    for u in sorted((gms.get("gm_uplinks") or []), key=lambda x: (x.get("locale") or "",
                                                                 x.get("name") or "")):
        if u.get("tier0") != t0:
            continue
        sg = segs.get(u.get("segment_path")) or {}
        A("  %-10s %-30s %-20s %-7s %-6s %s"
          % (u.get("locale"), (u.get("name") or "")[:30],
             "%s/%s" % (u.get("address"), u.get("prefix_len")),
             ",".join(str(v) for v in (sg.get("vlan_ids") or [])) or "?",
             u.get("mtu"), u.get("urpf")))
    A("")
    A("=" * 74)
    A(" BGP")
    A("=" * 74)
    for k, v in sorted((gms.get("gm_bgp_config") or {}).items()):
        A("  %-10s local AS %s   enabled %s   ecmp %s"
          % (v.get("locale"), v.get("local_as"), v.get("enabled"), v.get("ecmp")))
    A("")
    A("  %-10s %-18s %-10s %-7s %-6s %s"
      % ("SITE", "PEER", "REMOTE AS", "MAXHOP", "BFD", "OUT FILTER"))
    for n in sorted((gms.get("gm_bgp_neighbors") or []), key=lambda x: (x.get("locale") or "",
                                                                       str(x.get("peer")))):
        if n.get("tier0") != t0:
            continue
        outf = [f for f in (n.get("filters") or []) if f.startswith("out_route_filters")]
        inf = [f for f in (n.get("filters") or []) if f.startswith("in_route_filters")]
        A("  %-10s %-18s %-10s %-7s %-6s %s"
          % (n.get("locale"), n.get("peer"), n.get("remote_as"), n.get("max_hop"),
             n.get("bfd"), "yes" if outf else "none"))
        A("  %-10s   sources: %s" % ("", ", ".join(n.get("sources") or []) or "auto"))
        for _f in outf + inf:
            A("  %-10s   %s" % ("", _f))
            _ref = _f.split()[-1] if " " in _f else _f
            _rm = (gms.get("gm_route_maps") or {}).get(_ref)
            if _rm:
                for _e in _rm["entries"]:
                    _pls = []
                    for _plp in _e["prefix_lists"]:
                        _pl = (gms.get("gm_prefix_lists") or {}).get(_plp)
                        if _pl:
                            _pls.append("%s [%s]" % (_pl["name"], "; ".join(
                                "%s %s" % (x["action"], x["network"]) for x in _pl["prefixes"])))
                        else:
                            _pls.append(_plp.rstrip("/").split("/")[-1])
                    A("  %-10s     %s %s%s"
                      % ("", _e["action"], ", ".join(_pls) or "any",
                         ("  set %s" % _e["set"]) if _e["set"] else ""))
            elif _ref.startswith("/"):
                A("  %-10s     (contents not collected)" % "")
    if dp_nodes:
        A("")
        A("=" * 74)
        A(" DATAPATH   (read from the edges, not the manager)")
        A("=" * 74)
        for node, v in sorted(dp_nodes.items()):
            srs = [g["name"] for g in (v.get("gateways") or [])
                   if isinstance(g, dict) and g.get("type") == "SERVICE_ROUTER_TIER0"]
            A("  %-18s %-10s RTEP %s" % (node, v.get("site"),
                                         ", ".join(v.get("rtep_ips") or []) or "none"))
            A("  %-18s %-10s Tier-0 SR: %s" % ("", "", ", ".join(srs) or "none"))
            for nb in ((v.get("bgp") or {}).get("neighbors") or []):
                A("  %-18s %-10s   %s AS%s %s in=%s out=%s"
                  % ("", "", nb["peer"], nb["remote_as"], nb["state"],
                     nb["in_prefixes"], nb["out_prefixes"]))
    A("")
    return "\n".join(L) + "\n"


def _asbuilt_uplinks(cfg, gms, tag, t0):
    """[(vlan, subnet, peer, peer_as, [(edge, address)])] for one site.

    Prefers what the Global Manager actually has. Falls back to the design values
    in the config so the document is still useful when the GM was not collected,
    and says which one it used."""
    segs = {sg.get("path"): sg for sg in _res((gms.get("segments") or {}).get("body"))}
    rows, src = [], "Global Manager"
    byvlan = {}
    for u in (gms.get("gm_uplinks") or []):
        if u.get("tier0") != t0 or u.get("locale") != tag:
            continue
        for v in ((segs.get(u.get("segment_path")) or {}).get("vlan_ids") or []):
            byvlan.setdefault(str(v), []).append(u)
    nbrs = [n for n in (gms.get("gm_bgp_neighbors") or [])
            if n.get("tier0") == t0 and n.get("locale") == tag]
    if not byvlan:
        src = "config (fed_ns_uplink_* -- the Global Manager was not collected)"
        for vl in [str(x) for x in (cfg.get("fed_ns_expect_vlans_%s" % tag) or [])]:
            rows.append((vl, cfg.get("fed_ns_uplink_subnet_%s_vlan%s" % (tag, vl)),
                         cfg.get("fed_ns_uplink_peer_%s_vlan%s" % (tag, vl)),
                         cfg.get("fed_ns_uplink_peer_as_%s_vlan%s" % (tag, vl)), []))
        return rows, src
    for vl in sorted(byvlan):
        ifs = sorted(byvlan[vl], key=lambda x: str(x.get("name")))
        net = None
        try:
            a0 = ifs[0]
            net = str(ipaddress.ip_network("%s/%s" % (a0["address"], a0["prefix_len"]),
                                           strict=False))
        except Exception:
            net = cfg.get("fed_ns_uplink_subnet_%s_vlan%s" % (tag, vl))
        peer, peer_as = None, None
        for n in nbrs:
            try:
                if net and ipaddress.ip_address(n["peer"]) in ipaddress.ip_network(net):
                    peer, peer_as = n["peer"], n.get("remote_as")
            except Exception:
                pass
        pairs = [((u.get("edge_path") or "").rsplit("/", 1)[-1] or u.get("name"),
                  u.get("address")) for u in ifs]
        rows.append((vl, net, peer, peer_as, pairs))
    return rows, src


def fed_switch_spec_asbuilt(cfg, sites, gms):
    """The physical-fabric document, written from what is configured.

    Not a build plan. Every session below already exists on the NSX side, so this
    is what the leaf configuration is confirmed against."""
    t0 = (cfg.get("fed_ns_tier0_name") or "").strip()
    local_as = cfg.get("fed_ns_local_as")
    L = []
    A = L.append
    A("SWITCH REQUIREMENTS -- AS BUILT   %s" % now())
    A("For %s. Read from the running configuration, not proposed." % t0)
    A("")
    A("These sessions are already configured on the NSX side. Use this to confirm the")
    A("switch side matches, and as the record of what was built.")
    A("")
    for tag in sites:
        rows, src = _asbuilt_uplinks(cfg, gms, tag, t0)
        A("=" * 74)
        A(" %s        (source: %s)" % (tag, src))
        A("=" * 74)
        if not rows:
            A("  nothing found for %s at this location" % t0)
            A("")
            continue
        for vl, net, peer, peer_as, pairs in rows:
            A("  VLAN %-6s subnet %-20s peer %s%s"
              % (vl, net or "<unknown>", peer or "<unknown>",
                 "  (peer AS %s)" % peer_as if peer_as else ""))
            if pairs:
                A("    NSX side, %d sessions, all local AS %s:" % (len(pairs), local_as))
                for edge, addr in pairs:
                    A("      %-18s %s" % (edge, addr))
            else:
                A("    edge addresses not available -- collect the Global Manager to list them")
            A("    the switch that owns %s needs one neighbour statement per address above,"
              % (peer or "the peer"))
            A("    all remote-as %s. Match the existing sessions: BFD off, max-hop 1," % local_as)
            A("    graceful-restart helper.")
            A("")
    A("=" * 74)
    A(" NOTES")
    A("=" * 74)
    A(" %s uses AS %s at BOTH sites. It is one gateway spanning two locations and NSX"
      % (t0, local_as))
    A(" has no per-location AS override, so the same remote-as appears at each site.")
    A("")
    A(" One peer per VLAN per site. Redundancy is ACROSS VLANs, not within one -- losing")
    A(" the switch that owns a VLAN takes that uplink out on every edge at once, and the")
    A(" design survives on the other VLAN.")
    A("")
    for tag in sites:
        for vl in [str(x) for x in (cfg.get("fed_ns_expect_vlans_%s" % tag) or [])]:
            tm = cfg.get("fed_ns_teaming_%s_vlan%s" % (tag, vl))
            if tm:
                A(" %s VLAN %s is intended to pin to %s. Confirm the uplink profile on those"
                  % (tag, vl, tm))
                A(" edge nodes defines that named teaming policy, or the pinning does not happen.")
    A("")
    return "\n".join(L) + "\n"


def fed_verify_runbook(cfg, sites, gms, dp_nodes=None):
    """Verification and handover steps for a gateway that is already built."""
    t0 = (cfg.get("fed_ns_tier0_name") or "").strip()
    t1 = cfg.get("fed_ns_tier1_name") or ""
    seg = cfg.get("fed_ns_test_segment") or ""
    sub = cfg.get("fed_ns_test_subnet") or ""
    L = []
    A = L.append
    A("NSX FEDERATION -- NORTH-SOUTH VERIFICATION   %s" % now())
    A("%s is built. These are the steps that prove it, and the record to keep." % t0)
    A("")
    A("=" * 74)
    A(" WHAT IS CONFIGURED")
    A("=" * 74)
    for tag in sites:
        rows, src = _asbuilt_uplinks(cfg, gms, tag, t0)
        A("  %s   (source: %s)" % (tag, src))
        for vl, net, peer, peer_as, pairs in rows:
            A("    VLAN %-5s %-20s -> peer %s AS %s   %d interfaces"
              % (vl, net or "?", peer or "?", peer_as or "?", len(pairs)))
    A("")
    A("  Route re-distribution, per location:")
    _types = set()
    for pth, lss in (gms.get("locale_services") or {}).items():
        if "/tier-0s/" not in pth or pth.rstrip("/").split("/")[-1] != t0:
            continue
        for ls_ in (lss or []):
            rules = ((ls_.get("route_redistribution_config") or {})
                     .get("redistribution_rules") or [])
            for r_ in rules:
                for _t in (r_.get("route_redistribution_types") or []):
                    _types.add(str(_t))
            A("    %-10s %s"
              % (ls_.get("id"),
                 ", ".join(str(r_.get("route_redistribution_types")) for r_ in rules)
                 or "NONE -- sessions will establish and advertise nothing"))
    if _types and _types <= {"TIER1_CONNECTED"}:
        A("    TIER1_CONNECTED carries Tier-1 connected segments only. Anything attached")
        A("    directly to the Tier-0, and any Tier-1 static or NAT route, is NOT")
        A("    advertised. Revisit this before production moves onto this gateway.")
    A("")
    A("=" * 74)
    A(" VERIFY")
    A("=" * 74)
    A("  1. On one edge per site, inside the Tier-0 SR VRF:")
    A("       get logical-routers            # note the VRF of SR-%s" % t0)
    A("       vrf <id>")
    A("       get bgp neighbor summary       # every session Estab")
    A("       get route bgp                  # WHICH prefixes are advertised")
    A("     The second command is the one still outstanding: confirm each site")
    A("     advertises its OWN subnet and not the other site's.")
    A("")
    if sub:
        A("  2. From a VM on %s at the first site:" % (seg or sub))
        A("       ping <its gateway>             # distributed router")
        A("       ping <the VM at the other site> # east-west")
        A("       ping <an address off-overlay>   # north-south")
        A("     Repeat from the second site.")
        A("")
    if t1:
        A("  3. Start a continuous north-south ping. On the Global Manager swap %s" % t1)
        A("     primary to the other location and SAVE. The ping keeps running and the VM")
        A("     keeps its address. Swap back.")
        A("")
    A("  4. Record every result with timestamps. The failover and DF-bit output is the")
    A("     deliverable, not the fact that it passed.")
    A("")
    A("=" * 74)
    A(" OPEN")
    A("=" * 74)
    _outf = sorted(set(f for n in (gms.get("gm_bgp_neighbors") or [])
                       if n.get("tier0") == t0
                       for f in (n.get("filters") or [])
                       if f.startswith("out_route_filters")))
    if _outf:
        A("  - Outbound filtering IS in place: %s"
          % ", ".join(sorted(set(f.rstrip("/").split("/")[-1] for f in _outf))))
        A("    Confirm with 'get route bgp' that each location advertises its own subnet.")
    else:
        A("  - %s carries no outbound prefix filter while the site-local Tier-0s carry" % t0)
        A("    their own. Decide whether to mirror it, and confirm with 'get route bgp'.")
    A("  - Global Manager backup and remote logging: the GM sits outside VCF lifecycle,")
    A("    so nothing configures either for you.")
    A("")
    return "\n".join(L) + "\n"


def fed_print_verdict(ck, outdir=None):
    order = {"FAIL": 0, "WARN": 1, "SKIP": 2, "INFO": 3, "PASS": 4}
    rows = sorted(ck, key=lambda x: (order.get(x["state"], 5), x["area"], x["item"]))
    w = min(max([len(r["item"]) for r in rows] + [20]), 46)
    print("")
    print("=" * 74)
    print(" FEDERATION VERDICT")
    print("=" * 74)
    for r in rows:
        it = r["item"] if len(r["item"]) <= w else "..." + r["item"][-(w - 3):]
        print(" %-5s %-11s %-*s %s" % (r["state"], r["area"], w, it, r["detail"][:150]))
    tally = collections.Counter(r["state"] for r in rows)
    print("-" * 74)
    print(" " + "   ".join("%s %d" % (k, tally[k]) for k in sorted(tally, key=lambda x: order.get(x, 5))))
    if outdir:
        write_json(outdir, "federation_verdict", rows)
    return tally


# ---------------------------------------------------------------- fedapply (the only writing command)
def cmd_fedapply(a):
    """Converge the stretched Tier-0's north-south configuration on the Global Manager.
    Plans by default and changes nothing; --commit writes. Idempotent: safe to re-run."""
    global DRY
    DRY = False
    cfg = read_config(a.config or os.environ.get("FLEETPARITY_CONFIG"))
    outdir = a.outdir or cfg.get("outdir") or "/tmp/fleetparity"
    outdir = os.path.join(outdir, "federation_%s" % time.strftime("%Y%m%d-%H%M%S"))
    os.makedirs(outdir)

    up = None
    if getattr(a, "replay", None):
        rd = a.replay
        if not os.path.isdir(rd):
            sys.exit("not a directory: %s" % rd)
        subs = sorted(glob.glob(os.path.join(rd, "federation_*")), reverse=True)
        dirs = subs if (subs and not glob.glob(os.path.join(rd, "gm_*.json"))) else [rd]

        def _pick(fn):
            for sub in dirs:
                fp_ = os.path.join(sub, fn)
                if os.path.exists(fp_):
                    with open(fp_) as fh:
                        return json.load(fh)
            return None

        fqdn_tag = {}
        for k in cfg:
            if k.startswith("nsx_lm_host_"):
                fqdn_tag[str(cfg[k]).lower()] = k[len("nsx_lm_host_"):]
        sites, gm_data = collections.OrderedDict(), {}
        for sub in dirs:
            for fp_ in sorted(glob.glob(os.path.join(sub, "nsx_*.json"))):
                fq = os.path.basename(fp_)[4:-5]
                tag = fqdn_tag.get(fq.lower()) or fq.split(".")[0]
                if tag in sites:
                    continue
                with open(fp_) as fh:
                    sites[tag] = {"fqdn": fq, "data": json.load(fh)}
            for fp_ in sorted(glob.glob(os.path.join(sub, "gm_*.json"))):
                if os.path.basename(fp_).startswith("gm_standby_") or gm_data:
                    continue
                with open(fp_) as fh:
                    gm_data = json.load(fh)
        if not sites:
            sys.exit("no nsx_*.json found under %s" % rd)
        log("replay: %d Local Manager(s), Global Manager %s, no network calls"
            % (len(sites), "yes" if gm_data else "no"))
        dp = _pick("edge_datapath.json") or {}
        _DP.update(dp.get("nodes") or {})
        up = fed_uplinks(cfg, sites, gm_data)
        up["_sites"], up["_gm"] = sites, gm_data
        up["_replay_realization"] = _pick("northsouth_realization.json")
        a.verify = True
        outdir = os.path.join(os.path.dirname(outdir), "replay_%s"
                              % time.strftime("%Y%m%d-%H%M%S"))
        os.makedirs(outdir, exist_ok=True)
    if a.bundle and up is None:        # optional: reuse a previous run instead of re-collecting
        for root, _d, files in os.walk(a.bundle):
            if "northsouth_full.json" in files:
                with open(os.path.join(root, "northsouth_full.json")) as fh:
                    up = json.load(fh)
                break
        if up is None:
            sys.exit("northsouth_full.json not found under %s" % a.bundle)
        log("using the north-south plan from %s" % a.bundle)
    if up is None:
        log("collecting from the NSX managers (federation only; no Operations, SDDC or vCenter)")
        sites, gm_data = fed_collect_direct(cfg, outdir)
        shared_lm_pw = cfg.get("_lm_password") or ""
        if len(sites) < 2:
            sys.exit("need two Local Managers; got %d. Check nsx_lm_host_<site> in the config."
                     % len(sites))
        up = fed_uplinks(cfg, sites, gm_data)
        up["_sites"], up["_gm"] = sites, gm_data
        cfg["_lm_password"] = cfg.get("_lm_password") or shared_lm_pw
        write_json(outdir, "northsouth_full",
                   {k: v for k, v in up.items() if not k.startswith("_")})
        # The runbook and the switch requirements are PLAN artefacts: "build these
        # interfaces, add these neighbours". They are derived from the reference
        # Tier-0. Writing them when the gateway is already built, or when the VLAN
        # guard has failed, produces a confident document describing the wrong
        # design -- and the switch file gets applied to the leaves.
        _built = [u for u in ((gm_data or {}).get("gm_uplinks") or [])
                  if u.get("tier0") == (cfg.get("fed_ns_tier0_name") or "")]
        _guard = [c for c in up["checks"]
                  if c["state"] == "FAIL" and "uplink VLANs" in c["item"]]
        _why = None
        if getattr(a, "verify", False):
            _why = None          # verify writes AS-BUILT versions of both, later
        elif _built:
            _why = ("%s already has %d external interfaces. The planner derives a plan "
                    "from the REFERENCE Tier-0, which is the untouched local gateway on "
                    "the old VLANs -- so any runbook it wrote here would describe a "
                    "design nobody is building. Use --verify to judge what exists."
                    % (cfg.get("fed_ns_tier0_name"), len(_built)))
        elif _guard:
            _why = ("The uplink VLAN guard failed: %s. A plan copied from the reference "
                    "Tier-0 would carry the wrong VLANs, peers and transport zone."
                    % _guard[0]["detail"][:200])
        if _why:
            for _f in ("northsouth_runbook.txt", "switch_requirements.txt"):
                with open(os.path.join(outdir, _f), "w") as f:
                    f.write("NO PLAN GENERATED   %s\n%s\n\n%s\n"
                            % (now(), "=" * 74, _why))
            log("no plan artefacts written: %s" % _why.split(".")[0])
        else:
            with open(os.path.join(outdir, "northsouth_runbook.txt"), "w") as f:
                f.write(fed_northsouth_runbook(cfg, up, {}))
            with open(os.path.join(outdir, "switch_requirements.txt"), "w") as f:
                f.write(fed_switch_spec(cfg, up))
        bad = [c for c in up["checks"] if c["state"] in ("FAIL", "DECIDE")]
        if bad:
            print("")
            for c in bad:
                _d = str(c["detail"])
                print(" [%-6s] %-40s %s" % (c["state"], c["item"][:40], _d[:110]))
                for _i in range(110, min(len(_d), 440), 110):
                    print(" %-6s  %-40s %s" % ("", "", _d[_i:_i + 110]))
    host = a.host or cfg.get("nsx_gm_host")
    if getattr(a, "replay", None):
        host, user, pw = host or "replay", cfg.get("nsx_gm_user") or "admin", ""
    elif not host:
        sys.exit("no Global Manager: pass --host or set nsx_gm_host in the config")
    user = cfg.get("nsx_gm_user") or "admin"
    pw = "" if getattr(a, "replay", None) else cfg.get("_gm_password") or secret(
        "FLEETPARITY_NSX_GM_PASSWORD", cfg,
                                           ["nsx_gm_password", "nsx_admin_password"],
                                           "Global Manager '%s' password: " % user)

    print("")
    print("=" * 74)
    print(" CONTACTED")
    print("=" * 74)
    for tag, sd in (up.get("_sites") or {}).items():
        d = sd.get("data") or {}
        tn = len([t for t in _res(_nb(d, "transport_nodes"))
                  if (t.get("node_deployment_info") or {}).get("resource_type") == "EdgeNode"])
        ecs = [e.get("display_name") for e in _res(_nb(d, "edge_clusters"))]
        print("  LM  %-8s %-28s edge nodes: %-3d clusters: %s"
              % (tag, sd.get("fqdn"), tn, ", ".join(x for x in ecs if x) or "none"))
    gmd = up.get("_gm") or {}
    if gmd:
        sitesn = [x.get("display_name") or x.get("id") for x in _res(_nb(gmd, "sites"))]
        print("  GM  active   %-28s locations: %s" % (host, ", ".join(sitesn) or "none"))
    sb = cfg.get("nsx_gm_standby_host") or cfg.get("fed_gm_standby_vip_fqdn")
    if sb and sb != host:
        print("  GM  standby  %-28s read-only health" % sb)
    print("")
    print("=" * 74)
    print(" fleetparity %s  fedapply  ->  %s" % (__version__, host))
    print(" Tier-0: %s" % (cfg.get("fed_ns_tier0_name") or "T0-STRETCHED"))
    print(" mode  : %s" % ("COMMIT -- objects will be created or updated" if a.commit
                           else ("VERIFY ONLY -- read-only, nothing is written"
                                 if getattr(a, "verify", False)
                                 else "PLAN ONLY -- nothing is written")))
    print("=" * 74)
    # ---- prerequisites first: nothing on a stretched Tier-0 realizes without them
    pre_ck, blockers, gaps = [], [], []
    if up.get("_sites"):
        try:
            pre_ck, blockers, gaps = fed_ns_preflight(cfg, up, up["_sites"], up.get("_gm"),
                                                      host, user, pw)
        except Exception as e:
            import traceback
            log("! pre-flight FAILED: %s" % e)
            log("  %s" % traceback.format_exc().strip().splitlines()[-2].strip())
            if a.commit:
                sys.exit("pre-flight could not run; refusing to commit blind. "
                         "Re-run without --commit and send the traceback.")
    if pre_ck:
        print("")
        print("=" * 74)
        print(" PRE-FLIGHT")
        print("=" * 74)
        for x in pre_ck:
            print("  [%-4s] %-52s %s" % (x["state"], x["item"][:52], x["detail"][:70]))

    if gaps and (a.fix_rtep or not a.commit):
        rows = fed_ns_fix_rtep(gaps, cfg, cfg.get("nsx_admin_user") or "admin",
                               cfg.get("_lm_password") or "",
                               commit=bool(a.fix_rtep and a.commit))
        print("")
        print(" RTEP REMEDIATION%s" % ("" if (a.fix_rtep and a.commit) else "  (plan only)"))
        for r in rows:
            print("  [%-9s] %-8s %-22s %s" % (r["action"], r["site"], r["name"],
                                              r.get("detail", "")[:60]))
        if a.fix_rtep and a.commit:
            blockers = [b for b in blockers if "RTEP missing" not in b]

    if blockers and a.commit and not a.fix_rtep:
        print("")
        print("=" * 74)
        print(" COMMIT BLOCKED -- prerequisites not met")
        print("=" * 74)
        for b in blockers:
            print("  - %s" % b)
        print("")
        print(" Re-run with --fix-rtep --commit to configure the missing RTEPs first,")
        print(" or configure them on the Local Manager and re-run.")
        sys.exit(1)

    if getattr(a, "no_edge_bgp", False):
        cfg["_no_edge_bgp"] = True
    if a.verify_edges and up.get("_sites"):
        euser = cfg.get("nsx_edge_ssh_user") or "admin"
        base_pw = (os.environ.get("FLEETPARITY_EDGE_PASSWORD")
                   or cfg.get("nsx_edge_password") or "")
        if not base_pw and not DRY:
            base_pw = getpass.getpass("      NSX edge '%s' password (Enter to skip): " % euser)
        if base_pw:
            try:
                ecks, _dp = fed_ns_verify_edges(
                    cfg, up["_sites"], outdir, euser,
                    lambda t: scoped_secret(cfg, "nsx_edge_password", t, base_pw,
                                            "edge '%s' password" % euser))
                _DP.update(_dp or {})
            except Exception as e:
                log("! edge verification failed: %s" % e)
                ecks = []
            print("")
            print("=" * 74)
            print(" EDGE DATAPATH   (SSH, read-only)")
            print("=" * 74)
            for x in ecks:
                if x["state"] == "INFO":
                    continue
                print("  [%-4s] %-50s %s" % (x["state"], x["item"][:50], x["detail"][:66]))
            bad = [x for x in ecks if x["state"] == "FAIL"]
            if bad:
                print("")
                print("  The manager's view and the edge datapath disagree. Objects that the")
                print("  Local Manager reports as realized are not present on the edge.")
            pre_ck.extend(ecks)
        else:
            print("  edge verification skipped (no password)")

    if a.verify:
        real = up.get("_replay_realization")
        rp = os.path.join(outdir, "northsouth_realization.json")
        if real is None and os.path.exists(rp):
            with open(rp) as fh:
                real = json.load(fh)
        verdict = fed_verdict(cfg, up.get("_sites") or {}, up.get("_gm") or {}, _DP, real)
        tally = fed_print_verdict(verdict, outdir)
        _s, _g = up.get("_sites") or {}, up.get("_gm") or {}
        for _name, _fn in (("federation_asbuilt.txt",
                            lambda: fed_asbuilt(cfg, _s, _g, _DP)),
                           ("switch_requirements.txt",
                            lambda: fed_switch_spec_asbuilt(cfg, _s, _g)),
                           ("northsouth_runbook.txt",
                            lambda: fed_verify_runbook(cfg, _s, _g, _DP))):
            try:
                with open(os.path.join(outdir, _name), "w") as f:
                    f.write(_fn())
                print("   %s" % os.path.join(outdir, _name))
            except Exception as e:
                log("%s not written: %s" % (_name, e))
        print("")
        print(" Bundle: %s" % outdir)
        sys.exit(1 if tally.get("FAIL") else 0)

    if a.diagnose:
        paths = ["/global-infra" + o["path"] for o in fed_ns_desired(cfg, up)
                 if o["kind"] in ("segment", "interface")]
        fed_ns_diagnose(cfg, host, user, pw, paths, outdir,
                        wait=int(cfg.get("fed_ns_realize_wait") or 30))
        print("")
        print(" Detail: %s" % os.path.join(outdir, "northsouth_realization.json"))
        sys.exit(0)
    results, blocked = fed_ns_apply(cfg, up, host, user, pw, commit=bool(a.commit), outdir=outdir)

    tally = collections.Counter(r["action"] for r in results)
    last = None
    for r in results:
        if r["kind"] != last:
            print("-" * 74)
            last = r["kind"]
        print(" [%-9s] %-9s %-8s %-40s %s"
              % (r["action"], r["kind"], r["site"], r["id"][:40], (r.get("detail") or "")[:60]))
    print("=" * 74)
    print(" " + "   ".join("%s %d" % (k, tally.get(k, 0))
                           for k in ("ADD", "UPDATE", "UNCHANGED", "BLOCKED", "ERROR")))
    if blocked:
        print("")
        print(" BLOCKED objects need a value this run could not resolve. Fix the config or the")
        print(" environment and re-run; nothing partially applied.")
    if not a.commit and (tally.get("ADD") or tally.get("UPDATE")):
        print("")
        print(" Re-run with --commit to apply. Re-running after that reports UNCHANGED.")
    print("")
    if a.commit and not tally.get("ERROR"):
        paths = ["/global-infra" + r["path"] for r in results
                 if r["action"] in ("ADD", "UPDATE") and r["kind"] in ("segment", "interface")]
        if paths:
            try:
                fed_ns_diagnose(cfg, host, user, pw, paths, outdir,
                                wait=int(cfg.get("fed_ns_realize_wait") or 90))
            except Exception as e:
                log("realization check skipped: %s" % e)
    fedbp = [b_ for b_ in BP if b_["area"] == "federation" and b_["result"] in ("FAIL", "WARN")]
    if fedbp:
        print("")
        print(" GLOBAL MANAGER HEALTH")
        for b_ in fedbp:
            print("  [%-4s] %-46s %s" % (b_["result"], b_["check"][:46], b_["detail"][:60]))
    print("")
    print(" Switch side is unchanged by this command.")
    for _f in ("switch_requirements.txt", "northsouth_runbook.txt"):
        _p = os.path.join(outdir, _f)
        if os.path.exists(_p):
            with open(_p) as _fh:
                if _fh.read(18) == "NO PLAN GENERATED ":
                    continue
            print("   %s" % _p)
    sys.exit(2 if tally.get("ERROR") else (1 if blocked else 0))


# ---------------------------------------------------------------- migpath (the second writing command)
# Blue Global Manager segment -> Green Global Manager segment with the SAME id, joined by an
# edge bridge on each side over a transit VLAN. Blue's gateway serves both estates until
# cutover; cutover turns Blue's segment Connectivity OFF, then Green's ON (KB 330523 order).
#
# Objects this command creates are PATCHed with a complete body. Objects it only changes --
# every Blue segment, Green segments on re-runs, prefix lists -- are read, changed in memory
# and PUT back whole with their _revision. Nothing it does not manage is ever dropped,
# whether or not partial patch is enabled on the manager.

MIG_COLS = ("site", "segment", "source", "subnet", "gateway", "blue_tier1", "transit_vlan",
            "path", "wave", "notes")
MIG_PATHS = ("BRIDGE", "REVIEW", "SKIP", "READDRESS")
MIG_MANAGED = ("display_name", "connectivity_path", "subnets", "advanced_config",
               "bridge_profiles", "edge_paths", "ha_mode", "failover_mode", "prefixes", "tags")


def gm_put(host, H, sub, body, timeout=60):
    return http("https://%s/global-manager/api/v1/global-infra%s" % (host, sub),
                method="PUT", headers=H, body=body, timeout=timeout)


def gm_delete(host, H, sub, timeout=60):
    return http("https://%s/global-manager/api/v1/global-infra%s" % (host, sub),
                method="DELETE", headers=H, timeout=timeout)


def _mig_H(user, pw):
    return {"Authorization": "Basic " + base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()}


def _mig_rel(path):
    p = str(path or "")
    return p[len("/global-infra"):] if p.startswith("/global-infra") else p


def _mig_items(v):
    if v in (None, ""):
        return []
    if isinstance(v, (list, tuple)):
        return [str(x).strip() for x in v if str(x).strip()]
    return [x.strip() for x in str(v).split(",") if x.strip()]


def _mig_vlans(v):
    out = []
    for it in _mig_items(v):
        m = re.fullmatch(r"(\d+)\s*-\s*(\d+)", it)
        if m:
            lo, hi = sorted((int(m.group(1)), int(m.group(2))))
            out.extend(range(lo, hi + 1))
        elif it.isdigit():
            out.append(int(it))
    return out


def _mig_key(cfg, key, site, default=None):
    for k in ("%s_%s" % (key, site), key):
        v = cfg.get(k)
        if v not in (None, "", []):
            return v
    return default


def _mig_true(v):
    return str(v).strip().lower() in ("1", "true", "yes", "on")


def _mig_list(host, H, sub, cap=50):
    out, cursor = [], None
    for _ in range(cap):
        s = sub
        if cursor:
            s += ("&" if "?" in s else "?") + "cursor=" + urllib.parse.quote(str(cursor))
        st, b = gm_get(host, H, s)
        if st != 200:
            return None, st
        out.extend(_res(b))
        cursor = b.get("cursor") if isinstance(b, dict) else None
        if not cursor:
            break
    return out, 200


def _mig_named(objs, name):
    """Display name first, id only as a fallback: a Tier-0 displayed as one site's can carry the
    other site's id (seen in the field), so matching both at once can pick the wrong object."""
    n = str(name or "").strip().lower()
    hit = [o for o in objs or [] if str(o.get("display_name") or "").strip().lower() == n]
    return hit or [o for o in objs or [] if str(o.get("id") or "").strip().lower() == n]


def _mig_entry_key(e):
    return (_mig_rel(e.get("bridge_profile_path")), tuple(sorted(str(v) for v in e.get("vlan_ids") or [])),
            _mig_rel(e.get("vlan_transport_zone_path")))


def _mig_view(o):
    return json.dumps({k: o.get(k) for k in MIG_MANAGED if k in o}, sort_keys=True, default=str)


def _mig_match(items, sid, name, subnet, tier1=None):
    """The first of `items` that names this segment: its id, its name, a CIDR holding its subnet, or
    t1:<Blue Tier-1> (every segment on that Tier-1, whatever its subnet); None when none does."""
    try:
        net = ipaddress.ip_network(str(subnet), strict=False) if subnet else None
    except ValueError:
        net = None
    for x in items:
        if x in (sid, name):
            return x
        if x.lower().startswith("t1:"):
            if tier1 and x[3:].strip().lower() == str(tier1).strip().lower():
                return x
            continue
        if net is not None and "/" in x:
            try:
                sc = ipaddress.ip_network(x, strict=False)
            except ValueError:
                continue
            if net.version == sc.version and net.network_address in sc and net.prefixlen >= sc.prefixlen:
                return x
    return None


def mig_blue_site_segments(host, H):
    """(ids of the global segments that exist at this Blue location, [segments local to its Local Manager],
    why not): what is at the site, as the site's own Local Manager has it. The Global Manager pushes each
    Local Manager only the global objects that span its location. A segment local to the Local Manager is
    not on the Global Manager, so this tool does not migrate it; it is listed so nothing at the site goes unseen."""
    def pages(path):
        out, cur = [], None
        for _i in range(200):
            url = "https://%s/policy/api/v1%s?page_size=1000%s" % (
                host, path, ("&cursor=%s" % urllib.parse.quote(str(cur))) if cur else "")
            st_, b = http(url, headers=H, timeout=60)
            if st_ != 200 or not isinstance(b, dict):
                return None, st_
            out += b.get("results") or []
            cur = b.get("cursor")
            if not cur or not b.get("results"):
                break
        return out, 200
    g, st1 = pages("/global-infra/segments")
    if g is None:
        return None, [], "the global segments on %s are not readable (HTTP %s)" % (host, st1)
    loc, _st2 = pages("/infra/segments")
    loc = [x for x in loc or [] if not x.get("_system_owned")
           and any((sub or {}).get("gateway_address") for sub in x.get("subnets") or [])]
    return {x.get("id") for x in g if x.get("id")}, loc, None


def mig_rows(cfg, site, blue, green, st, test_ids=()):
    """The plan, derived on every run instead of kept in a file. Each Blue segment as Blue's Global
    Manager has it now; what the config decides: mig_scope_<site> (bridged) and mig_skip_<site> (never),
    each a list of CIDRs, segment names or ids; and its transit VLAN: the one NSX bridges it on, else the
    one this tool gave it (in the state), else, for a segment of the scope, the next free VLAN of the pool.
    A segment gone from Blue keeps its row while NSX holds anything of its migration. What is new, changed
    or gone on Blue since the last run is reported. Returns (rows, checks); nothing from a partial read."""
    checks = []

    def c(item, state, detail=""):
        checks.append({"area": "plan", "item": item, "state": state, "detail": str(detail)[:400]})

    def some(xs, k=6):
        return "; ".join(xs[:k]) + (" (+%d more)" % (len(xs) - k) if len(xs) > k else "")

    unread = (mig_unread("Blue", blue, ("segments", "tier1s", "bridge_profiles"))
              + mig_unread("Green", green, ("segments", "bridge_profiles")))
    if unread:
        c("segments from NSX", "FAIL", "not read: %s. Nothing is planned from a partial read: run again"
          % ", ".join(unread))
        return [], checks
    t1n = {t.get("path"): t.get("display_name") for t in blue["tier1s"]}
    inv = st.setdefault("inventory", {})
    first, day = not inv, now()[:10]
    scope_items = _mig_items(_mig_key(cfg, "mig_scope", site))
    skip_items = _mig_items(_mig_key(cfg, "mig_skip", site))
    want_all = any(x.lower() == "all" for x in scope_items)       # every segment Blue has at this site
    scope_items = [x for x in scope_items if x.lower() != "all"]
    at_site = blue.get("site_segments")                           # None when the site's Local Manager was not read
    if want_all and at_site is None:
        c("mig_scope_%s: all" % site, "FAIL", "what exists at %s is not known (%s): nothing is planned for all" % (
            blue.get("here") or site, blue.get("site_why") or "not read"))
    gseg = {s_.get("id"): s_ for s_ in green.get("segments") or []}
    bseg = {s_.get("id"): s_ for s_ in blue.get("segments") or []}
    gbp, bbp = mig_bp_paths(cfg, site, green, blue)
    live = mig_live_vlans(cfg, site, green, blue)
    vseg = {int(it) for d_ in (green, blue) for s_ in d_.get("segments") or []
            for it in _mig_items(s_.get("vlan_ids")) if it.isdigit()}
    pool = set(_mig_vlans(_mig_key(cfg, "mig_transit_vlans", site)))
    unusable = set(_mig_vlans(_mig_key(cfg, "mig_infra_vlans", site))) | vseg
    free = _mig_free_vlans(cfg, site, st, live, vseg)
    held = {v: sid_ for sid_, d_ in live.items() for v in d_.values()}      # VLAN -> the segment NSX bridges on it
    rows, new, changed, gone = [], [], [], []
    for seg in sorted(blue["segments"], key=lambda x: str(x.get("display_name") or x.get("id"))):
        d = _mig_classify(seg, t1n)
        sid = d["segment"]
        if not sid:
            continue
        rec = {"name": seg.get("display_name") or sid, "source": d["source"], "subnet": d["subnet"],
               "gateway": d["gateway"], "blue_tier1": d["blue_tier1"]}
        old = inv.get(sid)
        if old is None:
            inv[sid] = dict(rec, first_seen=day)
            new.append(sid)
        else:
            diffs = ["%s %s -> %s" % (k, old.get(k) or "-", rec[k] or "-")
                     for k in ("subnet", "gateway", "source", "blue_tier1", "name") if (old.get(k) or "") != (rec[k] or "")]
            ev = (["back on Blue %s" % day] if old.get("gone") else []) + (
                ["changed on Blue %s: %s" % (day, ", ".join(diffs))] if diffs else [])
            if diffs:
                changed.append("%s: %s" % (sid, ", ".join(diffs)))
            if ev:
                old["events"] = ((old.get("events") or []) + ev)[-20:]
            old.pop("gone", None)
            old.update(rec)
        rows.append(dict(d, name=rec["name"]))
    for sid in sorted(set(inv) - set(bseg)):
        old = inv[sid]
        if not old.get("gone"):
            old["gone"] = day
            gone.append(sid)
        if sid in gseg or (st["segments"].get(sid) or {}).get("status") not in (None, "planned", "absent"):
            rows.append({"segment": sid, "name": old.get("name") or sid, "source": old.get("source") or "gm-overlay",
                         "subnet": old.get("subnet") or "", "gateway": old.get("gateway") or "",
                         "blue_tier1": old.get("blue_tier1") or "", "path": "BRIDGE", "notes": ""})
    for r in rows:
        sid = r["segment"]
        old = inv.get(sid) or {}
        r.update(site=site, wave="", problems=[], net=None, gw=None, vlan=None, transit_vlan="",
                 source=(r.get("source") or "gm-overlay").lower(), test=sid in test_ids)
        notes = [x.strip() for x in (r.get("notes") or "").split(";") if x.strip()] + list(old.get("events") or [])
        if old.get("gone"):
            notes.append("not on Blue since %s" % old["gone"])
        r["at_site"] = (sid in at_site) if at_site is not None else None
        r["scope"] = bool(_mig_match(scope_items, sid, r["name"], r["subnet"], r.get("blue_tier1"))) or (
            want_all and r["at_site"] is True)
        r["skip"] = _mig_match(skip_items, sid, r["name"], r["subnet"], r.get("blue_tier1"))
        if r["skip"]:
            # skip wins over the scope. Built and not cut over: skip is the undo, Blue's bridge off and then
            # Green's segment deleted (mig_drop_plan). Green the gateway: rolled back first, by hand's choice.
            obs = mig_observed(gseg.get(sid), bseg.get(sid), gbp, bbp, r["source"] == "gm-overlay")
            if r["path"] != "BRIDGE" or obs in ("planned", "absent", "retired", "created", "built", "Blue bridged"):
                r["path"] = "SKIP"
                notes.append("mig_skip_%s: %s" % (site, r["skip"]))
            else:
                c("%s (%s)" % (sid, r["subnet"] or "no subnet"), "WARN",
                  "in mig_skip_%s (%s), but %s on NSX: %s, so it stays. To undo it: fp --rollback %s --commit, then the "
                  "next fp and fp --commit --expect <its digest> take it apart" % (site, r["skip"], obs, "no side is its gateway" if obs == "NO GATEWAY"
                                                       else "Green is its gateway", r["subnet"] or sid))
                r["skip"] = None
        try:
            r["net"] = ipaddress.ip_network(r["subnet"], strict=True) if r["subnet"] else None
        except ValueError as e:
            r["problems"].append("subnet %r: %s" % (r["subnet"], e))
        try:
            r["gw"] = ipaddress.ip_address(str(r["gateway"]).split("/")[0]) if r["gateway"] else None
        except ValueError as e:
            r["problems"].append("gateway %r: %s" % (r["gateway"], e))
        lv = sorted(set((live.get(sid) or {}).values()))
        s_ = st["segments"].get(sid) or {}
        have = int(s_["transit_vlan"]) if str(s_.get("transit_vlan") or "").isdigit() else None
        if len(lv) > 1:            # once bridged, the VLAN is NSX's; two of them would be a loop
            r["problems"].append("NSX bridges it on VLANs %s: remove one bridge first" % ",".join(str(v) for v in lv))
        elif lv:
            r["vlan"] = lv[0]
            if have != lv[0]:
                mig_state_seg(st, sid)["transit_vlan"] = lv[0]
        elif have is not None and not (r["scope"] or r["test"]) and mig_observed(
                gseg.get(sid), bseg.get(sid), gbp, bbp, r["source"] == "gm-overlay") in ("planned", "absent"):
            mig_state_seg(st, sid).pop("transit_vlan", None)      # out of the scope, nothing built: back to the pool
        elif have is not None and have in pool and have not in unusable and held.get(have, sid) == sid:
            r["vlan"] = have
        elif r["path"] == "BRIDGE" and (r["scope"] or r["test"]):
            if free:
                r["vlan"] = free.pop(0)
                mig_state_seg(st, sid)["transit_vlan"] = r["vlan"]
            else:
                r["problems"].append("transit VLAN pool exhausted: widen mig_transit_vlans_%s" % site)
        r["transit_vlan"] = str(r["vlan"]) if r["vlan"] is not None else ""
        r["notes"] = "; ".join(x for i, x in enumerate(notes + r["problems"]) if x not in (notes + r["problems"])[:i])
    if at_site is not None:
        c("Blue segments at %s" % (blue.get("here") or site), "INFO", "%d of the %d on Blue's Global Manager (from %s)" % (
            len(at_site & set(bseg)), len(bseg), blue.get("lm_host") or "its Local Manager"))
        loc = blue.get("lm_local") or []
        if loc:
            c("segments only on %s" % (blue.get("lm_host") or "the Local Manager"), "WARN",
              "%d exist only on Blue's Local Manager, not on its Global Manager, so this tool does not migrate them: %s" % (
                  len(loc), some(sorted("%s (%s)" % (x.get("display_name") or x.get("id"), ((x.get("subnets") or [{}])[0]
                                                                                            or {}).get("gateway_address"))
                                        for x in loc))))
    if first:
        c("Blue segments", "INFO", "%d read; from now on each run reports what is new, changed or gone on Blue" % len(bseg))
    else:
        mine = {r["segment"] for r in rows if r["scope"] or r["test"]} | set(st["segments"])
        if new:
            c("new on Blue", "INFO", some(sorted("%s (%s)" % (s_, inv[s_].get("subnet") or "no subnet") for s_ in new)))
        if changed:
            c("changed on Blue", "WARN" if any(x.split(":")[0] in mine for x in changed) else "INFO", some(changed))
        if gone:
            c("gone from Blue", "WARN" if set(gone) & mine else "INFO", some(sorted(gone)))
    return rows, checks


# ---------------------------------------------------------------- migpath: collection
def mig_side(host, H, site_id):
    """What migpath reads from one Global Manager for one location."""
    d = {"host": host, "site": site_id}
    st, v = http("https://%s/api/v1/node/version" % host, headers=H, timeout=30)
    d["version"] = v.get("product_version") if st == 200 and isinstance(v, dict) else None
    d["status"] = st
    ep = "/sites/%s/enforcement-points/default" % site_id
    for key, sub in (("segments", "/segments"), ("tier1s", "/tier-1s"), ("tier0s", "/tier-0s"),
                     ("tzs", ep + "/transport-zones"), ("edge_clusters", ep + "/edge-clusters"),
                     ("bridge_profiles", ep + "/edge-bridge-profiles")):
        res, s = _mig_list(host, H, sub)
        d[key], d[key + "_status"] = (res if res is not None else []), s
    # a segment NSX is still deleting (marked_for_delete) is gone for the plan; its bridge holds its VLAN until it is
    d["segments_deleting"] = [x for x in d["segments"] if x.get("marked_for_delete")]
    d["segments"] = [x for x in d["segments"] if not x.get("marked_for_delete")]
    for ec in d["edge_clusters"]:
        res, _s = _mig_list(host, H, "%s/edge-clusters/%s/edge-nodes" % (ep, ec.get("id")))
        ec["_nodes"] = res or []
    d["router_macs"] = {}          # filled from the Local Managers by cmd_migpath
    return d


def mig_lm_vdr_mac(host, user, pw):
    """Router MAC on one Local Manager. The documented place for it is the Local Manager's
    policy API; the Global Manager API has no global-config. Returns {"mac", "status"}."""
    st, b = http("https://%s/policy/api/v1/infra/global-config" % host, headers=_mig_H(user, pw), timeout=30)
    return {"mac": (b.get("vdr_mac") if st == 200 and isinstance(b, dict) else None), "status": st}


def mig_lm_edges(host, user, pw):
    """Edge transport nodes from a Local Manager, shaped like collect_nsx output so
    fed_edge_nodes() reads it. Only the Local Manager knows which zones an edge carries."""
    H = _mig_H(user, pw)
    d = {}
    for key, path in (("transport_nodes", "/api/v1/transport-nodes?page_size=1000"),
                      ("edge_clusters", "/api/v1/edge-clusters?page_size=1000")):
        st, b = http("https://%s%s" % (host, path), headers=H, timeout=60)
        d[key] = {"status": st, "body": b if st == 200 else {}}
    return d


def mig_snapshot(host, H, side):
    """Every object on one Global Manager that the migration could touch or depend on, by path:
    segments, gateways, their locale services, BGP neighbours and prefix lists, zones, edge
    clusters and nodes, bridge profiles. Compared before and after, it proves what changed."""
    snap = {}

    def put(o, fallback):
        snap[_mig_rel(o.get("path")) or fallback] = {k: v for k, v in o.items()
                                                     if not str(k).startswith("_") or k == "_revision"}

    for key in ("segments", "tier1s", "tier0s", "tzs", "bridge_profiles"):
        for o in side.get(key) or []:
            put(o, "/%s/%s" % (key, o.get("id")))
    for ec in side.get("edge_clusters") or []:
        put(ec, "/edge-clusters/%s" % ec.get("id"))
        for nd in ec.get("_nodes") or []:
            put(nd, "/edge-clusters/%s/edge-nodes/%s" % (ec.get("id"), nd.get("id")))
    for t in side.get("tier0s") or []:
        t0 = "/tier-0s/%s" % t.get("id")
        for o in _mig_list(host, H, t0 + "/prefix-lists")[0] or []:
            put(o, "%s/prefix-lists/%s" % (t0, o.get("id")))
        for ls in _mig_list(host, H, t0 + "/locale-services")[0] or []:
            lsp = "%s/locale-services/%s" % (t0, ls.get("id"))
            put(ls, lsp)
            for o in _mig_list(host, H, lsp + "/bgp/neighbors")[0] or []:
                put(o, "%s/bgp/neighbors/%s" % (lsp, o.get("id")))
    for t in side.get("tier1s") or []:
        t1 = "/tier-1s/%s" % t.get("id")
        for ls in _mig_list(host, H, t1 + "/locale-services")[0] or []:
            put(ls, "%s/locale-services/%s" % (t1, ls.get("id")))
    return snap


def _mig_norm(obj):
    """Same shape as the evidence files: redacted and JSON round-tripped."""
    return json.loads(json.dumps(deep_redact(obj), sort_keys=True, default=str))


def mig_alarms(host, H):
    """Open alarms on one manager, keyed by id. None when not readable."""
    out, url = {}, "https://%s/api/v1/alarms?page_size=200&status=OPEN" % host
    for _ in range(20):
        st, b = http(url, headers=H, timeout=40)
        if st != 200 or not isinstance(b, dict):
            return out or None
        for x in _res(b):
            out[str(x.get("id"))] = {k: x.get(k) for k in ("feature_name", "event_type", "entity_id",
                                                           "severity", "summary") if x.get(k) is not None}
        cur = b.get("cursor")
        if not cur:
            break
        url = "https://%s/api/v1/alarms?page_size=200&status=OPEN&cursor=%s" % (host, urllib.parse.quote(str(cur)))
    return out


def mig_impact(before, after, scope):
    """What changed between two snapshots, and which of it lies outside `scope` (paths)."""
    b, a_ = before or {}, after or {}
    changed = sorted(p for p in set(b) & set(a_) if b[p] != a_[p])
    added, removed = sorted(set(a_) - set(b)), sorted(set(b) - set(a_))
    return {"changed": changed, "added": added, "removed": removed, "scope": sorted(scope),
            "out_of_scope": [p for p in changed + added + removed if p not in scope]}


def mig_test_ids(cfg, site, segments):
    """(configured names, Blue segment ids they resolve to) for mig_test_segments_<site>: a segment's
    id, its name, or its subnet (192.0.2.0/24)."""
    names = _mig_items(_mig_key(cfg, "mig_test_segments", site))
    ids = set()
    for s_ in segments or []:
        nets = set()
        for sub in s_.get("subnets") or []:
            try:
                nets.add(str(ipaddress.ip_interface(str(sub.get("gateway_address"))).network))
            except ValueError:
                pass
        if s_.get("id") in names or s_.get("display_name") in names or nets & set(names):
            ids.add(s_.get("id"))
    return names, sorted(i for i in ids if i)


def mig_target(a):
    return a.cutover or a.unbridge or a.rollback or getattr(a, "retire", None)


def mig_blue_scope(a, cfg, site, blue, res, rows):
    """Blue paths a run may change, taken from the plan rather than from what validated. --test: the
    test segments and the Blue bridge profile. A build: the BRIDGE segments of mig_scope_<site>, the ones
    it takes apart (mig_drop_plan) and the Blue bridge profile. Any other action: its one segment.
    mig_apply refuses a Blue write outside it, and the re-read after every commit fails the run if
    anything outside it changed."""
    bp = (((res or {}).get("edges") or {}).get("Blue") or {}).get("bp_path")
    bps = {bp} if bp else set()
    infra = mig_bridge_infra_paths(cfg, site, (blue or {}).get("snapshot"))     # the bridge zone, cluster, edges
    if getattr(a, "test", False):
        names, ids = mig_test_ids(cfg, site, blue.get("segments"))
        return {"/segments/%s" % i for i in set(names) | set(ids)} | bps | infra
    if a.mode == "build":
        return {"/segments/%s" % r["segment"] for r in rows or []
                if r.get("segment") and r.get("path") == "BRIDGE" and r.get("scope")} | {
            "/segments/%s" % r["segment"] for r in (res or {}).get("drop") or [] if r.get("segment")} | bps | infra
    t = mig_target(a)
    return {"/segments/%s" % r["segment"] for r in rows or []
            if r.get("segment") and t in (r["segment"], r.get("subnet"), r.get("name"))} | infra


def _mig_blue_writes(cfg, a):
    """true: the tool writes Blue. test: only in --test runs, which touch only the test segments."""
    v = str(cfg.get("mig_blue_writes") or "").strip().lower()
    return _mig_true(v) or (v == "test" and bool(getattr(a, "test", False)))


def _mig_node_tzs(lm, name):
    for t in _res(_nb(lm, "transport_nodes")):
        if str(t.get("display_name") or "").lower() == str(name).lower():
            ids = []
            for hs in (t.get("host_switch_spec") or {}).get("host_switches") or []:
                for e in hs.get("transport_zone_endpoints") or []:
                    if e.get("transport_zone_id"):
                        ids.append(str(e["transport_zone_id"]))
            return ids
    return None


def _mig_tz_ids(tz):
    return {str(tz.get(k)) for k in ("nsx_id", "unique_id", "realization_id", "id") if tz.get(k)}


# ---------------------------------------------------------------- migpath: inventory
def _mig_has_dhcp(seg):
    seg = seg or {}
    return bool(seg.get("dhcp_config_path") or any((x or {}).get("dhcp_ranges") or (x or {}).get("dhcp_config")
                                                   for x in seg.get("subnets") or []))


def _mig_classify(seg, t1n):
    """Discovered fields for one Blue segment and the path the tool would give it."""
    gwa = ((seg.get("subnets") or [{}])[0] or {}).get("gateway_address") or ""
    net = gw = ""
    if gwa:
        try:
            itf = ipaddress.ip_interface(gwa)
            net, gw = str(itf.network), str(itf.ip)
        except ValueError:
            pass
    src = "gm-vlan" if seg.get("vlan_ids") else "gm-overlay"
    notes, path = [], "BRIDGE"
    if src == "gm-vlan":
        path = "REVIEW"
        notes.append("VLAN-backed on Blue: Green-side bridge only, legacy gateway switched by hand")
    elif not gw or not seg.get("connectivity_path"):
        path = "REVIEW"
        notes.append("Blue does not route it")
    if len(seg.get("subnets") or []) > 1:
        notes.append("%d subnets on Blue, only the first is migrated" % len(seg["subnets"]))
    if _mig_has_dhcp(seg):
        notes.append("DHCP on Blue: recreate on Green before cutover")
    return {"segment": seg.get("id"), "source": src, "subnet": net, "gateway": gw,
            "blue_tier1": t1n.get(seg.get("connectivity_path"), ""), "path": path, "notes": "; ".join(notes)}


def mig_plan_raw(path):
    """The plan CSV of 1.14.0 and earlier, as stored: read only to carry its SKIP decisions over."""
    if not path or not os.path.exists(path):
        return None
    with open(path, newline="", encoding="utf-8-sig") as fh:
        return [{c: (d.get(c) or "").strip() for c in MIG_COLS}
                for d in ({(k or "").strip().lower(): v for k, v in row.items()} for row in csv.DictReader(fh))]


def _mig_free_vlans(cfg, site, st, live=None, taken=()):
    """Pool VLANs nothing holds: not given out by this tool (state), not on a migration bridge on NSX,
    not green infrastructure (mig_infra_vlans), not a VLAN-backed segment's (`taken`)."""
    pool = _mig_vlans(_mig_key(cfg, "mig_transit_vlans", site))
    used = set(_mig_vlans(_mig_key(cfg, "mig_infra_vlans", site))) | set(taken)
    used |= {int(v["transit_vlan"]) for v in (st.get("segments") or {}).values()
             if str(v.get("transit_vlan") or "").isdigit()}
    used |= {v for d_ in (live or {}).values() for v in d_.values()}
    return [v for v in pool if v not in used]


def mig_unread(label, side, keys):
    """The lists this run needed from one Global Manager and did not get: ["Blue segments (HTTP 0)"]."""
    return ["%s %s (HTTP %s)" % (label, k.replace("_", " "), side.get(k + "_status"))
            for k in keys if side is not None and side.get(k + "_status", 200) != 200]


def mig_bp_paths(cfg, site, green, blue):
    """(Green, Blue) path of this migration's bridge profile on each side, or None where it does not exist yet."""
    out = []
    for d, pre in ((green, "mig_"), (blue, "mig_blue_")):
        bpn = _mig_key(cfg, pre + "bridge_profile", site) or "bp-migration-%s" % site
        hit = _mig_named((d or {}).get("bridge_profiles"), bpn)
        out.append(_mig_rel(hit[0].get("path")) if hit else None)
    return tuple(out)


def mig_live_vlans(cfg, site, green, blue):
    """{segment: {"Green": vlan, "Blue": vlan}}: the transit VLAN each side's migration bridge carries on
    NSX now. Once a segment is bridged, its VLAN is NSX's, whatever the plan says."""
    out = {}
    for side, d, bp in zip(("Green", "Blue"), (green, blue), mig_bp_paths(cfg, site, green, blue)):
        if not bp:
            continue
        for s in ((d or {}).get("segments") or []) + ((d or {}).get("segments_deleting") or []):
            for e in s.get("bridge_profiles") or []:
                if _mig_rel(e.get("bridge_profile_path")) == bp:
                    for v in e.get("vlan_ids") or []:
                        if str(v).isdigit():
                            out.setdefault(s.get("id"), {})[side] = int(v)
    return out


# ---------------------------------------------------------------- migpath: state
# One JSON file beside the plan holds what the runs learn: each scope's Blue baseline, each
# segment's observed status and history of changes, the VMs and NSX tags captured on Blue, the
# prefix-list entries and tags this tool placed, and the leaf ports it has read. It is written only
# when that changes, so a run that changes nothing leaves it byte for byte; the state before each
# change is kept beside it (.backup). Every run, changed or
# not, adds one line to the journal beside it. A lock beside it allows one run at a time.

def mig_state_file(cfg, site, plan_file):
    f = cfg.get("mig_state_file_%s" % site) or "migpath_state_%s.json" % site
    return f if os.path.isabs(f) else os.path.join(os.path.dirname(os.path.abspath(plan_file)), f)


def mig_journal_file(st_path):
    return os.path.splitext(st_path)[0] + ".runs.jsonl"


def mig_lock(st_path, ctx):
    """One migpath run at a time per site, as a state lock: a second run stops before it reads or
    writes anything. The operating system releases the lock when the run ends, however it ends."""
    import fcntl
    lp = st_path + ".lock"
    try:
        fh = open(lp, "a+")
    except OSError as e:
        sys.exit("cannot open the lock %s (%s). Nothing was done" % (lp, e))
    try:
        fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except (IOError, OSError):
        fh.seek(0)
        holder = fh.read().strip() or "another process"
        fh.close()
        sys.exit("another migpath run holds %s (%s). Nothing was done: run again when it ends." % (lp, holder))
    fh.seek(0)
    fh.truncate()
    fh.write("pid %d since %s: %s\n" % (os.getpid(), now(), " ".join(sys.argv[1:])))
    fh.flush()
    os.chmod(lp, 0o600)
    ctx["lock"] = fh


def mig_state_load(path, site):
    """The state as the last run left it; a new one on the first run. A state file that cannot be read
    stops the run: replacing it with an empty one would lose the baselines, the captures and what the
    tool placed, and the next runs would act without them."""
    st = {}
    if os.path.exists(path):
        try:
            with open(path) as fh:
                st = json.load(fh)
            if not isinstance(st, dict):
                raise ValueError("not a JSON object")
        except (OSError, ValueError) as e:
            sys.exit("state file %s cannot be read (%s). Nothing was done. The state before its last change is "
                     "in %s.backup: check it and copy it over the state file, or move the state file aside to "
                     "start over (baselines and captures are then taken again)" % (path, e, path))
    st.setdefault("site", site)
    st.setdefault("created", now())
    for k in ("baselines", "segments", "leaves"):
        st.setdefault(k, {})
    runs = st.pop("runs", None)               # 1.12.0 kept the journal inside the state
    jf = mig_journal_file(path)
    if runs and not os.path.exists(jf):
        with open(jf, "w") as fh:
            fh.writelines(json.dumps(r, sort_keys=True, default=str) + "\n" for r in runs)
        os.chmod(jf, 0o600)
    return st


def _mig_canon(st):
    return json.dumps({k: v for k, v in st.items() if k != "updated"}, sort_keys=True, default=str)


def mig_state_save(path, st, before=None):
    """Written only when what it holds changes: `before` is _mig_canon() of the state as loaded."""
    if before is not None and _mig_canon(st) == before:
        return False
    st["updated"] = now()
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(st, fh, indent=2, sort_keys=True, default=str)
    os.chmod(tmp, 0o600)
    if os.path.exists(path):          # the state before this change, as terraform.tfstate.backup
        shutil.copy2(path, path + ".backup")
        os.chmod(path + ".backup", 0o600)
    os.replace(tmp, path)
    return True


def mig_journal(st_path, entry):
    """One line per run, changed or not: the audit trail. Append-only."""
    jf = mig_journal_file(st_path)
    new = not os.path.exists(jf)
    with open(jf, "a") as fh:
        fh.write(json.dumps(entry, sort_keys=True, default=str) + "\n")
    if new:
        os.chmod(jf, 0o600)


def mig_state_seg(st, sid):
    return st["segments"].setdefault(sid, {"status": "planned", "history": [], "vms": {}})


def mig_observed(g, b, gbp, bbp, blue_side=True):
    """Where a segment stands, read from NSX rather than from what earlier runs did: planned, created,
    built, cutover, unbridged, retired, absent, NO GATEWAY when neither side has Connectivity ON, or
    Blue bridged when Blue's segment carries the migration bridge and Green has no segment."""
    def bridged(o, bp):
        es = (o or {}).get("bridge_profiles") or []
        return any(_mig_rel(e.get("bridge_profile_path")) == bp for e in es) if bp else bool(es)
    if not g:
        if blue_side and b and bbp and bridged(b, bbp):
            return "Blue bridged"
        return "planned" if (b or not blue_side) else "absent"
    if _mig_conn(g) == "ON":
        if blue_side and not b:
            return "retired"
        return "cutover" if bridged(g, gbp) or bridged(b, bbp) else "unbridged"
    if blue_side and (not b or _mig_conn(b) == "OFF"):
        return "NO GATEWAY"
    return "built" if bridged(g, gbp) else "created"


def mig_refresh_status(st, rows, gseg, bseg, gbp, bbp):
    """Observed status for the rows in play: in the state already, in the scope, or on NSX."""
    for r in rows:
        sid = r.get("segment")
        if not sid:
            continue
        obs = mig_observed(gseg.get(sid), bseg.get(sid), gbp, bbp, (r.get("source") or "gm-overlay") == "gm-overlay")
        if sid in st["segments"] or r.get("scope") or obs not in ("planned", "absent"):
            mig_state_seg(st, sid)["status"] = obs


def mig_state_event(st, sid, action, result, outdir, detail=""):
    """History of changes: recorded only for a run that wrote to this segment, or failed on it."""
    s_ = mig_state_seg(st, sid)
    s_["history"] = (s_["history"] + [{"ts": now(), "action": action, "result": result,
                                       "evidence": os.path.abspath(outdir), "detail": detail}])[-200:]

def mig_scope_key(a, res=None, scoped=True):
    """The baseline a run compares with: the test segments (--test), or the scope of the config."""
    return "test" if getattr(a, "test", False) else "scope"



# ---------------------------------------------------------------- migpath: router MAC
def mig_router_mac(cfg, a, green_lms, blue_macs, outdir, before_write=None, review=None, state=None):
    """--router-mac: set Green's router MAC on every Green Local Manager and read it back. Every Local
    Manager is read first; nothing is written unless all of them were read, so they never end up
    disagreeing. The documented change is a GET, the two fields changed, and a PUT of the whole
    object. Refused while Blue's router MAC is unknown or equal to the target. `review(digest, items)`
    decides a --commit --expect run (mig_review). Returns (rc, digest of the planned changes or None,
    their item hashes, Local Managers to change, Local Managers changed)."""
    target = str(cfg.get("mig_router_mac") or "").strip().lower()
    if not target:
        print("\n  [REFUSED] set mig_router_mac: the router MAC every Green Local Manager gets, different from Blue's "
              "(NSX's default is 02:50:56:56:44:52)")
        return 1, None, [], 0, 0
    if not re.fullmatch(r"([0-9a-f]{2}:){5}[0-9a-f]{2}", target):
        print("\n  [REFUSED] mig_router_mac %r is not a MAC address. Write it quoted, e.g. \"02:50:56:56:44:62\": "
              "YAML reads some unquoted MACs as numbers" % target)
        return 1, None, [], 0, 0
    blue_set = {str((v or {}).get("mac") or "").lower() for v in (blue_macs or {}).values()} - {""}
    if not blue_set:
        print("\n  [REFUSED] Blue's router MAC not read (%s): a collision cannot be ruled out"
              % (", ".join("%s HTTP %s" % (h, (v or {}).get("status")) for h, v in sorted((blue_macs or {}).items()))
                 or "set mig_blue_lm_host_<site>"))
        return 1, None, [], 0, 0
    if target in blue_set:
        print("\n  [REFUSED] mig_router_mac %s is Blue's router MAC: pick another" % target)
        return 1, None, [], 0, 0
    if not green_lms:
        print("\n  [REFUSED] no Green Local Manager configured (nsx_lm_host_<site>)")
        return 1, None, [], 0, 0
    plan, rc = [], 0
    for host, user, pw in green_lms:
        H = _mig_H(user, pw)
        if not pw:
            plan.append((host, H, "ERROR", "no password in %s: nothing written anywhere"
                         % _mig_shown(_MIG_CRED_KEY.get(host, "nsx_admin_password")), None))
            rc = 1
            continue
        st, gc = http("https://%s/policy/api/v1/infra/global-config" % host, headers=H, timeout=30)
        if st != 200 or not isinstance(gc, dict):
            plan.append((host, H, "ERROR", "read %s: nothing written anywhere" % mig_lm_unread_why(host, {"status": st}),
                         None))
            rc = 1
            continue
        cur = str(gc.get("vdr_mac") or "").lower()
        plan.append((host, H, "UNCHANGED" if cur == target else "UPDATE", cur, gc))
    ups = [p for p in plan if p[2] == "UPDATE"]
    items = sorted(([_mig_h([p[0], p[3], target]), "lm:%s" % p[0], p[4].get("_revision")] for p in ups),
                   key=lambda i: json.dumps(i, default=str))
    digest = _mig_h(items) if items else None
    stopped = note = None
    if a.commit and a.expect:
        ok, note = (review or (lambda d, i: (a.expect == (d or "none"), None)))(digest, items)
        if not ok:
            stopped, note = note or ("this is not the plan that was reviewed: --expect %s, the plan now is %s. "
                                     "Nothing was written" % (a.expect, digest or "none")), None
    rows = []
    for host, H, act, cur, gc in plan:
        url = "https://%s/policy/api/v1/infra/global-config" % host
        if act != "UPDATE" or not a.commit or rc or stopped:
            rows.append((host, act, cur if act == "UNCHANGED" else cur if act == "ERROR"
                         else "%s -> %s" % (cur or "?", target)))
            continue
        body = dict(gc, vdr_mac=target, allow_changing_vdr_mac_in_use=True)
        if before_write:
            before_write()            # the probes start just before the first write, once
            before_write = None
        st2, b2 = http(url, method="PUT", headers=H, body=body, timeout=60)
        st3, gc3 = http(url, headers=H, timeout=30)
        back = str((gc3 or {}).get("vdr_mac") or "").lower() if st3 == 200 and isinstance(gc3, dict) else ""
        if st2 in (200, 201) and back == target:
            rows.append((host, "UPDATE", "%s -> %s, read back" % (cur or "?", target)))
            if state is not None:       # the value before this tool first changed it: the way back
                rec_ = state.setdefault("router_mac", {}).setdefault(host, {"before": cur or None, "first_changed": now()})
                rec_.update(now=target, changed=now())
        else:
            rows.append((host, "ERROR", "PUT HTTP %s %s; reads %s" % (st2, str((b2 or {}).get("error_message") or "")[:100],
                                                                    back or "?")))
            rc = 1
    print("")
    print("  Blue's router MAC: %s" % ", ".join(sorted(blue_set)))
    for h, act, det in rows:
        print("  [%-9s] %-36s %s" % (act, h, det))
    print("")
    if stopped:
        print("  STOPPED: %s" % stopped)
    elif rc:
        print("  STOPPED: fix the ERROR and re-run")
    elif not ups:
        print("  No changes: router MAC %s on every Green Local Manager already." % target)
    elif a.commit:
        print("  router MAC %s on every Green Local Manager" % target)
    else:
        print("  plan %s: %d change(s), nothing written. To apply exactly these: --router-mac --commit --expect %s"
              % (digest, len(ups), digest))
    if note and not stopped:
        print("  %s" % note)
    write_json(outdir, "router_mac", {"target": target, "commit": bool(a.commit), "blue": sorted(blue_set), "digest": digest,
                                      "results": [{"host": h, "action": x, "detail": d} for h, x, d in rows]})
    L = ["MANUAL STEPS   router MAC %s on every Green Local Manager   %s" % (target, now()), "=" * 74,
         "For use only when the tool cannot run. Each step is safe to run again: the PUT carries the",
         "_revision it read, so NSX refuses it if the object changed since. curl prompts for each password.", ""]
    for i, (host, user, _pw) in enumerate(green_lms, 1):
        url = "https://%s/policy/api/v1/infra/global-config" % host
        L += ["%d  %s" % (i, host),
              "   curl -k -u %s %s > global-config.json" % (user, url),
              "   in global-config.json set \"vdr_mac\" to \"%s\" and \"allow_changing_vdr_mac_in_use\" to true" % target,
              "   curl -k -u %s -X PUT -H 'Content-Type: application/json' -d @global-config.json %s" % (user, url),
              "   curl -k -u %s %s        (reads \"vdr_mac\": \"%s\")" % (user, url, target), ""]
    with open(os.path.join(outdir, "manual_steps.txt"), "w") as fh:
        fh.write("\n".join(L))
    return (1 if rc or stopped else 0), digest, items, len(ups), sum(1 for r in rows if r[2].endswith("read back"))


# ---------------------------------------------------------------- migpath: the Blue test segment
def _mig_pl_decides(prefixes, net):
    """(permitted, entry): the first entry of a prefix list that matches `net` decides; none denies."""
    for p in prefixes or []:
        n = str(p.get("network") or "")
        act = str(p.get("action") or "").upper() == "PERMIT"
        if n.upper() == "ANY":
            return act, "ANY"
        try:
            base = ipaddress.ip_network(n, strict=False)
        except ValueError:
            continue
        if net.version != base.version or net.network_address not in base or net.prefixlen < base.prefixlen:
            continue
        ge = int(p["ge"]) if p.get("ge") else base.prefixlen
        le = int(p["le"]) if p.get("le") else (base.prefixlen if not p.get("ge") else net.max_prefixlen)
        if ge <= net.prefixlen <= le:
            return act, n
    return False, "no entry matches"


def mig_blue_advertises(blue, t1, net):
    """From Blue's snapshot: the Tier-1 advertises connected, and every outbound filter on its
    Tier-0's BGP neighbours lets `net` out."""
    if "TIER1_CONNECTED" not in (t1.get("route_advertisement_types") or []):
        return False, "%s does not advertise connected subnets" % t1.get("display_name")
    t0 = _mig_rel(t1.get("tier0_path"))
    snap = blue.get("snapshot") or {}
    filters = set()
    for p, o in snap.items():
        if t0 and p.startswith(t0 + "/locale-services/") and "/bgp/neighbors/" in p:
            for rf in o.get("route_filtering") or []:
                filters.update(rf.get("out_route_filters") or [])
    if not filters:
        return True, "no outbound filter on %s" % (t0.rsplit("/", 1)[-1] or "its Tier-0")
    for f in sorted(filters):
        ok, by = _mig_pl_decides((snap.get(_mig_rel(f)) or {}).get("prefixes"), net)
        if not ok:
            return False, "%s denies it (%s)" % (f.rsplit("/", 1)[-1], by)
    return True, "permitted by %s" % ", ".join(f.rsplit("/", 1)[-1] for f in sorted(filters))


def mig_setup(cfg, site, green, blue):
    """--test --setup: the Blue test segment from mig_test_subnet_<site> on mig_test_blue_tier1_<site>,
    gateway the first address, Connectivity ON, tagged migpath=test. Returns (checks, objects)."""
    checks, objs = [], []

    def c(item, state, detail=""):
        checks.append({"area": "setup", "item": item, "state": state, "detail": str(detail)[:400]})

    names = _mig_items(_mig_key(cfg, "mig_test_segments", site))
    sub = _mig_key(cfg, "mig_test_subnet", site)
    t1n = _mig_key(cfg, "mig_test_blue_tier1", site)
    if len(names) != 1:
        c("test segment", "FAIL", "mig_test_segments_%s must name exactly one segment for --setup" % site)
        return checks, objs
    name, net = names[0], None
    try:
        net = ipaddress.ip_network(str(sub or ""), strict=True)
        if net.num_addresses < 4:
            raise ValueError("too small for a gateway and a test VM")
    except ValueError as e:
        net = None
        c("test subnet", "FAIL", "mig_test_subnet_%s %s" % (site, ("%r: %s" % (sub, e)) if sub else "is not set"))
    t1 = (_mig_named(blue["tier1s"], t1n) or [None])[0] if t1n else None
    if not t1:
        c("Blue Tier-1 for the test segment", "FAIL", "%s. Have: %s" % (
            ("%r not found" % t1n) if t1n else "set mig_test_blue_tier1_%s" % site,
            ", ".join(sorted(str(t.get("display_name")) for t in blue["tier1s"])) or "none"))
    if not net or not t1:
        return checks, objs
    gw = "%s/%d" % (net.network_address + 1, net.prefixlen)
    hit = []
    for side, d in (("Blue", blue), ("Green", green)):
        for s_ in d["segments"]:
            if side == "Blue" and s_.get("id") == name:
                continue
            for x in s_.get("subnets") or []:
                try:
                    other = ipaddress.ip_interface(x.get("gateway_address")).network
                except (ValueError, TypeError):
                    continue
                if other.overlaps(net):
                    hit.append("%s segment %s (%s)" % (side, s_.get("id"), other))
    c("test subnet %s is free" % net, "FAIL" if hit else "PASS",
      ("overlaps %s" % ", ".join(hit[:4])) if hit else "no segment on either side uses it")
    ok, why = mig_blue_advertises(blue, t1, net)
    c("Blue advertises %s" % net, "PASS" if ok else "WARN", why if ok else
      "%s: until cutover the test VM answers only inside the segment, and the rollback route check fails" % why)
    ex = next((s_ for s_ in blue["segments"] if s_.get("id") == name), None)
    if ex:
        egw = str(((ex.get("subnets") or [{}])[0] or {}).get("gateway_address") or "")
        same = egw == gw and ex.get("connectivity_path") == t1.get("path")
        c("Blue segment %s" % name, "PASS" if same else "FAIL", "exists as configured" if same else
          "exists with gateway %s on %s, not what mig_test_* says: fix the config or remove it by hand"
          % (egw or "none", _mig_rel(ex.get("connectivity_path")) or "no gateway"))
    body = {"display_name": name, "connectivity_path": t1.get("path"), "subnets": [{"gateway_address": gw}],
            "advanced_config": {"connectivity": "ON"}, "tags": [{"scope": "migpath", "tag": "test"}],
            "description": "migpath test segment"}
    objs.append({"side": "Blue", "kind": "test-segment", "id": name, "segment": name, "host": blue["host"],
                 "H": blue["_H"], "path": "/segments/%s" % name, "create": body, "mutate": (lambda o: o),
                 "needs": None, "after": [], "gate": None})
    return checks, objs


def mig_setup_remove(cfg, site, green, blue, blm):
    """--test --setup --remove: the Blue test segment --setup made (tag migpath=test), deleted once nothing of
    the test is on it: Green has no segment of its id, Blue bridges it nowhere, and Blue's Local Manager
    holds no VM port on it. Returns (checks, objects)."""
    checks, objs = [], []

    def c(item, state, detail=""):
        checks.append({"area": "setup", "item": item, "state": state, "detail": str(detail)[:400]})

    names = _mig_items(_mig_key(cfg, "mig_test_segments", site))
    if len(names) != 1:
        c("test segment", "FAIL", "mig_test_segments_%s must name exactly one segment for --setup --remove" % site)
        return checks, objs
    name = names[0]
    b = next((s_ for s_ in blue["segments"] if s_.get("id") == name), None)
    if not b:
        c("Blue segment %s" % name, "INFO", "not on Blue: nothing to delete")
        return checks, objs
    gone = [s_ for s_ in (green.get("segments") or []) + (green.get("segments_deleting") or []) if s_.get("id") == name]
    need = None
    if not any(t.get("scope") == "migpath" and t.get("tag") == "test" for t in b.get("tags") or []):
        need = "not made by --setup (no migpath=test tag): left. Delete it by hand if it should go"
    elif gone:
        need = "Green still has a segment %s%s: fp --test --remove --commit first" % (
            name, " (NSX is deleting it)" if gone[0].get("marked_for_delete") else "")
    elif b.get("bridge_profiles"):
        need = "Blue still bridges it: fp --test --remove --commit first"
    else:
        bh, bu, bp = blm
        ports, why = mig_blue_vm_ports(bh, _mig_H(bu, bp), {name: b.get("display_name") or name}) if bh else \
            (None, "mig_blue_lm_host_%s not set" % site)
        if ports is None or name not in ports:
            need = "its VM ports on Blue's Local Manager were not read (%s): it cannot be shown empty" % (why or "no switch found")
        elif ports[name]:
            need = "%d VM port(s) on it in Blue's Local Manager: move or delete those VMs first" % ports[name]
    c("Blue segment %s" % name, "INFO" if not need else "WARN", "made by --setup, nothing on it: --commit deletes it"
      if not need else need)
    objs.append({"side": "Blue", "kind": "test-segment", "id": name, "segment": name, "host": blue["host"],
                 "H": blue["_H"], "path": "/segments/%s" % name, "create": None, "mutate": None,
                 "needs": need, "after": [], "gate": None, "delete": True})
    return checks, objs


# ---------------------------------------------------------------- migpath: vCenter
_MIG_VC = {}
_MIG_VC_PW = {}         # host -> (user, password), this run only, never written
_MIG_VIM = {}           # host -> logged-in MigVim


def mig_vc(cfg, site, which):
    """(host, session headers) for the Blue vCenter at this site ('blue'), Blue's other site
    ('blue-remote') or Green ('green'). (None, None) when not configured."""
    key = {"blue": "mig_blue_vc_%s", "blue-remote": "mig_blue_vc_remote_%s", "green": "mig_green_vc_%s"}[which] % site
    host = str(cfg.get(key) or "").strip()
    if not host:
        return None, None
    if host in _MIG_VC:
        return host, _MIG_VC[host]
    side = "blue" if which.startswith("blue") else "green"
    user, pw, pkey = _mig_vc_signin(cfg, site, host, side)
    if pkey in ("mig_%s_vc_password" % side, "mig_%s_vc_password_%s" % (side, site)):    # this site's own: env first
        pw = os.environ.get("FLEETPARITY_MIG_%s_VC_PASSWORD" % side.upper()) or pw
    if side == "green" and not pw and pkey == "mig_green_vc_password":
        pw = cfg.get("sddc_password") or ""
    if not pw and not DRY:
        pw = getpass.getpass("      vCenter %s '%s' password (%s): " % (host, user, _mig_shown(pkey)))
    _MIG_VC_PW[host] = (user, pw)
    _MIG_VC[host], why = _mig_vc_session(host, user, pw)
    if why:
        _MIG_VC_WHY[host] = why if why.startswith("not reachable") else "%s: %s" % (why, _mig_shown(pkey))
    return host, _MIG_VC[host]


_MIG_VC_WHY = {}            # vCenter -> why this run could not sign in to it, naming the setting to fix
_MIG_CRED_KEY = {}          # Local Manager -> the setting its password came from, to name in a message


def mig_green_lm_signins(cfg, site, ask=True):
    """[(Local Manager, user, password)] for every Green Local Manager the config names or the Global Manager
    has, each signed in to with its own site's password: site-b's with sites.site-b.green.lm_password, in a
    site-a run too. A per-host nsx_admin_password_<fqdn> wins; with the sign-ins kept once for every site, that
    one. A password left blank is asked for by name; for another site's manager, Enter leaves it unread, so
    no sign-in is tried with a password that is not its own."""
    out, env_shared = [], os.environ.get("FLEETPARITY_NSX_ADMIN_PASSWORD") or ""
    for k in sorted(cfg):
        if not (k.startswith("nsx_lm_host_") and cfg.get(k)):
            continue
        s_, fq = k[len("nsx_lm_host_"):], str(cfg[k]).strip()
        ukey = next((x for x in ("nsx_admin_user_%s" % fq, "nsx_admin_user_%s" % s_) if cfg.get(x)), "nsx_admin_user")
        user = cfg.get(ukey) or "admin"
        pkey = next((x for x in ("nsx_admin_password_%s" % fq, "nsx_admin_password_%s" % s_) if x in cfg), "nsx_admin_password")
        mine = s_ == site or pkey == "nsx_admin_password"         # this run's site, or one password for every site
        pw = os.environ.get(env_key("FLEETPARITY_NSX_ADMIN_PASSWORD", fq)) or cfg.get(pkey) or (env_shared if mine else "")
        if not pw and ask and not DRY:
            pw = getpass.getpass("      Green Local Manager %s '%s' password (%s%s): " % (
                fq, user, _mig_shown(pkey), "" if mine else "; Enter leaves it unread"))
        _MIG_CRED_KEY[fq] = pkey
        out.append((fq, user, pw or ""))
    return out


def mig_lm_unread_why(host, v):
    """Why a Local Manager's router MAC was not read, naming the setting when it refused the password."""
    st = v.get("status")
    if st in (401, 403) and host in _MIG_CRED_KEY:
        return "HTTP %s: the password in %s was refused" % (st, _mig_shown(_MIG_CRED_KEY[host]))
    return ("HTTP %s" % st) if isinstance(st, int) else str(st or "not read")


def _mig_vc_signin(cfg, site, host, side):
    """(user, password, setting) for one Blue or Green vCenter: the sign-in of the site whose vCenter it is,
    so a site-a run reading site-b's Blue vCenter signs in with site-b's (sites.site-b.blue.vc_password); else this
    run's own. setting: the key the password comes from, to name in a message."""
    sites = [str(x) for x in _mig_items(cfg.get("mig_sites"))]
    ukey, pkey = "mig_%s_vc_user" % side, "mig_%s_vc_password" % side
    dflt = "administrator@vsphere.local"
    own = next((s_ for s_ in sites if str(cfg.get("mig_%s_vc_%s" % (side, s_)) or "").strip().lower() == host.lower()), None)
    if own and own != site and "%s_%s" % (pkey, own) in cfg:
        return (cfg.get("%s_%s" % (ukey, own)) or cfg.get(ukey) or dflt, cfg.get("%s_%s" % (pkey, own)) or "",
                "%s_%s" % (pkey, own))
    user = cfg.get(ukey) or (cfg.get("sddc_user") if side == "green" else None) or dflt
    return user, cfg.get(pkey) or "", "%s_%s" % (pkey, site) if "%s_%s" % (pkey, site) in cfg else pkey


def _mig_vc_session(host, user, pw):
    """(session headers, None), or (None, why) when vCenter does not let this sign-in in."""
    if not pw:
        return None, "no password given for %s" % user
    basic = base64.b64encode(("%s:%s" % (user, pw)).encode()).decode()
    st, tok = http("https://%s/api/session" % host, method="POST", headers={"Authorization": "Basic " + basic}, timeout=30)
    if st in (200, 201) and isinstance(tok, str):
        return {"vmware-api-session-id": tok}, None
    if st in (401, 403):
        return None, "the password for %s was refused" % user
    return None, "not reachable (%s)" % (("HTTP %s" % st) if st else str(tok)[:80])


def _mig_vc_esc(name):
    """A name as vCenter keeps it: a % / \\ in an inventory name is stored as %25 %2f %5c."""
    return str(name).replace("%", "%25").replace("/", "%2f").replace("\\", "%5c")


def _mig_vc_segnets(host, H, vim):
    """({port group: NSX segment id}, error) for one vCenter's distributed port groups, from the
    segment id vCenter keeps on each NSX port group (DVPortgroupConfigInfo.segmentId, a policy path)."""
    st, nets = http("https://%s/api/vcenter/network?types=DISTRIBUTED_PORTGROUP" % host, headers=H, timeout=60)
    if st != 200 or not isinstance(nets, list):
        return None, "port group list HTTP %s" % st
    ids, out = sorted({n.get("network") for n in nets if n.get("network")}), {}
    for i in range(0, len(ids), 500):
        got, err = vim.props("DistributedVirtualPortgroup", ids[i:i + 500], ["config.segmentId"])
        if err:
            return None, err
        for m, p in (got or {}).items():
            v = p.get("config.segmentId")
            s = (v.text or "").strip().rstrip("/").rsplit("/", 1)[-1] if v is not None else ""
            if s:
                out[m] = s
    return out, None


def mig_vc_host(cfg, host):
    """(host, session headers) for a Blue vCenter found on Blue's Local Manager. Blue's vCenter account;
    the passwords already entered this run are tried first (one SSO domain), then it is asked for once.
    (host, None) when it cannot sign in."""
    if host in _MIG_VC:
        return host, _MIG_VC[host]
    user = cfg.get("mig_blue_vc_user") or "administrator@vsphere.local"
    tries = [p for p in [os.environ.get("FLEETPARITY_MIG_BLUE_VC_PASSWORD"), cfg.get("mig_blue_vc_password")] if p]
    tries += [p for _h, (u, p) in list(_MIG_VC_PW.items()) if u == user and p and p not in tries]
    H = None
    for p in tries:
        H = vcenter_session(host, user, p)
        if H:
            _MIG_VC_PW[host] = (user, p)
            break
    if not H and not DRY:
        p = getpass.getpass("      vCenter %s '%s' password (found on Blue's Local Manager; Enter skips it): " % (host, user))
        H = vcenter_session(host, user, p) if p else None
        if H:
            _MIG_VC_PW[host] = (user, p)
    if not H:
        _MIG_VC_WHY.setdefault(host, "not signed in as %s: the Blue vCenter passwords this run has were refused" % user)
    _MIG_VC[host] = H
    return host, H


def mig_blue_vcs(cfg, site, bh, BLH):
    """The Blue vCenters at this site: mig_blue_vc_<site> first, then every other vCenter registered on
    Blue's Local Manager here (VMs of the site's segments can be in any of them). A name that resolves
    to an address already listed is the same vCenter. ([hosts], why the Local Manager was not read)"""
    out, why = [], None
    first = str(cfg.get("mig_blue_vc_%s" % site) or "").strip()
    found = []
    if bh and BLH:
        st, b = http("https://%s/api/v1/fabric/compute-managers" % bh, headers=BLH, timeout=30)
        if st == 200 and isinstance(b, dict):
            found = [str(x.get("server") or "").strip() for x in b.get("results") or []
                     if str(x.get("origin_type") or "vCenter") == "vCenter" and x.get("server")]
        else:
            why = "the vCenters registered on %s were not read (HTTP %s)" % (bh, st)
    addr = set()
    for h in [first] + found:
        if not h:
            continue
        try:
            a_ = socket.gethostbyname(h)
        except (OSError, UnicodeError):
            a_ = h.lower()
        if a_ not in addr and h.lower() not in [x.lower() for x in out]:
            addr.add(a_)
            out.append(h)
    return out, why


def _mig_scan_merge(parts):
    """One view of the scans of several vCenters: each VM with its vCenter ("vc"). A vCenter not read is
    listed in "unread"; the view has an "error" only when none was read. Absent is "sure" only when every
    vCenter's port groups were matched by segment id."""
    ok = [p for p in parts if not p.get("error")]
    out = {"host": ", ".join(p["host"] for p in (ok or parts)), "hosts": [p["host"] for p in ok],
           "networks": {}, "how": {}, "vms": {}, "unread": [(p["host"], p["error"]) for p in parts if p.get("error")],
           "error": None if ok else "; ".join("%s: %s" % (p["host"], p["error"]) for p in parts) or "no vCenter",
           "sure": any(p.get("sure") for p in ok) and not any(p.get("id_note") for p in ok),
           "id_note": "; ".join("%s: %s" % (p["host"], p["id_note"]) for p in ok if p.get("id_note")) or None}
    for p in ok:
        for sid, lst in (p.get("vms") or {}).items():
            out["vms"].setdefault(sid, []).extend(dict(v, vc=p["host"]) for v in lst)
        for sid, nets in (p.get("networks") or {}).items():
            out["networks"].setdefault(sid, []).extend("%s/%s" % (p["host"], n) for n in nets)
            out["how"].setdefault(sid, (p.get("how") or {}).get(sid))
    return out


def mig_vc_scan(host, H, segs, vim=None, vim_err=None):
    """VMs attached to the networks of the segments `segs` ({segment id: name}) on one vCenter. A
    segment's network is the NSX port group that carries its segment id (read with `vim`, a SOAP
    session), else the network of its name, also as vCenter keeps it (a / is stored as %2f); two
    segments of one name stay apart by their ids. vCenter's VM list has no network filter, so every
    VM's NICs are read, in parallel. A segment with no network there is absent, which is not the same
    as empty: "sure" says whether absent can be trusted (the port groups' segment ids were read)."""
    out = {"host": host, "networks": {}, "how": {}, "vms": {s: [] for s in segs}, "error": None,
           "sure": False, "id_note": None}
    if not segs:
        return out
    if not H:
        out["error"] = "no vCenter session (login failed)"
        return out
    want = {}
    for sid, n in segs.items():
        for k in {str(n), _mig_vc_esc(n)}:
            want.setdefault(k, set()).add(sid)
    byname, keys = {}, sorted(want)
    for i in range(0, len(keys), 40):
        q = "&".join("names=%s" % urllib.parse.quote(k, safe="") for k in keys[i:i + 40])
        st, nets = http("https://%s/api/vcenter/network?%s" % (host, q), headers=H, timeout=40)
        if st != 200 or not isinstance(nets, list):
            out["error"] = "network list HTTP %s" % st
            return out
        for nw in nets:
            for sid in want.get(nw.get("name"), ()):
                byname.setdefault(sid, set()).add(nw.get("network"))
    segof = {}
    if vim is None:
        out["id_note"] = "segment ids not read: %s" % (vim_err or "no SOAP session")
    else:
        try:
            segof, err = _mig_vc_segnets(host, H, vim)
        except Exception as e:          # the names stand
            segof, err = None, str(e)
        if err:
            out["id_note"], segof = "segment ids not read: %s" % err, {}
    byid = {}
    for m, s in segof.items():
        if s in segs:
            byid.setdefault(s, set()).add(m)
    out["sure"] = bool(byid)
    for sid in segs:
        if sid in byid:
            nets, how = byid[sid], "segment id"
        else:                           # another NSX segment's port group of the same name is not this one
            nets, how = {m for m in byname.get(sid, ()) if m not in segof}, "name"
        if nets:
            out["networks"][sid], out["how"][sid] = sorted(nets), how
    id2seg = {}
    for sid, lst in out["networks"].items():
        for m in lst:
            id2seg.setdefault(m, set()).add(sid)
    if not id2seg:
        return out
    vms = {}
    st, cls = http("https://%s/api/vcenter/cluster" % host, headers=H, timeout=40)
    lists = ["clusters=%s" % c.get("cluster") for c in cls] if st == 200 and isinstance(cls, list) and cls else [""]
    for q in lists:
        st, lst = http("https://%s/api/vcenter/vm%s" % (host, ("?" + q) if q else ""), headers=H, timeout=60)
        if st != 200 or not isinstance(lst, list):
            out["error"] = "VM list HTTP %s" % st
            return out
        for v in lst:
            vms[v.get("vm")] = v

    def nics(vmid):
        st_, info = http("https://%s/api/vcenter/vm/%s" % (host, vmid), headers=H, timeout=40)
        if st_ != 200 or not isinstance(info, dict):
            return vmid, None
        return vmid, [((x or {}).get("backing") or {}).get("network") for x in (info.get("nics") or {}).values()]

    bad, pool = 0, collections.deque(vms)
    lock = threading.Lock()

    def worker():
        nonlocal bad
        while True:
            with lock:
                if not pool:
                    return
                vmid = pool.popleft()
            vid, nets_ = nics(vmid)
            with lock:
                if nets_ is None:
                    bad += 1
                    continue
                v = vms[vid]
                for sid in set().union(*[id2seg.get(n, set()) for n in nets_]):
                    out["vms"][sid].append({"vm": vid, "name": v.get("name"), "power_state": v.get("power_state")})
    ts = [threading.Thread(target=worker) for _ in range(min(16, len(vms)) or 1)]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    if bad:
        out["error"] = "%d VM(s) could not be read" % bad
    return out


def mig_vc_ip(host, H, vmid):
    st, g = http("https://%s/api/vcenter/vm/%s/guest/identity" % (host, vmid), headers=H, timeout=20)
    return g.get("ip_address") if st == 200 and isinstance(g, dict) and g.get("ip_address") else None


def mig_vc_ips(host, H, vmids, workers=16):
    """{vm: guest address} for many VMs, read in parallel: a scope of hundreds of VMs in seconds."""
    import concurrent.futures
    vmids = sorted(set(vmids))
    if not host or not vmids:
        return {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(workers, len(vmids))) as ex:
        got = list(ex.map(lambda x: mig_vc_ip(host, H, x), vmids))
    return {v: ip for v, ip in zip(vmids, got) if ip}


def mig_nsx_vm_index(host, H):
    """{display name: [VM, ...]} for every VM in one Local Manager's inventory, a page at a time: one
    read for a whole scope instead of one per VM. None when not readable."""
    out, cur, n, seen = {}, None, 0, set()
    for _i in range(200):
        q = "page_size=1000" + ("&cursor=%s" % urllib.parse.quote(str(cur)) if cur else "")
        st, b = http("https://%s/api/v1/fabric/virtual-machines?%s" % (host, q), headers=H, timeout=90)
        if st != 200 or not isinstance(b, dict):
            return None
        page = b.get("results") or []
        for v in page:
            out.setdefault(v.get("display_name"), []).append(v)
        n += len(page)
        cur = b.get("cursor")
        total = b.get("result_count")
        if not cur or not page or cur in seen or (str(total).isdigit() and n >= int(total)):
            return out
        seen.add(cur)
    return None


def _mig_mp_pages(host, H, path):
    """Every result of one NSX Manager API list, a page at a time: (list, None) or (None, why)."""
    out, cur, seen = [], None, set()
    for _i in range(500):
        st, b = http("https://%s%s%spage_size=1000%s" % (host, path, "&" if "?" in path else "?",
                                                         ("&cursor=%s" % urllib.parse.quote(str(cur))) if cur else ""),
                     headers=H, timeout=90)
        if st != 200 or not isinstance(b, dict):
            return None, "%s HTTP %s" % (path.split("?")[0], st)
        page = b.get("results") or []
        out += page
        cur = b.get("cursor")
        if not cur or not page or cur in seen:
            return out, None
        seen.add(cur)
    return None, "%s: more than 500 pages" % path.split("?")[0]


def mig_blue_vm_ports(host, H, segs):
    """({segment id: VM ports}, why not) on Blue's Local Manager: NSX's own count of the VM network
    adapters on each segment at this site, whatever vCenter the VMs are in. A segment's logical switch
    is the one tagged with its policy path, else the only switch of its name. A segment with no switch
    found is left out (not known), not counted as 0."""
    ls, why = _mig_mp_pages(host, H, "/api/v1/logical-switches")
    if ls is None:
        return None, why
    seg_of, names = {}, {}
    for x in ls:
        names.setdefault(x.get("display_name"), []).append(x.get("id"))
        for t in x.get("tags") or []:
            p = str(t.get("tag") or "")
            if t.get("scope") == "policyPath" and "/segments/" in p:
                seg_of[x.get("id")] = p.rstrip("/").rsplit("/", 1)[-1]
    tagged = set(seg_of.values())
    for sid, n in segs.items():
        one = names.get(n) or []
        if sid not in tagged and len(one) == 1 and one[0] not in seg_of:
            seg_of[one[0]] = sid
    ports, why = _mig_mp_pages(host, H, "/api/v1/logical-ports?attachment_type=VIF")
    if ports is None:
        return None, why
    out = {s: 0 for s in set(seg_of.values()) if s in segs}
    for p in ports:
        s = seg_of.get(p.get("logical_switch_id"))
        if s in out:
            out[s] += 1
    return out, None


def mig_vm_checks(cfg, site, a, res, st, blue, blm, outdir):
    """Where each row's VMs are, from vCenter, checked against NSX's own count. Blue's are captured into
    the state on every run: address, power state, and the NSX tags Blue's Local Manager holds for them.
    A segment's port group is found by its NSX segment id (by name when the ids are not readable).
    Gates: at cutover no Blue VM on the segment at the other site (KB 330523); before unbridge and retire, none left
    on Blue at all: none in vCenter, and no VM port left on the segment in Blue's Local Manager."""
    checks = []

    def c(item, state, detail=""):
        checks.append({"area": "vcenter", "item": item, "state": state, "detail": str(detail)[:900]})

    def some(xs, k=8):
        return ", ".join(xs[:k]) + (" (+%d more)" % (len(xs) - k) if len(xs) > k else "")

    rows = res.get("rows") or []
    if not rows:
        return checks
    here, there = blue.get("here") or "this site", blue.get("there") or "the other site"
    disp = {s.get("id"): s.get("display_name") or s.get("id") for s in blue.get("segments") or []}
    net = {r["segment"]: disp.get(r["segment"]) or r.get("name") or r["segment"] for r in rows}
    vcs, scans = {}, {}
    key = {"blue": "mig_blue_vc_%s" % site, "blue-remote": "mig_blue_vc_remote_%s" % site}
    same = str(cfg.get(key["blue"]) or "").strip().lower() == str(cfg.get(key["blue-remote"]) or "x").strip().lower()
    if same:
        c("Blue's %s vCenter" % there, "WARN", "%s is the %s vCenter: set it to Blue's %s vCenter; until then the %s checks "
          "are done by hand" % (key["blue-remote"], here, there, there))
    bh, bu, bp = blm
    BLH = _mig_H(bu, bp) if bh else None

    def scan_one(host, H):
        vim, verr = None, None
        if host and H:
            try:
                _h, vim, verr = _mig_vim_host(host)
            except Exception as e:      # by name only
                vim, verr = None, str(e)
        return mig_vc_scan(host, H, net, vim, verr), vim
    for which in ("blue-remote", "green"):
        host, H = mig_vc(cfg, site, which) if not (same and which == "blue-remote") else (None, None)
        vcs[which] = (host, H)
        scans[which] = scan_one(host, H)[0] if host else None
    # Blue here: mig_blue_vc_<site> and every other vCenter registered on Blue's Local Manager here
    blue_hosts, vc_why = mig_blue_vcs(cfg, site, bh, BLH)
    parts, uuids = [], set()
    for h in blue_hosts:
        host, H = mig_vc(cfg, site, "blue") if h == str(cfg.get(key["blue"]) or "").strip() else mig_vc_host(cfg, h)
        vcs[host] = (host, H)
        sc_, vim = scan_one(host, H)
        if vim is not None and getattr(vim, "uuid", None):
            if vim.uuid in uuids:
                continue                # the same vCenter under another name
            uuids.add(vim.uuid)
        parts.append(sc_)
    loc = _mig_scan_merge(parts) if parts else None
    rem, grn = scans["blue-remote"], scans["green"]
    scans["blue"] = parts
    nsx, nsx_why = mig_blue_vm_ports(bh, BLH, net) if BLH else (None, "mig_blue_lm_host_%s not set" % site)
    write_json(outdir, "vm_inventory", dict(scans, nsx={"host": bh, "vm_ports": nsx, "why": nsx_why}))
    for r in rows:                      # for the segments report
        r["nsx_vm_ports"] = nsx[r["segment"]] if nsx is not None and r["segment"] in nsx else ""

    def vms_of(scan, sid):
        return None if scan is None or scan.get("error") else scan["vms"].get(sid, [])

    if a.mode in ("build", "cutover", "rollback"):
        if vc_why:
            c("Blue vCenters at %s" % here, "WARN", "%s: only %s is read" % (vc_why, key["blue"]))
        for h_, e_ in (loc or {}).get("unread") or []:
            if not (loc or {}).get("error"):
                c("Blue vCenter %s" % h_, "WARN", "not read (%s): its VMs are not captured or moved, and unbridge and "
                  "retire refuse the scope's segments until it is" % e_)
        if loc is None:
            c("Blue vCenter", "WARN", "set %s: until then VM addresses and NSX tags are not captured" % key["blue"])
        elif loc.get("error"):
            c("Blue vCenter %s" % loc["host"], "WARN", "%s: VMs not captured this run" % loc["error"])
        else:
            found = [s for s in net if s in loc["networks"]]
            byid = sum(1 for s in found if loc["how"].get(s) == "segment id")
            c("Blue vCenter %s" % loc["host"], "INFO", "%d VM(s) on %d of the %d segments; port groups found for %d "
              "(%d by NSX segment id, %d by name)%s" % (
                  len({v["vm"] for s in net for v in loc["vms"].get(s) or []}), sum(1 for s in net if loc["vms"].get(s)),
                  len(net), len(found), byid, len(found) - byid, "; %s" % loc["id_note"] if loc.get("id_note") else ""))
            miss = sorted(net[s] for s in net if s not in loc["networks"])
            if miss:
                c("Blue vCenter %s port groups" % loc["host"], "WARN", "none for %d segment(s): %s. %s" % (
                    len(miss), some(miss), "No host of this vCenter carries them: their VMs are not seen here"
                    if loc.get("sure") else "Not found by name either, and the NSX segment ids were not read: "
                    "their VMs are not seen"))
        if nsx is None:
            c("Blue Local Manager VM ports", "WARN" if BLH else "INFO",
              "not read (%s): VMs are counted from vCenter only" % nsx_why)
        elif loc is not None and not loc.get("error"):
            gap = ["%s (%d)" % (net[s], n) for s, n in sorted(nsx.items(), key=lambda x: net[x[0]])
                   if n and not loc["vms"].get(s)]
            if gap:
                c("Blue VMs vCenter does not show", "WARN", "%s: VM ports in Blue's %s Local Manager %s, no VM in %s. "
                  "They are in a vCenter not registered there or not readable, so they are not captured or moved, and "
                  "unbridge and retire refuse these segments" % (some(gap), here, bh, loc["host"]))
    # every Blue VM of the scope at once: addresses in parallel per vCenter, NSX tags from one inventory read
    allb = [v for r in rows for v in vms_of(loc, r["segment"]) or []]
    ips = {}
    for h_ in sorted({v.get("vc") for v in allb if v.get("vc")}):
        got_ = mig_vc_ips(h_, (vcs.get(h_) or (None, None))[1], [v["vm"] for v in allb if v.get("vc") == h_])
        ips.update({(h_, k): ip_ for k, ip_ in got_.items()})
    bidx = mig_nsx_vm_index(bh, BLH) if BLH and allb else None
    for r in rows:
        sid, nm = r["segment"], net[r["segment"]]
        seg = mig_state_seg(st, sid)
        on_blue, on_remote, on_green = vms_of(loc, sid), vms_of(rem, sid), vms_of(grn, sid)
        ports = nsx.get(sid) if nsx is not None else None
        # values only, no read timestamps: a run that finds the same VMs leaves the state unchanged
        for v in on_blue or []:
            rec = seg["vms"].setdefault(v["name"], {"first_seen": now()})
            rec.update(vm=v["vm"], vc=v.get("vc"), power_state=v.get("power_state"), where="blue")
            ip = ips.get((v.get("vc"), v["vm"]))
            if ip:
                rec["ip"] = ip
            if not BLH:
                rec["tags_note"] = "mig_blue_lm_host_%s not set" % site
                continue
            hits = [x for x in bidx.get(v["name"], []) if x.get("display_name") == v["name"]] \
                if bidx is not None else mig_nsx_vms(bh, BLH, v["name"])
            if hits is None:
                rec["tags_note"] = "Blue Local Manager not readable"
            elif len(hits) != 1:
                rec["tags_note"] = "%d VMs named %s in Blue's NSX inventory" % (len(hits), v["name"])
            else:
                tags = [{"scope": str(t.get("scope") or ""), "tag": str(t.get("tag") or "")}
                        for t in hits[0].get("tags") or []]
                if rec.get("tags") != tags and rec.get("tags_back") != "owed":
                    rec["tags"], rec["tags_read"] = tags, now()     # back from Green: the capture stands until it is on Blue
                rec.pop("tags_note", None)
        for v in on_green or []:
            rec = seg["vms"].get(v["name"])
            if rec is not None and rec.get("where") != "green":
                rec["where"], rec["on_green_since"] = "green", now()
        new = sorted(v["name"] for v in on_green or [] if v["name"] not in seg["vms"])
        if new:
            c("%s VMs on Green with no Blue capture" % sid, "WARN", "%s%s: on Green before the tool saw them on Blue; "
              "check their NSX tags by hand" % (", ".join(new[:6]), " ..." if len(new) > 6 else ""))
        # the routing moves to Green only once every VM of the segment is on Green, at both sites, unless the site
        # allows a cutover with VMs still on Blue here (they reach Green's gateway over the bridge; KB 330523 still holds)
        strict = a.mode == "cutover" and not _mig_true(_mig_key(cfg, "mig_cutover_with_blue_vms", site))
        if a.mode == "cutover" and not strict:
            item = "KB 330523: no Blue VM on %s at %s" % (sid, there)
            if rem is None:
                c(item, "WARN", "set %s; until then check Blue's %s vCenter by hand" % (key["blue-remote"], there))
            elif rem.get("error"):
                c(item, "FAIL", "Blue's %s vCenter not readable: %s" % (there, rem["error"]))
            elif on_remote:
                c(item, "FAIL", "%d at %s: %s. Blue's Connectivity OFF cuts the segment's cross-location traffic: "
                  "move them to %s first" % (len(on_remote), there, ", ".join(sorted(v["name"] for v in on_remote)[:6]), here))
            elif sid not in rem["networks"] and not rem.get("sure"):
                c(item, "WARN", "no port group named %s in Blue's %s vCenter %s, and its NSX segment ids were not read "
                  "(%s): check it by hand" % (nm, there, rem["host"], rem.get("id_note") or ""))
            else:
                c(item, "PASS", "none%s" % ("" if sid in rem["networks"] else
                                            " (no port group for it in Blue's %s vCenter)" % there))
        if a.mode in ("unbridge", "retire") or strict:
            why = {"unbridge": "without the bridge they lose Green's gateway",
                   "retire": "retiring deletes the segment under them",
                   "cutover": "the routing moves only once all its VMs are on Green (mig_cutover_with_blue_vms_%s: false)"
                              % site}[a.mode]
            for label, scan, lst, k in ((here, loc, on_blue, "blue"), (there, rem, on_remote, "blue-remote")):
                item = "%s empty on Blue at %s" % (sid, label)
                p_ = ports if k == "blue" else None
                if scan is None:
                    c(item, "FAIL" if k == "blue" else "WARN",
                      "set %s%s" % (key[k], "" if k == "blue" else "; until then check it by hand"))
                elif scan.get("error"):
                    c(item, "FAIL", "not readable: %s" % scan["error"])
                elif scan.get("unread"):
                    c(item, "FAIL", "Blue vCenter %s not read: it cannot be shown empty" % ", ".join(h_ for h_, _e in scan["unread"]))
                elif lst:
                    c(item, "FAIL", "%d VM(s): %s. Move them to Green first: %s" % (
                        len(lst), ", ".join(sorted(v["name"] for v in lst)[:6]), why))
                elif p_:
                    c(item, "FAIL", "%s shows none, but Blue's Local Manager %s still has %d VM port(s) on it: VMs in "
                      "a vCenter the tool does not read. Move them to Green first: %s" % (scan["host"], bh, p_, why))
                elif sid in scan["networks"]:
                    c(item, "PASS", "no VM on %s%s" % (nm, "" if k != "blue" else " (NSX: 0 VM ports)" if p_ == 0 else
                                                       " (NSX VM ports not read: %s)" % (nsx_why or "no switch found")))
                elif k == "blue":
                    c(item, "PASS" if p_ == 0 else "FAIL", "no port group for it in %s, and %s" % (
                        scan["host"], "no VM port on it in Blue's Local Manager" if p_ == 0 else
                        "its VM ports in Blue's Local Manager were not read (%s): it cannot be shown empty"
                        % (nsx_why or "no switch found")))
                elif scan.get("sure"):
                    c(item, "PASS", "no port group for it in %s: no VM there can be on it" % scan["host"])
                else:
                    c(item, "WARN", "no port group named %s in %s, and its NSX segment ids were not read (%s): "
                      "check it by hand" % (nm, scan["host"], scan.get("id_note") or ""))
        elif on_blue is not None:
            c("%s VMs" % sid, "INFO", "%s%s%s%s" % (
                ("%d on Blue" % len(on_blue)) if sid in loc["networks"] else "Blue: no port group in %s" % loc["host"],
                "" if ports is None else " (NSX: %d VM port%s)" % (ports, "" if ports == 1 else "s"),
                ", %d on Green" % len(on_green) if on_green is not None else "",
                "; addresses and NSX tags captured" if on_blue else ""))
    return checks


def mig_drop_checks(cfg, site, res, objs):
    """Before a Green segment of mig_drop_plan is deleted: the site's Green vCenter must show no VM on
    it. Unreadable, or a VM on it: that delete is held with the reason."""
    drop = res.get("drop") or []
    if not drop:
        return []
    host, H = mig_vc(cfg, site, "green")
    vim, verr = None, None
    if host and H:
        try:
            _h, vim, verr = _mig_vim_session(cfg, site, "green")
        except Exception as e:      # by name only
            vim, verr = None, str(e)
    scan = mig_vc_scan(host, H, {r["segment"]: r.get("name") or r["segment"] for r in drop}, vim, verr) if host else None
    held, net = {}, {r["segment"]: r.get("subnet") or r["segment"] for r in drop}
    for r in drop:
        sid = r["segment"]
        if scan is None:
            held[sid] = "set mig_green_vc_%s: the tool sees a segment empty before it deletes it" % site
        elif scan.get("error"):
            held[sid] = "Green vCenter %s not readable (%s): it cannot be shown empty" % (host, scan["error"])
        elif scan["vms"].get(sid):
            vs = sorted(v["name"] for v in scan["vms"][sid])
            held[sid] = "%d VM(s) on it in %s: %s. It stays: list them in mig_return_vms_%s first" % (
                len(vs), host, ", ".join(vs[:6]), site)
    for o in objs:
        if o.get("drop") and o["segment"] in held and not o.get("needs"):
            o["needs"] = held[o["segment"]]
    if not held:
        return []
    return [{"area": "plan", "item": "out of the scope, held", "state": "WARN",
             "detail": "%d not deleted: %s" % (len(held), "; ".join("%s: %s" % (net[k], v) for k, v in sorted(held.items())[:4]))}]


# ---------------------------------------------------------------- migpath: NSX VM tags
def _mig_tagset(tags):
    return {(str(t.get("scope") or ""), str(t.get("tag") or "")) for t in tags or []}


def mig_nsx_vms(host, H, name):
    """VMs with this exact display name on one Local Manager; None when not readable."""
    st, b = http("https://%s/api/v1/fabric/virtual-machines?display_name=%s" % (host, urllib.parse.quote(name)),
                 headers=H, timeout=30)
    return [v for v in _res(b) if v.get("display_name") == name] if st == 200 else None


def mig_tags_apply(host, H, captured, commit, index=None, where="Green"):
    """Blue's NSX tags onto the same VMs on Green's Local Manager (or, where="Blue", back on Blue's for a
    VM returned there). add_tags only appends: a tag already on the VM is never removed. Each write is
    read back. `index`: the Local Manager's VM inventory read once this run (mig_nsx_vm_index); without
    it each VM is looked up on its own."""
    out = []
    for name, cap in sorted((captured or {}).items()):
        want = [t for t in cap.get("tags") or [] if t.get("tag") or t.get("scope")]
        row = {"vm": name, "segment": cap.get("segment"), "action": None, "detail": "", "add": [], "side": where}
        out.append(row)
        if not want:
            row["action"], row["detail"] = "UNCHANGED", "no NSX tags on Blue"
            continue
        vms = ([x for x in index.get(name, []) if x.get("display_name") == name] if index is not None
               else mig_nsx_vms(host, H, name))
        if vms is None:
            row["action"], row["detail"] = "ERROR", "%s VM list not readable" % where
            continue
        if not vms:
            row["action"], row["detail"] = "PENDING", "not in %s's NSX inventory yet" % where
            continue
        if len(vms) > 1:
            row["action"], row["detail"] = "BLOCKED", "%d VMs named %s on %s: rename one" % (len(vms), name, where)
            continue
        have = _mig_tagset(vms[0].get("tags"))
        missing = [t for t in want if (str(t.get("scope") or ""), str(t.get("tag") or "")) not in have]
        row["external_id"] = vms[0].get("external_id")
        if cap.get("placed") and cap["placed"] == row["external_id"]:
            # placed once on this VM: from then on its tags are the Green team's, never fought over
            row["action"], row["detail"] = "UNCHANGED", "placed %s%s" % (
                cap.get("placed_at") or "earlier", "; %d removed on Green since, left alone" % len(missing) if missing else "")
            continue
        if not missing:
            row["action"], row["detail"] = "UNCHANGED", "%d tag(s) present" % len(want)
            continue
        row["add"] = [{"scope": str(t.get("scope") or ""), "tag": str(t.get("tag") or "")} for t in missing]
        row["action"], row["detail"] = "ADD", "%d tag(s): %s" % (len(missing), ", ".join(
            "%s=%s" % (t["scope"], t["tag"]) for t in row["add"][:4]))
        if commit:
            st, b = http("https://%s/api/v1/fabric/virtual-machines?action=add_tags" % host, method="POST",
                         headers=H, body={"external_id": row["external_id"], "tags": row["add"]}, timeout=30)
            again = mig_nsx_vms(host, H, name) or [{}]
            if st not in (200, 201, 204) or not _mig_tagset(want) <= _mig_tagset(again[0].get("tags")):
                row["action"], row["detail"] = "ERROR", "add_tags HTTP %s; tags not all present after" % st
            else:
                row["detail"] += ", read back"
    return out


def mig_tag_capture(res, st):
    """{vm: {"tags", "segment", "placed", "placed_at"}}: the NSX tags captured on Blue for the VMs of this
    run's rows, and where the tool has already placed them on Green."""
    out = {}
    for r in res.get("rows") or []:
        for n, v in sorted(((st["segments"].get(r["segment"]) or {}).get("vms") or {}).items()):
            if v.get("tags"):
                out[n] = {"tags": v["tags"], "segment": r["segment"], "placed": v.get("tags_placed_ext"),
                          "placed_at": v.get("tags_on_green")}
    return out


def mig_tag_checks(rows, mode, where="Green"):
    """Green's firewall matches on these tags, so an ambiguous or failed VM stops a cutover. where="Blue":
    the tags of VMs returned to Blue, going back on Blue's Local Manager."""
    by = collections.defaultdict(list)
    for t in rows or []:
        by[t["action"]].append(t)
    parts = ["%d %s (%s%s)" % (len(by[k]), label, ", ".join(t["vm"] for t in by[k][:5]), " ..." if len(by[k]) > 5 else "")
             for k, label in (("ADD", "to add"), ("UNCHANGED", "in place"), ("PENDING", "not on %s yet" % where))
             if by.get(k)]
    out = [{"area": "tags", "item": "NSX tags from Blue on Green" if where == "Green" else "NSX tags back on Blue",
            "state": "INFO", "detail": "; ".join(parts)}] if parts else []
    for t in by.get("UNCHANGED", []):
        if "left alone" in t["detail"]:
            out.append({"area": "tags", "item": "NSX tags on %s for %s" % (where, t["vm"]), "state": "INFO", "detail": t["detail"]})
    for t in by.get("BLOCKED", []) + by.get("ERROR", []):
        out.append({"area": "tags", "item": "NSX tags on %s for %s" % (where, t["vm"]),
                    "state": "FAIL" if mode == "cutover" and where == "Green" else "WARN", "detail": t["detail"]})
    return out


# ---------------------------------------------------------------- migpath: probes
class MigProbe(object):
    """A ping kept running across a change. Loss is counted from the moment the change starts (mark)
    to two packets short of the end, which were still in flight when the probe stopped."""
    INTERVAL = 0.2

    def __init__(self, ip, label, judge):
        self.ip, self.label, self.judge = ip, label, judge
        self.lines, self.proc, self.error, self.t, self.since = [], None, None, None, None

    def start(self):
        try:
            self.proc = subprocess.Popen(["ping", "-n", "-O", "-i", str(self.INTERVAL), "-W", "1", self.ip],
                                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, universal_newlines=True)
        except Exception as e:
            self.error = "ping not started: %s" % e
            return self
        self.t = threading.Thread(target=self._read)
        self.t.daemon = True
        self.t.start()
        return self

    def _read(self):
        for line in self.proc.stdout:
            self.lines.append(line)

    def _seqs(self, answered=None):
        out = []
        for ln in list(self.lines):
            m = re.search(r"icmp_seq=(\d+)", ln)
            if m and (answered is None or answered == ("bytes from" in ln)):
                out.append(int(m.group(1)))
        return out

    def replies(self):
        return len(self._seqs(True))

    def mark(self):
        s = self._seqs()
        self.since = (max(s) + 1) if s else 1

    def answered_before(self):
        return any(q < (self.since or 0) for q in self._seqs(True))

    def recovered(self, n=5):
        seen = [ln for ln in list(self.lines) if "icmp_seq=" in ln][-n:]
        return len(seen) == n and all("bytes from" in ln for ln in seen)

    def alive(self):
        return self.proc is not None and self.proc.poll() is None

    def kill(self):
        if self.alive():
            try:
                self.proc.kill()
            except Exception:
                pass

    def stop(self):
        if self.proc:
            try:
                self.proc.send_signal(signal.SIGINT)
                self.proc.wait(timeout=5)
            except Exception:
                self.proc.kill()
            if self.t:
                self.t.join(timeout=5)
        r = mig_ping_summary(self.lines, self.INTERVAL, self.error, self.since)
        r.update(ip=self.ip, label=self.label, judge=self.judge)
        return r


def mig_ping_summary(lines, interval, error=None, since=None):
    """Packets judged, lost, and the longest run of consecutive losses in seconds, from `since` (the
    change) to two packets before the last one sent. `answered_before`: it replied before the change."""
    if error:
        return {"error": error}
    got, seen, sent = set(), set(), None
    for ln in lines:
        m = re.search(r"icmp_seq=(\d+)", ln)
        if m:
            seen.add(int(m.group(1)))
            if "bytes from" in ln:
                got.add(int(m.group(1)))
        m = re.search(r"(\d+) packets transmitted", ln)
        if m:
            sent = int(m.group(1))
    if not seen and not sent:
        return {"error": "no ping output: %s" % ("".join(lines[:2]).strip()[:120] or "none")}
    first = 0 if 0 in seen else 1
    last = max(seen) if seen else first
    if sent:
        last = max(last, first + sent - 1)
    start = max(first, since or first)
    window = list(range(start, last - 1))
    lost = [q for q in window if q not in got]
    longest = run = 0
    prev = None
    for q in lost:
        run = run + 1 if prev is not None and q == prev + 1 else 1
        longest = max(longest, run)
        prev = q
    return {"judged": len(window), "lost": len(lost), "longest_gap_s": round(longest * interval, 1),
            "replies": len(got), "answered_before": any(q < start for q in got)}


def mig_probe_targets(cfg, site, mode, rows, st):
    """(ip, label, judge) to ping across a change. Production addresses (mig_probe_ips_<site>) are
    judged strictly: any loss fails the run. The segment's gateway and a few of its VMs, with the
    addresses captured from Blue's vCenter, are measured: a short gap is expected when the gateway moves."""
    out, seen = [], set()

    def add(ip, label, judge):
        try:
            ip = str(ipaddress.ip_address(str(ip).strip()))
        except ValueError:
            return
        if ip not in seen and len(out) < 40:
            seen.add(ip)
            out.append((ip, label, judge))

    for ip in _mig_items(_mig_key(cfg, "mig_probe_ips", site)):
        add(ip, "production %s" % ip, "production")
    if mode in ("build", "cutover", "rollback", "unbridge"):
        k = int(cfg.get("mig_probe_vms") or 3)
        for r in rows or []:
            if mode in ("cutover", "rollback") and r.get("gw"):
                add(r["gw"], "gateway %s %s" % (r["segment"], r["gw"]), "segment")
            vms = ((st.get("segments") or {}).get(r["segment"]) or {}).get("vms") or {}
            picked = 0
            for n, v in sorted(vms.items()):
                if picked >= k:
                    break
                try:
                    inside = r.get("net") is not None and ipaddress.ip_address(v.get("ip") or "") in r["net"]
                except ValueError:
                    inside = False
                if inside and str(v.get("power_state") or "POWERED_ON") == "POWERED_ON":
                    add(v["ip"], "VM %s %s" % (n, v["ip"]), "segment")
                    picked += 1
    return out


def mig_probes_start(targets, ctx):
    """Start the probes, give each up to 3 s to answer, then mark the start of the change."""
    probes = [MigProbe(ip, label, judge).start() for ip, label, judge in targets]
    ctx["probes"] = probes
    t0 = time.time()
    while time.time() - t0 < 3 and any(p.alive() and p.replies() < 3 for p in probes):
        time.sleep(0.2)
    for p in probes:
        p.mark()
    if probes:
        log("-- %d probe(s) running: %s" % (len(probes), ", ".join(p.ip for p in probes[:6])
                                            + (" ..." if len(probes) > 6 else "")))
    return probes


def mig_probes_finish(probes, cfg):
    """At least 3 s after the change, then until every probe that answered before it has answered
    five in a row again, at most mig_probe_tail seconds (default 120)."""
    if not probes:
        return []
    tail = int(cfg.get("mig_probe_tail") or 120)
    time.sleep(3)
    t0 = time.time()
    while time.time() - t0 < tail and any(p.alive() and p.answered_before() and not p.recovered() for p in probes):
        time.sleep(0.5)
    return [p.stop() for p in probes]


def mig_probe_checks(results, mode):
    out = []
    for r in results or []:
        item = "probe %s" % r.get("label")
        if r.get("error"):
            out.append({"area": "probe", "item": item, "state": "WARN", "detail": r["error"]})
            continue
        nums = "lost %d of %d, longest gap %.1fs" % (r["lost"], r["judged"], r["longest_gap_s"])
        if not r.get("answered_before"):
            out.append({"area": "probe", "item": item, "state": "WARN" if r["judge"] == "production" else "INFO",
                        "detail": "no answer before the change (down, or ICMP blocked): not judged"})
        elif r["judge"] == "production":
            out.append({"area": "probe", "item": item, "state": "FAIL" if r["lost"] else "PASS", "detail": nums})
        elif mode in ("cutover", "rollback"):
            out.append({"area": "probe", "item": item, "state": "INFO", "detail": nums + " (the gateway moved)"})
        else:
            out.append({"area": "probe", "item": item, "state": "WARN" if r["lost"] else "PASS", "detail": nums})
    return out


# ---------------------------------------------------------------- migpath: overlay tunnels
def _mig_short(n):
    return str(n or "").strip().lower().split(".")[0]


def mig_green_hosts(cfg, site):
    """(cluster, [host names], why not): the connected hosts of the cluster VMs land on in Green's vCenter
    (mig_green_cluster_<site>, or its only cluster)."""
    gvc, GH = mig_vc(cfg, site, "green")
    if not gvc:
        return None, [], "set mig_green_vc_%s" % site
    if not GH:
        return None, [], "%s: %s" % (gvc, _MIG_VC_WHY.get(gvc) or "no session")
    st1, cls = http("https://%s/api/vcenter/cluster" % gvc, headers=GH, timeout=40)
    if st1 != 200 or not isinstance(cls, list):
        return None, [], "%s: cluster list not readable (HTTP %s)" % (gvc, st1)
    want = _mig_key(cfg, "mig_green_cluster", site)
    hit = [x for x in cls if not want or x.get("name") == want]
    if len(hit) != 1:
        return None, [], "%s: %s" % (gvc, ("no cluster named %s" % want) if want else
                                     "%d clusters: set mig_green_cluster_%s" % (len(hit), site))
    st2, hl = http("https://%s/api/vcenter/host?clusters=%s" % (gvc, hit[0].get("cluster")), headers=GH, timeout=40)
    if st2 != 200 or not isinstance(hl, list):
        return hit[0].get("name"), [], "%s: hosts of %s not readable (HTTP %s)" % (gvc, hit[0].get("name"), st2)
    return hit[0].get("name"), sorted(str(h.get("name")) for h in hl if h.get("connection_state") == "CONNECTED"), None


def _mig_pool_subnets(lmhost, H, pid, cache):
    """[(cidr, gateway)] of an IP pool on a Local Manager, by policy path or by id."""
    pid = str(pid or "")
    if not pid:
        return []
    if pid not in cache:
        subs = []
        tries = (["/policy/api/v1%s/ip-subnets" % pid] if pid.startswith("/") else
                 ["/policy/api/v1/infra/ip-pools/%s/ip-subnets" % pid, "/api/v1/pools/ip-pools/%s" % pid])
        for path in tries:
            st_, b = http("https://%s%s" % (lmhost, path), headers=H, timeout=30)
            if st_ != 200:
                continue
            items = _res(b) or ((b.get("subnets") if isinstance(b, dict) else None) or [])
            subs = [(str(x.get("cidr")), x.get("gateway_ip")) for x in items if x.get("cidr")]
            if subs:
                break
        cache[pid] = subs
    return cache[pid]


def _mig_tn_tep_subnets(lmhost, H, tn, cache):
    """[(cidr, gateway)] a transport node's tunnel endpoints are on: its IP pool, or its static list."""
    out = []
    for hs in ((tn or {}).get("host_switch_spec") or {}).get("host_switches") or []:
        spec = hs.get("ip_assignment_spec") or {}
        pid = spec.get("ip_pool_id") or spec.get("ip_pool")
        if pid:
            out += _mig_pool_subnets(lmhost, H, pid, cache)
        for ip in spec.get("ip_list") or []:
            try:
                out.append((str(ipaddress.ip_interface("%s/%s" % (ip, spec.get("subnet_mask"))).network),
                            spec.get("default_gateway")))
            except ValueError:
                pass
    return out


def _mig_tn_endpoints(lmhost, H, tn_id, cache):
    """[(ip, cidr, gateway, vmk)] of a transport node's tunnel endpoints as realized on it (its state)."""
    key = "state:%s" % tn_id
    if key not in cache:
        out = []
        st_, b = http("https://%s/api/v1/transport-nodes/%s/state" % (lmhost, tn_id), headers=H, timeout=40)
        if st_ == 200 and isinstance(b, dict):
            for hs in b.get("host_switch_states") or []:
                for ep in hs.get("endpoints") or []:
                    ip, mask = ep.get("ip"), ep.get("subnet_mask")
                    try:
                        cidr = str(ipaddress.ip_interface("%s/%s" % (ip, mask)).network) if ip and mask else None
                    except ValueError:
                        cidr = None
                    out.append((str(ip or ""), cidr, ep.get("default_gateway") or None, ep.get("device_name")))
        cache[key] = out
    return cache[key]


def mig_leaf_tables(cfg, site, nets, cache):
    """{leaf: {net: [routing tables holding exactly that net] or None}} on the route leaves, read with `ip route`
    (any account). Shows whether the leaves the edges sit on can route to each tunnel subnet at all."""
    key = "leaf:%s" % ",".join(nets)
    if key in cache:
        return cache[key]
    out = {}
    leaves = _mig_items(_mig_key(cfg, "mig_route_leaves", site))
    if leaves:
        user, pw = _mig_leaf_creds(cfg)
        cmd = "PATH=$PATH:/usr/sbin:/sbin; " + " ".join("ip -j route show table all %s; echo '#END#';" % n for n in nets)
        for h in leaves:
            ok, o = ssh_exec(h, user, pw, cmd, timeout=20)
            parts = str(o).split("#END#") if ok else []
            row = {}
            for k, n in enumerate(nets):
                try:
                    d = json.loads(parts[k].strip() or "[]") if k < len(parts) else None
                except ValueError:
                    d = None
                row[n] = None if not isinstance(d, list) else sorted(
                    {str(e.get("table") or "main") for e in d if str(e.get("dst")) == n})
            out[h.split(".")[0]] = row
    cache[key] = out
    return out


def mig_tunnel_why(cfg, site, lmhost, H, htn, etn, t, cache):
    """Why one tunnel is down, from its two endpoints as NSX realized them (address, subnet, gateway), the pools
    they come from, and the routes the leaves hold for each subnet."""
    lip, rip = str(t.get("local_ip") or ""), str(t.get("remote_ip") or "")
    diag = str((t.get("bfd") or {}).get("diagnostic") or "").strip()

    def where(ip, subs):
        for cidr, gw in subs:
            try:
                if ipaddress.ip_address(ip) in ipaddress.ip_network(cidr, strict=False):
                    return cidr, gw
            except ValueError:
                pass
        return None, None
    hep = next((e for e in _mig_tn_endpoints(lmhost, H, htn.get("id"), cache) if e[0] == lip), None)
    eep = next((e for e in _mig_tn_endpoints(lmhost, H, etn.get("id"), cache) if e[0] == rip), None) if etn else None
    pc, pg = where(lip, _mig_tn_tep_subnets(lmhost, H, htn, cache))
    qc, qg = where(rip, _mig_tn_tep_subnets(lmhost, H, etn, cache)) if etn else (None, None)
    hc, hg = (hep[1] if hep else None) or pc, (hep[2] if hep else pg)
    ec, eg = (eep[1] if eep else None) or qc, (eep[2] if eep else qg)
    pair = "%s%s -> %s%s" % (lip or "?", " (%s)" % hep[3] if hep and hep[3] else "", rip or "?",
                             (", BFD %s" % diag) if diag and diag.lower() != "no diagnostic" else "")
    try:
        same = bool(hc) and ipaddress.ip_address(rip) in ipaddress.ip_network(hc, strict=False)
    except ValueError:
        same = False
    if same:
        return "%s: one subnet, %s: its VLAN is not carried between them, or the MTU is under 1600" % (pair, hc)
    if hc and not hg:
        if pg:
            return ("%s: the host's tunnel endpoint has no default gateway, though its pool now has %s (%s): the host was "
                    "prepared before the gateway was set. Resync NSX on each host of the cluster" % (pair, pg, hc))
        return ("%s: the host's tunnel pool %s has no gateway, so its tunnels reach only their own subnet. Set the gateway "
                "on that pool, then resync NSX on each host" % (pair, hc))
    if ec and not eg:
        return "%s: the edge's tunnel endpoint (%s) has no default gateway, so it cannot answer %s" % (pair, ec, hc or lip)
    if hc and ec:
        tables = mig_leaf_tables(cfg, site, [hc, ec], cache)
        seen = []
        for leaf, row in sorted(tables.items()):
            a_, b_ = row.get(hc), row.get(ec)
            if a_ is None or b_ is None:
                continue
            if not a_:
                seen.append("%s holds %s (%s) but no route to %s" % (leaf, ec, ", ".join(b_) or "no table", hc))
            elif b_ and not set(a_) & set(b_):
                seen.append("%s holds %s in table %s but %s only in %s: different VRFs" % (leaf, ec, ", ".join(b_), hc,
                                                                                         ", ".join(a_)))
        lead = "%s: %s (gateway %s) and %s (gateway %s) do not reach each other" % (pair, hc, hg, ec, eg)
        if seen:
            return lead + ". " + "; ".join(seen) + ". Route them in one VRF"
        return lead + (". The leaves route both: check MTU 1600 or more on that path (vmkping -d -s 1572) and that "
                       "UDP 6081 is allowed" if tables else ". On the switches: a route between them in one VRF, MTU "
                       "1600 or more, UDP 6081 allowed")
    return "%s: the switches between them do not carry it (route, MTU 1600 or more, UDP 6081)" % pair


def mig_tunnel_checks(cfg, site, lmhost, H, lm, res, mode):
    """Overlay tunnels from each host VMs land on (the Green vCenter's cluster) to the Green bridge edges and the
    Tier-0's edges at this site, as Green's Local Manager reports them. A VM on a host whose tunnels to them are
    down reaches nothing past its own segment: not Blue's gateway over the bridge before the cutover, not the
    Tier-0 after it. A down tunnel is explained from its two endpoints and their pools. Refuses a cutover while
    a host's tunnels to the Tier-0's edges are down. Returns (checks, {host: {"ok": True|False|None, "why"}});
    --move lands VMs only on hosts whose tunnels are not known to be down."""
    checks, out = [], {}

    def c(item, state, detail=""):
        checks.append({"area": "tunnels", "item": item, "state": state, "detail": str(detail)[:900]})

    groups = [(g, e) for g, e in (("bridge", _mig_items(_mig_key(cfg, "mig_bridge_edges", site))),
                                  ("Tier-0", list(res.get("t0_edges") or []))) if e]
    if not lmhost or not groups:
        return checks, out
    cl, names, why = mig_green_hosts(cfg, site)
    if why:
        c("overlay tunnels to the edges", "WARN", "not checked: %s" % why)
        return checks, out
    tns = _res(_nb(lm, "transport_nodes"))
    if not tns:
        c("overlay tunnels to the edges", "WARN", "not checked: transport nodes on %s not readable" % lmhost)
        return checks, out
    by = {}
    for t in tns:
        info = t.get("node_deployment_info") or {}
        for n in [t.get("display_name"), info.get("fqdn")] + list(info.get("ip_addresses") or []):
            if _mig_short(n):
                by.setdefault(_mig_short(n), t)
    cache = {}
    for hname in names:
        hs = _mig_short(hname)
        tn = by.get(hs)
        if not tn:
            c("%s tunnels to the edges" % hs, "WARN", "%s is not a transport node on %s: not checked" % (hname, lmhost))
            continue
        st_, b = http("https://%s/api/v1/transport-nodes/%s/tunnels" % (lmhost, tn.get("id")), headers=H, timeout=40)
        tl = b.get("tunnels") if st_ == 200 and isinstance(b, dict) else None
        if not isinstance(tl, list):
            c("%s tunnels to the edges" % hs, "WARN", "not readable on %s (HTTP %s)" % (lmhost, st_))
            out[hs] = {"ok": None, "why": "not readable"}
            continue
        bad, good, none_ = [], [], []
        for g, es in groups:
            for e in es:
                et = by.get(_mig_short(e))
                mine = [t for t in tl if _mig_short(t.get("remote_node_display_name")) == _mig_short(e)
                        or (et is not None and t.get("remote_node_id") == et.get("id"))]
                up = [t for t in mine if str(t.get("status") or "").upper() == "UP"]
                down = [t for t in mine if str(t.get("status") or "").upper() == "DOWN"]
                if down:            # NSX makes tunnels on demand: only one that exists and is down is a fault
                    bad.append((g, e, mig_tunnel_why(cfg, site, lmhost, H, tn, et, down[0], cache)
                                + ("" if not up else " (%d of %d up)" % (len(up), len(mine)))))
                elif up:
                    good.append(e)
                else:
                    none_.append(e)
        out[hs] = {"ok": False if bad else (True if not none_ else None), "why": bad[0][2] if bad else ""}
        if not bad:
            c("%s tunnels to the edges" % hs, "PASS" if good else "INFO", "; ".join(x for x in (
                "up to %s" % ", ".join(good) if good else "",
                "none yet to %s (NSX makes them once a VM of a segment there needs them)" % ", ".join(none_)
                if none_ else "") if x))
            continue
        t0bad = [e for g, e, _w in bad if g == "Tier-0"]
        c("%s tunnels to the edges" % hs, "FAIL" if mode == "cutover" and t0bad else "WARN",
          "down to %s. %s%s" % (", ".join(e for _g, e, _w in bad), bad[0][2],
                                ". After a cutover its VMs reach nothing past their segment" if t0bad else
                                ". A VM there cannot reach Blue's gateway over the bridge"))
    return checks, out


# ---------------------------------------------------------------- migpath: tunnel pool gateways
# The edges' and the hosts' tunnel endpoints can sit in different subnets (VCF puts each domain's hosts on their
# own tunnel VLAN). Then every tunnel between them is routed, and each side's pool needs a gateway: without one
# its endpoints reach only their own subnet, and the VMs on those hosts reach nothing past their segment. The
# gateway is read from the leaves (the address they share in that subnet, the VRR vlanN-v0), never guessed.

def mig_leaf_addrs(cfg, site, cache):
    """{leaf: [(ip, prefixlen, interface, vrf or "")]} for every IPv4 address on the tunnel leaves
    (mig_tep_leaves_<site>, else the bridge and route leaves), read with `ip -j addr show` (any account)."""
    if "leafaddrs" in cache:
        return cache["leafaddrs"]
    leaves = _mig_items(_mig_key(cfg, "mig_tep_leaves", site)) or sorted(
        set(_mig_items(_mig_key(cfg, "mig_bridge_leaves", site))) | set(_mig_items(_mig_key(cfg, "mig_route_leaves", site))))
    out = {}
    if leaves:
        user, pw = _mig_leaf_creds(cfg)
        for h in leaves:
            ok, o = ssh_exec(h, user, pw, "PATH=$PATH:/usr/sbin:/sbin ip -j addr show", timeout=25)
            try:
                d = json.loads(o) if ok else None
            except ValueError:
                d = None
            if not isinstance(d, list):
                continue
            out[h] = [(str(ai.get("local")), ai.get("prefixlen"), str(itf.get("ifname") or ""), str(itf.get("master") or ""))
                      for itf in d for ai in itf.get("addr_info") or [] if ai.get("family") == "inet" and ai.get("local")]
    cache["leafaddrs"] = out
    return out


def mig_leaf_gateway(cfg, site, cidr, cache):
    """(gateway, interface, vrf, why not) of a tunnel subnet from the leaves: the address every leaf read owns in
    it, the VRR one (vlanN-v0) first. None and the reason when the switches have none, or no single shared one."""
    addrs = mig_leaf_addrs(cfg, site, cache)
    if not addrs:
        return None, None, None, "no leaf readable (mig_tep_leaves_%s, or the bridge and route leaves)" % site
    try:
        net = ipaddress.ip_network(cidr, strict=False)
    except ValueError:
        return None, None, None, "%s is not a subnet" % cidr
    per = {}
    for h, lst in addrs.items():
        per[h.split(".")[0]] = [(ip, itf, vrf) for ip, _p, itf, vrf in lst
                                if _mig_ip_in(ip, net)]
    have = [v for v in per.values() if v]
    if not have:
        return None, None, None, ("no leaf (%s) owns an address in %s: the switches have no gateway for it. Give its VLAN "
                                  "a gateway (VRR) in the VRF of the other tunnel subnet" % (", ".join(sorted(per)), cidr))
    common = set.intersection(*[{ip for ip, _i, _v in v} for v in have])
    vrr = sorted({ip for v in have for ip, itf, _v in v if ip in common and itf.endswith("-v0")})
    pick = vrr or sorted(common)
    if len(pick) != 1:
        return None, None, None, "the leaves own %s in %s and no single shared address: set the gateway by hand" % (
            "; ".join("%s %s" % (k, ",".join(sorted(ip for ip, _i, _v in v))) for k, v in sorted(per.items()) if v), cidr)
    itf, vrf = next((i, v_) for v in have for ip, i, v_ in v if ip == pick[0])
    return pick[0], itf, vrf, None


def _mig_ip_in(ip, net):
    try:
        return ipaddress.ip_address(ip) in net
    except ValueError:
        return False


def mig_leaf_reach(cfg, site, vrf, dst, cache):
    """{leaf: True|False|None}: whether each tunnel leaf routes to `dst` from the VRF the gateway lives in."""
    key = "reach:%s:%s" % (vrf, dst)
    if key in cache:
        return cache[key]
    out = {}
    user, pw = _mig_leaf_creds(cfg)
    for h in mig_leaf_addrs(cfg, site, cache):
        ok, o = ssh_exec(h, user, pw, "PATH=$PATH:/usr/sbin:/sbin ip -j route get %s%s" % (dst, (" vrf %s" % vrf) if vrf else ""),
                         timeout=20)
        try:
            d = json.loads(o) if ok and str(o).strip().startswith("[") else None
        except ValueError:
            d = None
        out[h.split(".")[0]] = (bool(d) and str(d[0].get("type") or "unicast") not in ("unreachable", "blackhole", "prohibit")
                                ) if d is not None else (False if ok or "unreachable" in str(o).lower() else None)
    cache[key] = out
    return out


def _mig_policy_pool(lmhost, H, ref, cache):
    """(pool id, name, [subnet objects]) of a tunnel pool on a Local Manager, from a transport node's pool
    reference (a policy path, a policy id, or the manager id the policy pool realizes)."""
    key = "pool:%s" % ref
    if key in cache:
        return cache[key]
    ref, hit = str(ref or ""), None
    if ref.startswith("/infra/ip-pools/"):
        hit = ref.rsplit("/", 1)[-1]
    else:
        st_, b = http("https://%s/policy/api/v1/infra/ip-pools" % lmhost, headers=H, timeout=30)
        for p_ in _res(b) if st_ == 200 else []:
            if ref in (p_.get("id"), p_.get("path"), p_.get("realization_id"), p_.get("unique_id"), p_.get("nsx_id")):
                hit = p_.get("id")
                break
    out = None
    if hit:
        st_, b = http("https://%s/policy/api/v1/infra/ip-pools/%s" % (lmhost, hit), headers=H, timeout=30)
        st2, sb = http("https://%s/policy/api/v1/infra/ip-pools/%s/ip-subnets" % (lmhost, hit), headers=H, timeout=30)
        if st2 == 200:
            out = (hit, (b or {}).get("display_name") if st_ == 200 else hit,
                   [x for x in _res(sb) if x.get("cidr")])
    cache[key] = out
    return out


def mig_tep_plan(cfg, site, lmhost, H, lm, res, cache=None):
    """Each tunnel pool of the Green edges (bridge and Tier-0) and of the hosts VMs land on, against what the
    other side's tunnels sit in. A pool whose subnet must reach another tunnel subnet and has no gateway gets the
    one the leaves own there (UPDATE, applied with --commit and read back); none on the switches, or several, is
    BLOCKED with the reason. A pool that has its gateway while a node's endpoint does not is BLOCKED until that node
    is re-applied. Returns (rows, checks)."""
    cache = {} if cache is None else cache
    rows, checks = [], []
    tns = _res(_nb(lm, "transport_nodes"))
    edges = _mig_items(_mig_key(cfg, "mig_bridge_edges", site)) + list(res.get("t0_edges") or [])
    _cl, hosts, why = mig_green_hosts(cfg, site)
    if not lmhost or not tns or not edges or why:
        return rows, checks
    by = {}
    for t in tns:
        info = t.get("node_deployment_info") or {}
        for n in [t.get("display_name"), info.get("fqdn")]:
            if _mig_short(n):
                by.setdefault(_mig_short(n), t)
    members = [("edge", by[_mig_short(e)]) for e in edges if _mig_short(e) in by] + \
              [("host", by[_mig_short(h)]) for h in hosts if _mig_short(h) in by]
    eps = {t.get("id"): _mig_tn_endpoints(lmhost, H, t.get("id"), cache) for _k, t in members}
    nets = {"edge": set(), "host": set()}
    for kind, t in members:
        for _ip, cidr, _gw, _d in eps.get(t.get("id")) or []:
            if cidr:
                nets[kind].add(cidr)
    pools = {}
    for kind, t in members:
        for hs in (t.get("host_switch_spec") or {}).get("host_switches") or []:
            spec = hs.get("ip_assignment_spec") or {}
            ref = spec.get("ip_pool_id") or spec.get("ip_pool")
            if ref:
                pools.setdefault(str(ref), {"kinds": set(), "nodes": []})
                pools[str(ref)]["kinds"].add(kind)
                pools[str(ref)]["nodes"].append(t)
    for ref, info in sorted(pools.items()):
        pp = _mig_policy_pool(lmhost, H, ref, cache)
        if not pp:
            checks.append({"area": "tunnels", "item": "tunnel pool %s" % ref.rsplit("/", 1)[-1], "state": "WARN",
                           "detail": "not readable on %s: its gateway is not checked" % lmhost})
            continue
        pid, pname, subs = pp
        for sub in subs:
            cidr = str(sub.get("cidr"))
            others = set()
            for kind in info["kinds"]:
                others |= {n for n in nets["host" if kind == "edge" else "edge"] if n != cidr}
            if cidr not in nets["edge"] | nets["host"] or not others:
                continue                # its tunnels never leave their subnet: no gateway needed
            path = "/infra/ip-pools/%s/ip-subnets/%s" % (pid, sub.get("id"))
            label = "%s %s" % (pname, cidr)
            gw = sub.get("gateway_ip")
            if not gw:
                lgw, itf, vrf, why_ = mig_leaf_gateway(cfg, site, cidr, cache)
                if not lgw:
                    rows.append({"side": "Green", "kind": "tep-gateway", "id": label, "path": path, "host": lmhost,
                                 "action": "BLOCKED", "detail": "no gateway; its tunnels cannot reach %s. %s" % (
                                     ", ".join(sorted(others)), why_)})
                    continue
                body = {k: v for k, v in sub.items() if not str(k).startswith("_") or k == "_revision"}
                body["gateway_ip"] = lgw
                rows.append({"side": "Green", "kind": "tep-gateway", "id": label, "path": path, "host": lmhost,
                             "action": "UPDATE", "rev": sub.get("_revision"), "body": body,
                             "change": [{"field": "gateway_ip", "to": lgw}],
                             "detail": "gateway not set -> %s (%s on the leaves): its tunnels reach %s" % (
                                 lgw, itf, ", ".join(sorted(others)))})
                for o_ in sorted(others):          # the gateway is useful only if the leaves route onward from it
                    tgt = str(next(ipaddress.ip_network(o_, strict=False).hosts(), "")) if o_ else ""
                    reach = mig_leaf_reach(cfg, site, vrf, tgt, cache) if tgt else {}
                    if reach and all(v is False for v in reach.values()):
                        checks.append({"area": "tunnels", "item": "leaves route %s to %s" % (cidr, o_), "state": "WARN",
                                       "detail": "no leaf routes %s from %s%s: the gateway alone will not bring the "
                                                 "tunnels up. Route %s into that VRF on the switches" % (
                                                     tgt, itf, (" (VRF %s)" % vrf) if vrf else "", o_)})
                continue
            stale = sorted({t.get("display_name") for t in info["nodes"] for ip, c_, g_, _d in eps.get(t.get("id")) or []
                            if c_ == cidr and not g_})
            if stale:
                rows.append({"side": "Green", "kind": "tep-gateway", "id": label, "path": path, "host": lmhost,
                             "action": "BLOCKED", "detail": "gateway %s, but not on %s yet: re-apply each by hand (an edge: "
                             "Edit > Edge Node Uplink Mapping > Apply > Save; a host: resync NSX), one at a time" % (
                                 gw, ", ".join(stale))})
            else:
                rows.append({"side": "Green", "kind": "tep-gateway", "id": label, "path": path, "host": lmhost,
                             "action": "UNCHANGED", "detail": "gateway %s, on every node" % gw})
    return rows, checks


def mig_tep_apply(lmhost, H, rows):
    """Each planned pool gateway: the subnet PUT whole with its _revision, then read back."""
    for r in rows:
        if r["kind"] != "tep-gateway" or r["action"] != "UPDATE":
            continue
        url = "https://%s/policy/api/v1%s" % (lmhost, r["path"])
        st_, b = http(url, method="PUT", headers=H, body=r["body"], timeout=60)
        st2, back = http(url, headers=H, timeout=30)
        r["http"] = st_
        if st_ in (200, 201) and st2 == 200 and (back or {}).get("gateway_ip") == r["body"]["gateway_ip"]:
            r["detail"] += ", read back"
            r["rev_after"] = (back or {}).get("_revision")
        else:
            r["action"] = "ERROR"
            r["detail"] = "PUT HTTP %s%s" % (st_, (": %s" % str((b or {}).get("error_message"))[:120]) if isinstance(b, dict) and b.get("error_message") else "")
    return rows


# ---------------------------------------------------------------- migpath: route on the leaves
def mig_route_parse(text, local_as):
    """FRR `show bgp ipv4 unicast <prefix> json` -> ('green'|'blue'|'absent', AS path) or (None, why)."""
    try:
        d = json.loads(text)
    except ValueError:
        return None, "not JSON"
    paths = (d or {}).get("paths") or []
    if not paths:
        return "absent", "not in the BGP table"
    for p in paths:
        best = p.get("bestpath")
        if (best.get("overall") if isinstance(best, dict) else bool(best)) or p.get("best") is True:
            asp = p.get("aspath")
            txt = asp.get("string") if isinstance(asp, dict) else asp if isinstance(asp, str) else p.get("path") or ""
            return ("green" if str(local_as) in str(txt).split() else "blue"), str(txt) or "local"
    return "absent", "no best path"


def mig_route_parse_ip(text, prefix, green_nets):
    """`ip -j route show table all <prefix>`, then `#NH#` and `ip -j nexthop show` -> ('green'|'blue'|'mixed'|
    'absent', next hops) or (None, why). Cumulus installs BGP routes as nexthop objects ("nhid 875" and no next
    hop on the route), so the route's nexthop object, or each member of its group, gives the addresses. Green when
    every IPv4 next hop lies in a subnet of Green's Tier-0 uplinks (read from NSX): no vtysh, no sudo."""
    rtxt, _sep, ntxt = str(text).partition("#NH#")
    try:
        d = json.loads(rtxt.strip() or "[]")
    except ValueError:
        return None, "not JSON"
    nh = {}
    try:
        for x in json.loads(ntxt.strip()) if ntxt.strip() else []:
            nh[x.get("id")] = x
    except ValueError:
        nh = {}
    nets = []
    for n in green_nets or []:
        try:
            nets.append(ipaddress.ip_network(str(n), strict=False))
        except ValueError:
            pass
    if not nets:
        return None, "Green's Tier-0 uplink subnets not known"
    gws, mine = [], []
    for e in d if isinstance(d, list) else []:
        if str(e.get("dst")) != prefix or e.get("type") in ("unreachable", "blackhole", "prohibit", "local"):
            continue
        mine.append(e)
        hops = e.get("nexthops") or ([e] if e.get("gateway") or e.get("via") else [])
        if not hops and e.get("nhid") is not None and nh.get(e["nhid"]) is not None:
            o = nh[e["nhid"]]
            hops = [nh.get(m.get("id")) for m in o.get("group") or []] if o.get("group") else [o]
        for hop in hops:
            gw = (hop or {}).get("gateway") or ((hop or {}).get("via") or {}).get("host")
            if gw:
                gws.append(str(gw))
    if not mine:
        return "absent", "no route to %s in any table (%s)" % (prefix, rtxt.strip()[:60] or "empty")
    v4 = []
    for x in gws:
        try:
            if ipaddress.ip_address(x).version == 4:
                v4.append(x)
        except ValueError:
            pass
    if not v4:                  # next hops not read, or IPv6 link-local ones (learned over the fabric): not judged
        o_ = nh.get(mine[0].get("nhid")) if mine[0].get("nhid") is not None else None
        return None, "route present, next hops not judged: %s%s" % (
            json.dumps(mine[0], sort_keys=True)[:120], (" nexthop %s" % json.dumps(o_, sort_keys=True)[:120]) if o_ else "")

    def green_hop(x):
        return any(ipaddress.ip_address(x) in n for n in nets)
    g = sorted({x for x in v4 if green_hop(x)})
    b = sorted({x for x in v4 if not green_hop(x)})
    if g and not b:
        return "green", "via %s, Green's Tier-0 uplinks" % ", ".join(g)
    if b and not g:
        return "blue", "via %s, not Green's Tier-0" % ", ".join(b)
    return "mixed", "via %s (Green) and %s (not Green)" % (", ".join(g), ", ".join(b))


def mig_t0_nets(green, t0, locales):
    """The addresses of Green's Tier-0 uplinks and HA VIPs at these locations, each as a /32: a leaf route whose
    next hops are all among them is Green's. By address, not subnet: Blue's edges can share an uplink subnet."""
    out = set()

    def take(subs):
        for sub in subs or []:
            for ip in sub.get("ip_addresses") or []:
                try:
                    out.add(str(ipaddress.ip_network(str(ip), strict=False)))
                except ValueError:
                    pass
    for l in locales or []:
        st_, b = gm_get(green["host"], green["_H"], "/tier-0s/%s/locale-services/%s/interfaces" % (t0.get("id"), l.get("id")))
        for itf in _res(b) if st_ == 200 else []:
            take(itf.get("subnets"))
        for hv in l.get("ha_vip_configs") or []:
            take(hv.get("vip_subnets"))
    return sorted(out)


def _mig_leaf_creds(cfg):
    user = cfg.get("leaf_user") or "cumulus"
    pw = os.environ.get("FLEETPARITY_LEAF_PASSWORD") or cfg.get("leaf_password") or ""
    if not pw and not DRY:
        pw = getpass.getpass("      leaf '%s' password (%s; Enter to skip): " % (user, _mig_shown("leaf_password")))
        cfg["leaf_password"] = pw
    return user, pw


def mig_route_wait(cfg, site, prefix, expect, green_nets=None):
    """Poll the leaves until the prefix's best path is Green's or, after a rollback, Blue's again. Read-only
    SSH. Per leaf, the first way that works: vtysh (BGP best path, judged by fed_ns_local_as in its AS path),
    sudo vtysh, then the kernel's routing table (`ip route`, any account), judged by the next hops against
    Green's Tier-0 uplink subnets. Returns one check."""
    item = "route %s on the leaves" % prefix
    leaves = _mig_items(_mig_key(cfg, "mig_route_leaves", site))
    if not leaves:
        return {"area": "route", "item": item, "state": "SKIP", "detail": "set mig_route_leaves_%s" % site}
    user, pw = _mig_leaf_creds(cfg)
    local_as = str(cfg.get("fed_ns_local_as") or "").strip()
    if not local_as:
        return {"area": "route", "item": item, "state": "FAIL",
                "detail": "set fed_ns_local_as (the AS of Green's Tier-0, as the leaves see it) to judge the route"}
    wait = int(cfg.get("mig_route_wait") or 90)
    step = min(5, max(1, wait // 3))
    cmd = "vtysh -c 'show bgp ipv4 unicast %s json'" % prefix
    ipcmd = ("PATH=$PATH:/usr/sbin:/sbin; ip -j route show table all %s; echo '#NH#'; ip -j nexthop show 2>/dev/null; true"
             % prefix)
    modes = ["plain"] + (["ip"] if green_nets else []) + ["sudo"]      # sudo last: a refused sudo is logged on the leaf
    how, last, t0 = {}, {}, time.time()
    shown = t0                          # each leaf's reading every 15 s while waiting: a quiet wait is not a stuck one
    want = ("via AS %s" % local_as if expect == "green" else "not via AS %s" % local_as)
    while True:
        for h in leaves:
            res_, why = (None, "no answer"), []
            for mode in ([how[h]] if h in how else modes):
                if mode == "ip":
                    ok, o = ssh_exec(h, user, pw, ipcmd, timeout=20)
                    if ok and o.strip().startswith("["):
                        how[h] = mode
                        res_ = mig_route_parse_ip(o.strip(), prefix, green_nets)
                        break
                else:
                    if mode == "plain":
                        ok, o = ssh_exec(h, user, pw, cmd, timeout=20)
                    else:
                        ok, o = ssh_exec(h, user, pw, "sudo -S -p '' " + cmd, stdin_data=pw + "\n", timeout=20)
                    if ok and "{" in o:              # sudo's first-use lecture can come ahead of the JSON
                        o = o[o.index("{"):]
                    if ok and o.strip().startswith("{"):
                        how[h] = mode
                        res_ = mig_route_parse(o, local_as)
                        break
                why.append("%s: %s" % (mode, str(o).strip().splitlines()[0][:80] if str(o).strip() else "no output"))
                res_ = (None, "; ".join(why))
            last[h] = res_
        readable = {h: v for h, v in last.items() if v[0] is not None}
        waited = int(time.time() - t0)
        if not readable:
            return {"area": "route", "item": item, "state": "WARN",
                    "detail": "leaves not readable (%s); check by hand: sudo vtysh -c 'show bgp ipv4 unicast %s'"
                              % (next(iter(last.values()))[1], prefix)}
        if all(v[0] == expect for v in readable.values()):
            skipped = sorted(set(leaves) - set(readable))
            return {"area": "route", "item": item, "state": "PASS",
                    "detail": "%s on %s after %ds: %s%s" % (
                        want if all(how.get(h) != "ip" for h in readable) else
                        "Green's" if expect == "green" else "not Green's",
                        ", ".join(h.split(".")[0] for h in readable), waited,
                        "; ".join(sorted(set(v[1] for v in readable.values()))),
                        (" (%s not readable)" % ", ".join(skipped)) if skipped else "")}
        if time.time() - t0 >= wait:
            return {"area": "route", "item": item, "state": "FAIL",
                    "detail": "not %s after %ds: %s" % (want, waited, "; ".join(
                        "%s %s %s" % (h.split(".")[0], v[0], v[1]) for h, v in sorted(readable.items())))}
        if time.time() - shown >= 15:
            shown = time.time()
            log("   %ds of %ds: %s" % (waited, wait, ", ".join("%s %s" % (h.split(".")[0], {
                "green": "via Green", "blue": "not via Green", "absent": "no route", "mixed": "via Green and not"}.get(
                    v[0], "not read")) for h, v in sorted(last.items()))))
        time.sleep(step)


# ---------------------------------------------------------------- migpath: plan
def mig_plan(cfg, site, a, green, blue, lm, rows, st=None):
    """Pre-flight checks and the ordered list of objects for this run. No writes."""
    checks, objs, res = [], [], {"rows": [], "edges": {}, "site": site,
                                 "owned": {sid: v.get("prefix_lists") or [] for sid, v in
                                           ((st or {}).get("segments") or {}).items()}}

    def c(item, state, detail=""):
        checks.append({"area": "migpath", "item": item, "state": state, "detail": str(detail)[:400]})

    for side, d in (("Green", green), ("Blue", blue)):
        if not d.get("version"):
            c("%s Global Manager %s" % (side, d.get("host")), "FAIL", "HTTP %s" % d.get("status"))
    if not green.get("version") or not blue.get("version"):
        return checks, objs, res
    c("Green Global Manager", "PASS" if str(green["version"]).startswith("9.1.1") else "WARN",
      "%s  NSX %s" % (green["host"], green["version"]))
    c("Blue Global Manager", "INFO", "%s  NSX %s  location %s" % (blue["host"], blue["version"], blue["site"]))

    # router MAC: two NSX systems on one broadcast domain must not share it. It is set per
    # Local Manager; every Green Local Manager must carry the same value, and Blue's must differ.
    item = "router MAC differs Blue/Green"
    g_rm, b_rm = green.get("router_macs") or {}, blue.get("router_macs") or {}
    gset = {str(v["mac"]).lower() for v in g_rm.values() if v.get("mac")}
    bset = {str(v["mac"]).lower() for v in b_rm.values() if v.get("mac")}
    unread = ["%s (%s)" % (h, mig_lm_unread_why(h, v)) for h, v in sorted(list(g_rm.items()) + list(b_rm.items()))
              if not v.get("mac")]
    if len(gset) > 1:
        c("router MAC equal on every Green Local Manager", "FAIL",
          ", ".join("%s %s" % (h, v.get("mac")) for h, v in sorted(g_rm.items())))
    if gset & bset:
        c(item, "FAIL", "both %s. Change vdr_mac on every Green Local Manager before any bridge "
          "carries traffic." % ", ".join(sorted(gset & bset)))
    elif not g_rm or not b_rm:
        c(item, "WARN", "set %s to read it" % ("nsx_lm_host_%s" % site if not g_rm else "mig_blue_lm_host_%s" % site))
    elif unread:
        c(item, "WARN", "not readable on %s; confirm by hand" % ", ".join(unread))
    else:
        c(item, "PASS", "Green %s, Blue %s" % (", ".join(sorted(gset)), ", ".join(sorted(bset))))

    # Green gateway chain: Tier-1 advertises, Tier-0 redistributes, filter known
    t1name = _mig_key(cfg, "mig_tier1", site) or cfg.get("fed_ns_tier1_name")
    t1 = (_mig_named(green["tier1s"], t1name) or [None])[0]
    res["t1"] = t1
    if not t1:
        c("Tier-1 %s" % t1name, "FAIL", "not on the Green Global Manager. Have: %s"
          % ", ".join(sorted(str(t.get("display_name")) for t in green["tier1s"])))
    else:
        adv = t1.get("route_advertisement_types") or []
        c("Tier-1 %s advertises connected" % t1.get("display_name"),
          "PASS" if "TIER1_CONNECTED" in adv else "FAIL", ", ".join(adv) or "nothing advertised")
        t0 = next((x for x in green["tier0s"] if x.get("path") == t1.get("tier0_path")), None)
        res["t0"] = t0
        if not t0:
            c("Tier-0 behind %s" % t1.get("display_name"), "FAIL", "tier0_path %s not found" % t1.get("tier0_path"))
        else:
            hs_, lsb = gm_get(green["host"], green["_H"], "/tier-0s/%s/locale-services" % t0.get("id"))
            ls = next((l for l in _res(lsb) if site.lower() in (str(l.get("id")).lower(),
                       str(l.get("display_name")).lower()) or ("/sites/%s/" % site) in str(l.get("edge_cluster_path"))), None)
            types = []
            for rule in ((ls or {}).get("route_redistribution_config") or {}).get("redistribution_rules") or []:
                types += rule.get("route_redistribution_types") or []
            c("%s redistributes Tier-1 connected at %s" % (t0.get("display_name"), site),
              "PASS" if "TIER1_CONNECTED" in types else "FAIL",
              "present" if "TIER1_CONNECTED" in types else "absent or null: sessions stay up and advertise nothing")
            want_as = str(cfg.get("fed_ns_local_as") or "").strip()
            if ls and want_as:
                hs_, bgp = gm_get(green["host"], green["_H"], "/tier-0s/%s/locale-services/%s/bgp" % (t0.get("id"), ls.get("id")))
                has_as = str((bgp or {}).get("local_as_num") or "").strip() if hs_ == 200 and isinstance(bgp, dict) else ""
                c("%s local AS at %s is fed_ns_local_as" % (t0.get("display_name"), site),
                  "WARN" if not has_as else "PASS" if has_as == want_as else "FAIL",
                  "not readable (HTTP %s): confirm %s by hand" % (hs_, want_as) if not has_as else
                  has_as if has_as == want_as else "NSX says %s, fed_ns_local_as says %s: the route check would judge by the "
                  "wrong AS. Set fed_ns_local_as: %s" % (has_as, want_as, has_as))
            pls = set()
            if ls:
                hs_, nb = gm_get(green["host"], green["_H"], "/tier-0s/%s/locale-services/%s/bgp/neighbors"
                                % (t0.get("id"), ls.get("id")))
                for n in _res(nb):
                    for rf in n.get("route_filtering") or []:
                        pls.update(rf.get("out_route_filters") or [])
            res["prefix_lists"] = sorted(pls)
            res["route_maps"] = mig_route_maps(green, pls)
            res["other_sites"] = mig_other_sites(green, t0, [l for l in _res(lsb) if l is not ls])
            # this location's uplinks only: another location's can reuse a range the other estate uses here
            res["green_nets"] = mig_t0_nets(green, t0, [ls] if ls else [])     # judges the leaves' routes without vtysh
            if ls:            # the Tier-0's edges here: the way out of every host once a segment is cut over
                ecp_ = _mig_rel(ls.get("edge_cluster_path"))
                ec_ = next((e for e in green.get("edge_clusters") or [] if _mig_rel(e.get("path")) == ecp_), None)
                res["t0_edges"] = sorted({str(n.get("display_name")) for n in (ec_ or {}).get("_nodes") or []
                                          if n.get("display_name")})
            c("%s uplinks at %s" % (t0.get("display_name"), site), "INFO" if res["green_nets"] else "WARN",
              ", ".join(n_.split("/")[0] for n_ in res["green_nets"]) + ": a leaf route via these is Green's"
              if res["green_nets"] else "not read: the route check after a cutover then needs vtysh on the leaves")
            unread_rm = [m_ for m_ in res["route_maps"].values() if m_.get("status") != 200]
            c("%s outbound filter" % t0.get("display_name"), "PASS" if pls and not unread_rm else "WARN",
              "; ".join(mig_filter_text(p, res["route_maps"]) for p in sorted(pls)) if pls else
              "none: every connected subnet is advertised. Decide before the first cutover.")

    # bridges, each side
    reserved = set(_mig_items(cfg.get("mig_reserved_vlan_tzs")) or ["nsx-vlan-transportzone", "nsx-vlan-t0-tz"])
    blue_writes = _mig_blue_writes(cfg, a)
    bw = str(cfg.get("mig_blue_writes") or "").strip().lower()
    c("Blue writes", "INFO", "enabled" if _mig_true(bw) else
      ("test segments only" + ("" if getattr(a, "test", False) else "; this run writes nothing on Blue"))
      if bw == "test" else "disabled: Blue steps are printed for doing by hand")
    for side, d, pre in (("Green", green, "mig_"), ("Blue", blue, "mig_blue_")):
        ecn = _mig_key(cfg, pre + "bridge_edge_cluster", site)
        names = _mig_items(_mig_key(cfg, pre + "bridge_edges", site))
        tzn = _mig_key(cfg, pre + "bridge_vlan_tz", site)
        bpn = _mig_key(cfg, pre + "bridge_profile", site) or "bp-migration-%s" % site
        info = {"nodes": [], "tz": None, "bp_path": None, "block": None, "names": names}
        ec = (_mig_named(d["edge_clusters"], ecn) or [None])[0] if ecn else None
        if not ec:
            info["block"] = "%s bridge edge cluster unresolved" % side
            c("%s bridge edge cluster" % side, "FAIL", "%r not found. Have: %s" % (ecn, ", ".join(
                sorted(str(x.get("display_name")) for x in d["edge_clusters"])) or "none"))
        elif len(names) != 2:
            info["block"] = "%s bridge edges not set" % side
            c("%s bridge edges" % side, "FAIL", "%sbridge_edges_%s must be [primary, backup]" % (pre, site))
        else:
            for n in names:
                hit = _mig_named(ec.get("_nodes"), n)
                if hit:
                    info["nodes"].append(hit[0])
                else:
                    c("%s bridge edge %s" % (side, n), "FAIL", "not in %s. Have: %s" % (ec.get("display_name"),
                      ", ".join(str(x.get("display_name")) for x in ec.get("_nodes") or [])))
            if len(info["nodes"]) == 2:
                c("%s bridge edges" % side, "PASS", "%s primary, %s backup, %s" % (names[0], names[1], ec.get("display_name")))
            else:
                info["block"] = "%s bridge edges unresolved" % side
        # production isolation: the bridge edges run no gateway, the bridge zone carries no segment
        snap = d.get("snapshot") or {}
        if ec:
            ecp = _mig_rel(ec.get("path"))
            gws = sorted({(snap.get(p.split("/locale-services/")[0]) or {}).get("display_name")
                          or p.split("/locale-services/")[0].rsplit("/", 1)[-1]
                          for p, o in snap.items() if "/locale-services/" in p and "/bgp/" not in p
                          and ecp and _mig_rel(o.get("edge_cluster_path")) == ecp})
            info["dedicated"] = not gws
            c("%s bridge edges dedicated" % side, "FAIL" if gws else "PASS",
              "%s runs %s. Bridge on new edges that run no gateway." % (ec.get("display_name"), ", ".join(gws))
              if gws else "no gateway on %s" % ec.get("display_name"))
            if gws:
                info["block"] = info["block"] or "%s bridge edges run a gateway" % side
        tz = (_mig_named(d["tzs"], tzn) or [None])[0] if tzn else None
        if tz and tz.get("tz_type") == "VLAN_BACKED":
            tzp = _mig_rel(tz.get("path"))
            on = sorted(str(s_.get("id")) for s_ in d["segments"] if tzp and _mig_rel(s_.get("transport_zone_path")) == tzp)
            c("%s bridge zone dedicated" % side, "FAIL" if on else "PASS",
              "%s carries %s. Bridge on a new zone with no segments." % (tzn, ", ".join(on[:6]))
              if on else "no segment on %s" % tzn)
            if on:
                info["block"] = info["block"] or "%s bridge zone carries segments" % side
        if not tzn or not tz:
            info["block"] = info["block"] or "%s bridge zone unresolved" % side
            c("%s bridge zone" % side, "FAIL", "%r not found at %s. Create it on the Local Manager and attach it "
              "to a free fastpath vNIC on both bridge edges." % (tzn, d["site"]))
        elif tz.get("tz_type") != "VLAN_BACKED" or tz.get("display_name") in reserved:
            info["block"] = info["block"] or "%s bridge zone unusable" % side
            c("%s bridge zone" % side, "FAIL", "%s is %s%s" % (tzn, tz.get("tz_type"),
              "; it carries Tier-0 uplinks" if tz.get("display_name") in reserved else ""))
        else:
            info["tz"] = tz
            if side == "Green" and lm is not None and len(info["nodes"]) == 2:
                miss = [n for n in names if _mig_node_tzs(lm, n) is not None
                        and not (_mig_tz_ids(tz) & set(_mig_node_tzs(lm, n)))]
                unread = [n for n in names if _mig_node_tzs(lm, n) is None]
                if miss:
                    info["block"] = "%s not attached to %s" % (tzn, ", ".join(miss))
                    c("Green bridge zone on edges", "FAIL", "%s not on %s" % (tzn, ", ".join(miss)))
                elif unread:
                    c("Green bridge zone on edges", "WARN", "switch spec not readable for %s" % ", ".join(unread))
                else:
                    c("Green bridge zone on edges", "PASS", "%s on both" % tzn)
            else:
                c("%s bridge zone" % side, "PASS", "%s  (edge attachment proven by --verify)" % tzn
                  if side == "Blue" else tzn)
        existing = _mig_named(d["bridge_profiles"], bpn)
        bpid = existing[0].get("id") if existing else ns_id(bpn)
        info["bp_path"] = "/sites/%s/enforcement-points/default/edge-bridge-profiles/%s" % (d["site"], bpid)
        info["bp_name"] = bpn
        res["edges"][side] = info
        if a.mode == "build" and not getattr(a, "remove", False):
            body = {"display_name": bpn, "edge_paths": [n.get("path") for n in info["nodes"]],
                    "ha_mode": "ACTIVE_STANDBY",
                    "failover_mode": str(cfg.get("mig_bridge_failover") or "NON_PREEMPTIVE").upper()}
            need = None if len(info["nodes"]) == 2 else "%s bridge edges unresolved" % side
            if not info.get("dedicated", True):
                need = need or "%s bridge edges run a gateway" % side
            if side == "Blue" and not blue_writes:
                need = need or "Blue writes disabled: create %s on Blue by hand" % bpn
            objs.append({"side": side, "kind": "bridge-profile", "id": bpn, "host": d["host"],
                         "H": d["_H"], "path": info["bp_path"], "create": body,
                         "mutate": (lambda o, b=body: dict(o, edge_paths=b["edge_paths"],
                                                           ha_mode=b["ha_mode"], failover_mode=b["failover_mode"])),
                         "needs": need, "after": []})

    # rows
    infra = set(_mig_vlans(_mig_key(cfg, "mig_infra_vlans", site)))
    vseg = {}                      # single-VLAN segments on either manager: a transit VLAN must not be one
    for side_, d_ in (("Green", green), ("Blue", blue)):
        for s_ in d_["segments"]:
            for it in _mig_items(s_.get("vlan_ids")):
                if it.isdigit():
                    vseg.setdefault(int(it), "%s segment %s" % (side_, s_.get("id")))
    target = mig_target(a)
    test = bool(getattr(a, "test", False))
    test_ids = list(getattr(a, "test_ids", None) or [])
    if test:
        names = _mig_items(_mig_key(cfg, "mig_test_segments", site))
        if not names:
            c("test segments", "FAIL", "set mig_test_segments_%s to the Blue test segment" % site)
        elif not test_ids and getattr(a, "remove", False):
            c("test segments", "INFO", "none of %s is on Blue or Green: nothing to take apart" % ", ".join(names))
        elif not test_ids:
            c("test segments", "FAIL", "none of %s is on Blue: create it with --test --setup" % ", ".join(names))
        else:
            c("test segments", "INFO", "%s: Blue writes limited to %s and the Blue bridge profile"
              % (", ".join(test_ids), "it" if len(test_ids) == 1 else "them"))
    if a.mode == "build":
        if test:            # --test --remove builds nothing: it takes the test segments apart (mig_drop_plan)
            sel = [] if getattr(a, "remove", False) else [r for r in rows if r["segment"] in test_ids]
        else:
            sc_items = _mig_items(_mig_key(cfg, "mig_scope", site))
            sel = [r for r in rows if r["path"] == "BRIDGE" and r.get("scope")]
            if not sc_items:
                c("mig_scope_%s" % site, "WARN", "not set: a build bridges nothing. List the CIDRs (or segment "
                  "names) to migrate")
            else:
                c("scope", "INFO", "mig_scope_%s %s: %d segment%s to bridge" % (
                    site, ", ".join(sc_items), len(sel), "" if len(sel) == 1 else "s"))
            rv = [r for r in rows if r.get("scope") and r["path"] == "REVIEW"]
            if rv:
                c("segments of the scope not bridged", "WARN", "%d REVIEW, not built: %s" % (len(rv), "; ".join(
                    "%s (%s)" % (r["subnet"] or r["segment"], r["notes"] or "see its notes") for r in rv[:5])
                    + (" (+%d more)" % (len(rv) - 5) if len(rv) > 5 else "")))
            sk = [r for r in rows if r.get("scope") and r["path"] == "SKIP"]
            if sk:
                c("skipped in the scope", "INFO", "%d in mig_skip_%s: %s" % (len(sk), site, ", ".join(
                    r["subnet"] or r["segment"] for r in sk[:8]) + (" (+%d more)" % (len(sk) - 8) if len(sk) > 8 else "")))
    else:
        sel = [r for r in rows if target in (r["segment"], r["subnet"], r.get("name"))]
        if not sel:
            c("segment %s" % target, "FAIL", "no Blue segment with that id, name or subnet at %s" % site)
        elif test and any(r["segment"] not in test_ids for r in sel):
            c("segment %s" % target, "FAIL", "not a test segment: --test acts only on %s"
              % (", ".join(test_ids) or "mig_test_segments"))
            sel = []
    seen = {}
    gseg = {s.get("id"): s for s in green["segments"]}
    bseg = {s.get("id"): s for s in blue["segments"]}
    g_gw = {}
    for s in green["segments"]:
        for sub in s.get("subnets") or []:
            if sub.get("gateway_address"):
                g_gw[str(sub["gateway_address"]).split("/")[0]] = s.get("id")
    for r in sel:
        who = "%s (%s)" % (r["segment"], r["subnet"] or "no subnet")
        bad = list(r["problems"])
        if r["path"] != "BRIDGE":
            bad.append("path %s: only BRIDGE rows are built" % r["path"])
        if any(x.get("id") == r["segment"] for x in green.get("segments_deleting") or []):
            bad.append("NSX is still deleting Green's segment: run again once it is gone")
        if not r["net"] or not r["gw"]:
            bad.append("subnet and gateway are required")
        elif r["gw"] not in r["net"]:
            bad.append("gateway %s outside %s" % (r["gw"], r["net"]))
        if r["vlan"] is None:
            if not r["problems"]:
                bad.append("no transit VLAN: %s is not in mig_scope_%s" % (r["subnet"] or r["segment"], site))
        elif not 1 <= r["vlan"] <= 4094:
            bad.append("transit VLAN %s is not 1-4094" % r["vlan"])
        elif r["vlan"] in infra:
            bad.append("transit VLAN %s is green infrastructure (mig_infra_vlans)" % r["vlan"])
        elif r["vlan"] in vseg:
            bad.append("transit VLAN %s is used by %s" % (r["vlan"], vseg[r["vlan"]]))
        elif r["vlan"] in seen:
            bad.append("transit VLAN %s also on %s" % (r["vlan"], seen[r["vlan"]]))
        if r["vlan"] is not None:
            seen.setdefault(r["vlan"], r["segment"])
        b = bseg.get(r["segment"])
        g = gseg.get(r["segment"])
        if r["source"] == "gm-overlay":
            if not b and a.mode == "build" and g and _mig_conn(g) == "ON" and not g.get("bridge_profiles"):
                c(who, "INFO", "cut over, unbridged, Blue's segment retired: nothing to build")
                continue
            if not b:
                if a.mode != "retire":        # retire reads 404 and says "already gone"
                    bad.append("Blue has no segment %r" % r["segment"])
            else:
                bgw = str(((b.get("subnets") or [{}])[0] or {}).get("gateway_address") or "").split("/")[0]
                if r["gw"] and bgw != str(r["gw"]):
                    bad.append("Blue's gateway is %s, the plan says %s: the plan is stale" % (bgw or "none", r["gw"]))
                if b.get("vlan_ids"):
                    bad.append("Blue's segment is VLAN-backed; set source gm-vlan")
        if g:
            ggw = str(((g.get("subnets") or [{}])[0] or {}).get("gateway_address") or "").split("/")[0]
            if r["gw"] and ggw and ggw != str(r["gw"]):
                bad.append("Green already has %s with gateway %s" % (r["segment"], ggw))
        other = g_gw.get(str(r["gw"]))
        if other and other != r["segment"]:
            bad.append("Green segment %s already owns gateway %s" % (other, r["gw"]))
        # once bridged, the VLAN is NSX's: a plan that disagrees would add a second bridge, a loop
        for side_, obj in (("Green", g), ("Blue", b)):
            bp_ = (res["edges"].get(side_) or {}).get("bp_path")
            for e in (obj or {}).get("bridge_profiles") or []:
                vs = sorted(int(v) for v in e.get("vlan_ids") or [] if str(v).isdigit())
                if bp_ and _mig_rel(e.get("bridge_profile_path")) == bp_ and r["vlan"] is not None and vs != [r["vlan"]]:
                    bad.append("%s bridges it on VLANs %s, not only %s: remove the extra VLAN from that bridge first"
                               % (side_, ",".join(str(v) for v in vs), r["vlan"]))
        for x in bad:
            c(who, "FAIL", x)
        if bad:
            continue
        res["rows"].append(r)
        mig_row_objects(cfg, site, a, r, green, blue, res, objs, g, b, blue_writes)
    if a.mode == "build" and (not test or getattr(a, "remove", False)):
        mig_drop_plan(cfg, site, rows, sel, gseg, bseg, green, blue, res, objs, c, st, blue_writes,
                      want=set(test_ids) if test else None)
    for item, detail in res.pop("infos", []):
        c(item, "INFO", detail)
    for item, detail in res.pop("warns", []):
        c(item, "WARN", detail)
    for item, detail in res.pop("fails", []):
        c(item, "FAIL", detail)
    return checks, objs, res


def mig_drop_plan(cfg, site, rows, sel, gseg, bseg, green, blue, res, objs, c, st=None, blue_writes=False, want=None):
    """The undo of a build, for each segment this site's runs built that the config no longer bridges: out
    of the scope, or in skip (skip wins). Blue's side first, the build in reverse: Blue's bridge comes off
    Blue's segment (a Blue write: blue_writes), then Green's segment (tag migpath/from-blue) is deleted.
    Only while nothing depends on them: Green is not the gateway (a cut-over segment is never a candidate:
    --rollback first) and no VM is on Green's segment (mig_drop_checks holds both steps). Held, all of them,
    while the scope is empty or an item of it matches no Blue segment: a typo there must not undo the build.
    A segment this site's runs did not build, another site's, or a test segment outside the scope is never
    touched. `want`: exactly these segments, whatever the scope says (--test --remove)."""
    picked = {r["segment"] for r in sel}
    bbp = (res["edges"].get("Blue") or {}).get("bp_path")
    t1p = (res.get("t1") or {}).get("path")
    mine = {sid for sid, v in ((st or {}).get("segments") or {}).items()      # built by this site's runs
            if any(h.get("action") == "build" for h in v.get("history") or [])}
    res["drop"] = []
    sub = {r.get("segment"): r.get("subnet") or r.get("segment") for r in rows}
    going = sorted((sub.get(x.get("id")) or x.get("display_name") or x.get("id") for x in green.get("segments_deleting") or []),
                   key=lambda x: (len(str(x)), str(x)))
    if going:
        c("Green segments NSX is deleting", "INFO", "%d marked for delete, still on NSX while its Local Managers remove "
          "them: %s%s" % (len(going), ", ".join(going[:12]), " (+%d more)" % (len(going) - 12) if len(going) > 12 else ""))
    for r in rows:
        sid = r.get("segment")
        if not sid or sid in picked or sid not in mine:
            continue                # bridged by this run's plan, or not this site's build: never touched from here
        if want is not None and sid not in want:
            continue
        if want is None and r.get("test") and not r.get("scope"):
            continue                # the test runs' own: fp --test --remove takes it apart
        g, b = gseg.get(sid), bseg.get(sid) or {}
        b_br = bool(bbp) and any(_mig_rel(e.get("bridge_profile_path")) == bbp for e in b.get("bridge_profiles") or [])
        if g:
            if _mig_conn(g) != "OFF" or not any(t.get("scope") == "migpath" and t.get("tag") == "from-blue"
                                                for t in g.get("tags") or []):
                continue            # Green is the gateway, or not made by this tool
            if not t1p or g.get("connectivity_path") != t1p:
                continue            # another site's
        elif not b_br:
            continue                # nothing of it left on either side
        res["drop"].append(r)
        label = r.get("subnet") or sid
        why = ("--test --remove" if want is not None else "listed in mig_skip_%s" % site if r.get("skip")
               else "not in mig_scope_%s" % site)
        off = "%s bridge" % sid
        if b_br:
            objs.append({"side": "Blue", "kind": "segment-bridge", "id": off, "segment": sid, "host": blue["host"],
                         "H": blue["_H"], "path": "/segments/%s" % sid, "create": None,
                         "mutate": (lambda o, bp=bbp: _mig_without_profile(o, bp)),
                         "needs": None if blue_writes else "Blue writes disabled: take Blue's bridge off %s by hand" % label,
                         "after": [], "gate": None, "drop": True, "note": "%s %s: Blue's bridge off first" % (label, why)})
        if g:
            objs.append({"side": "Green", "kind": "segment", "id": sid, "segment": sid, "host": green["host"],
                         "H": green["_H"], "path": "/segments/%s" % sid, "create": None, "mutate": None, "needs": None,
                         "after": [("Blue", off)] if b_br else [], "gate": None, "delete": True, "drop": True,
                         "note": "%s %s: built by this tool" % (label, why)})
    if not res["drop"]:
        return
    hold = None
    if want is None:
        items = [x for x in _mig_items(_mig_key(cfg, "mig_scope", site)) if str(x).lower() != "all"]
        dead = [x for x in items if not any(_mig_match([x], r.get("segment"), r.get("name"), r.get("subnet"),
                                                       r.get("blue_tier1")) for r in rows)]
        hold = ("mig_scope_%s is empty" % site if not _mig_items(_mig_key(cfg, "mig_scope", site)) else
                "mig_scope_%s: %s matches no Blue segment" % (site, ", ".join(dead)) if dead else None)
    if hold:
        for o in objs:
            if o.get("drop") and not o.get("needs"):
                o["needs"] = "%s: nothing is undone until the scope is right" % hold
    nets = sorted((r.get("subnet") or r["segment"] for r in res["drop"]), key=lambda x: (len(x), x))
    nb = sum(1 for o in objs if o.get("drop") and o["side"] == "Blue")
    ng = sum(1 for o in objs if o.get("drop") and o["side"] == "Green")
    c("undo (--test --remove)" if want is not None else "undo (out of the scope, or in skip)", "WARN" if hold or nb else "INFO",
      "%d segment(s) built by this tool that the config no longer bridges: %s%s. %s" % (
          len(nets), ", ".join(nets[:12]), " (+%d more)" % (len(nets) - 12) if len(nets) > 12 else "",
          ("Held: %s" % hold) if hold else
          "%s takes Blue's bridge off %d of them, then deletes Green's segment of %d, where no VM is on it" % (
              "--commit" if want is not None else "--commit --expect <its digest>", nb, ng)
          if nb else "%s deletes Green's segment of each, where no VM is on it" % (
              "--commit" if want is not None else "--commit --expect <its digest>")))


def _mig_entry(info, vlan):
    return {"bridge_profile_path": "/global-infra" + info["bp_path"], "vlan_ids": [str(vlan)],
            "vlan_transport_zone_path": (info["tz"] or {}).get("path")}


def _mig_conn(o):
    return str((o.get("advanced_config") or {}).get("connectivity") or "ON").upper()


def _mig_with_conn(o, state):
    o = json.loads(json.dumps(o))
    o.setdefault("advanced_config", {})["connectivity"] = state
    return o


def _mig_with_entry(o, entry, present=True):
    o = json.loads(json.dumps(o))
    key = _mig_entry_key(entry)
    cur = o.get("bridge_profiles") or []
    has = any(_mig_entry_key(e) == key for e in cur)
    if present and not has:
        o["bridge_profiles"] = cur + [entry]
    elif not present and has:
        o["bridge_profiles"] = [e for e in cur if _mig_entry_key(e) != key]
    return o


def _mig_without_profile(o, bp):
    """The segment with no entry of this migration's bridge profile left, whatever VLAN it carries."""
    o = json.loads(json.dumps(o))
    cur = o.get("bridge_profiles") or []
    keep = [e for e in cur if _mig_rel(e.get("bridge_profile_path")) != bp]
    if len(keep) != len(cur):
        o["bridge_profiles"] = keep
    return o


def mig_row_objects(cfg, site, a, r, green, blue, res, objs, g, b, blue_writes):
    """Objects for one plan row, in the order they must be applied."""
    ge, be = res["edges"].get("Green") or {}, res["edges"].get("Blue") or {}
    sid, sub = r["segment"], "/segments/%s" % r["segment"]
    gw = "%s/%d" % (r["gw"], r["net"].prefixlen)
    g_entry, b_entry = _mig_entry(ge, r["vlan"]), _mig_entry(be, r["vlan"])
    t1 = res.get("t1")
    g_cut = bool(g) and _mig_conn(g) == "ON"
    blue_side = r["source"] == "gm-overlay"
    bneed = None if blue_writes else "Blue writes disabled: do this on Blue by hand"

    def add(side, kind, label, path, mutate, needs=None, create=None, after=None, gate=None, delete=False):
        after = [(s_, i_) for s_, i_ in (after or []) if i_]
        objs.append({"side": side, "kind": kind, "id": label, "segment": sid,
                     "host": (green if side == "Green" else blue)["host"],
                     "H": (green if side == "Green" else blue)["_H"], "path": path, "create": create,
                     "mutate": mutate, "needs": needs, "after": after or [], "gate": gate, "delete": delete})

    if a.mode == "retire":
        # Blue's segment is deleted once Green is the gateway, both bridges are gone and (mig_vm_checks)
        # no VM is left on it at either Blue location. Deleted is final: rollback ends here.
        if not blue_side:
            add("Blue", "retire", "%s delete" % sid, sub, None,
                "source %s: Blue's Global Manager holds no segment to retire" % r["source"])
            return
        why = None
        if not g or _mig_conn(g) != "ON":
            why = "Green is not the gateway yet: cut over first"
        elif g.get("bridge_profiles"):
            why = "Green's segment is still bridged: unbridge first"
        elif b and _mig_conn(b) != "OFF":
            why = "Blue's gateway is still on: cut over first"
        elif b and b.get("bridge_profiles"):
            why = "Blue's segment is still bridged: unbridge first"
        add("Blue", "retire", "%s delete" % sid, sub, None, why or bneed, delete=True)
        return

    if a.mode == "build":
        create = {"display_name": (b or {}).get("display_name") or sid,
                  "connectivity_path": (t1 or {}).get("path"),
                  "subnets": [{"gateway_address": gw}],
                  "advanced_config": {"connectivity": "OFF"},
                  "bridge_profiles": [g_entry],
                  "tags": [{"scope": "migpath", "tag": "from-blue"}]}

        def g_mut(o, create=create, cut=g_cut):
            if cut:
                return o          # Green is the gateway: the segment is the Green team's now, left alone
            o = json.loads(json.dumps(o))
            o["display_name"] = create["display_name"]
            o["connectivity_path"] = create["connectivity_path"]
            if not any(s.get("gateway_address") == gw for s in o.get("subnets") or []):
                o["subnets"] = [{"gateway_address": gw}] + list(o.get("subnets") or [])
            return _mig_with_entry(o, g_entry)
        need = ge.get("block") or (None if t1 else "Tier-1 unresolved")
        add("Green", "segment", sid, sub, g_mut, need, create, after=[("Green", ge.get("bp_name"))])
        if blue_side:
            add("Blue", "segment-bridge", sid, sub,
                (lambda o, cut=g_cut: o if cut else _mig_with_entry(o, b_entry)),
                be.get("block") or bneed, after=[("Blue", be.get("bp_name"))])
        if res.get("other_sites") and not g_cut:
            st_o, d_o = mig_other_sites_verdict(res["other_sites"], r["net"])
            res.setdefault("infos" if st_o == "PASS" else "warns", []).append(
                ("%s advertised only from %s" % (r["net"], site_of(res)), d_o if st_o != "FAIL" else "the cutover will refuse: " + d_o))
        if res.get("route_maps") and not g_cut:
            adds_, infos_, fails_ = mig_out_filter_plan(res, r, green)
            res.setdefault("infos", []).extend(infos_ + [("%s at cutover" % r["net"], "adds it to %s%s"
                                                          % (p_.rsplit("/", 1)[-1], n_)) for p_, n_ in adds_ if n_])
            res.setdefault("warns", []).extend((i_, "the cutover will refuse: " + d_) for i_, d_ in fails_)
        return

    if a.cutover:
        if not g:
            add("Green", "connectivity", "%s ON" % sid, sub, None, "Green segment missing: build it first")
            return
        adds_, infos_, fails_ = mig_out_filter_plan(res, r, green)
        res.setdefault("infos", []).extend(infos_)
        res.setdefault("fails", []).extend(fails_)
        if res.get("other_sites"):
            st_o, d_o = mig_other_sites_verdict(res["other_sites"], r["net"])
            res.setdefault({"PASS": "infos", "WARN": "warns", "FAIL": "fails"}[st_o], []).append(
                ("%s advertised only from %s" % (r["net"], site_of(res)), d_o))
        # a cutover leaves the segment bridged on both sides: on a built segment these read UNCHANGED; after
        # --unbridge they put both bridges back, Green staying the gateway (the undo of --unbridge)
        add("Green", "segment-bridge", "%s bridge" % sid, sub, lambda o: _mig_with_entry(o, g_entry), ge.get("block"))
        if blue_side:
            add("Blue", "segment-bridge", "%s bridge" % sid, sub, lambda o: _mig_with_entry(o, b_entry),
                be.get("block") or bneed)
        for p, note in adds_:
            def pl_mut(o, net=r["net"]):
                o = json.loads(json.dumps(o))
                new, _why = prefixes_with(o.get("prefixes"), net)
                if new is not None:
                    o["prefixes"] = new
                return o
            add("Green", "prefix-list", "%s += %s%s" % (p.rsplit("/", 1)[-1], r["net"], note), _mig_rel(p), pl_mut)
        on = lambda o: _mig_with_conn(o, "ON")
        if blue_side:
            add("Blue", "connectivity", "%s OFF" % sid, sub, lambda o: _mig_with_conn(o, "OFF"), bneed)
            add("Green", "connectivity", "%s ON" % sid, sub, on, gate="blue-off:%s" % sid)
        else:
            add("Green", "connectivity", "%s ON" % sid, sub, on,
                None if a.legacy_gw_off else "the legacy gateway for %s is outside NSX: switch it off, "
                "then re-run with --legacy-gw-off" % r["net"])
        return

    if a.unbridge:
        if not g or _mig_conn(g) != "ON":
            add("Green", "unbridge", "%s bridge" % sid, sub, None,
                "not cut over: removing the bridge now strands every VM still reaching Blue's gateway")
            return
        add("Green", "unbridge", "%s bridge" % sid, sub, lambda o: _mig_without_profile(o, ge.get("bp_path")))
        if blue_side:
            add("Blue", "unbridge", "%s bridge" % sid, sub, lambda o: _mig_without_profile(o, be.get("bp_path")), bneed)
        return

    if a.rollback:
        if not g:
            add("Green", "connectivity", "%s OFF" % sid, sub, None, "Green segment missing: nothing to roll back")
            return
        if blue_side and not b:
            add("Green", "connectivity", "%s OFF" % sid, sub, None,
                "Blue's segment is retired: there is no gateway to roll back to. Green stays ON")
            return
        # Green OFF then Blue ON, back to back. If the tool cannot turn Blue on, it must not
        # turn Green off either: that would leave the segment with no gateway at all.
        off = "%s OFF" % sid
        half = blue_side and not blue_writes and not (b and _mig_conn(b) == "ON")
        add("Green", "segment-bridge", "%s bridge" % sid, sub, lambda o: _mig_with_entry(o, g_entry))
        if blue_side:
            add("Blue", "segment-bridge", "%s bridge" % sid, sub, lambda o: _mig_with_entry(o, b_entry), bneed)
        add("Green", "connectivity", off, sub, lambda o: _mig_with_conn(o, "OFF"),
            "Blue writes disabled: turn Green OFF and Blue ON by hand, back to back" if half else None)
        if blue_side:
            add("Blue", "connectivity", "%s ON" % sid, sub, lambda o: _mig_with_conn(o, "ON"), bneed,
                after=[("Green", off)])
        owned = set((res.get("owned") or {}).get(sid) or [])
        for p in res.get("prefix_lists") or []:
            if _mig_rel(p) not in owned and p not in (res.get("route_maps") or {}):
                res.setdefault("infos", []).append((     # not placed by this tool: not the tool's to take away
                    "%s prefix on %s" % (sid, p.rsplit("/", 1)[-1]),
                    "%s was not added by this tool: left in place (Green OFF advertises nothing for it)" % r["net"]))
        for p in sorted(owned):                  # every list this tool put the subnet in

            def pl_rm(o, net=r["net"]):
                o = json.loads(json.dumps(o))
                new, _why = prefixes_without(o.get("prefixes"), net)
                if new is not None:
                    o["prefixes"] = new
                return o
            add("Green", "prefix-list", "%s -= %s" % (p.rsplit("/", 1)[-1], r["net"]), _mig_rel(p), pl_rm,
                after=[("Green", off)])     # withdraw only once Green no longer routes it


def mig_dhcp_checks(res, green, blue):
    """At cutover: if Blue serves DHCP to the segment (a segment DHCP config, or DHCP on its Tier-1),
    Green must too, or renewals fail from the flip on."""
    out = []
    bt1s = {t.get("path"): t for t in blue.get("tier1s") or []}
    gseg = {s.get("id"): s for s in green.get("segments") or []}
    bseg = {s.get("id"): s for s in blue.get("segments") or []}
    gt1 = res.get("t1") or {}
    for r in res.get("rows") or []:
        b, g = bseg.get(r["segment"]), gseg.get(r["segment"])
        if not b:
            continue
        bt1 = bt1s.get(b.get("connectivity_path")) or {}
        src = "segment DHCP" if _mig_has_dhcp(b) else \
            ("DHCP on %s" % bt1.get("display_name") if bt1.get("dhcp_config_paths") else None)
        if not src:
            continue
        dst = "segment DHCP" if _mig_has_dhcp(g) else \
            ("DHCP on %s" % gt1.get("display_name") if gt1.get("dhcp_config_paths") else None)
        out.append({"area": "migpath", "item": "%s DHCP on Green" % r["segment"], "state": "PASS" if dst else "FAIL",
                    "detail": ("Blue: %s; Green: %s" % (src, dst)) if dst else
                              "Blue serves it (%s); Green's segment and %s have none. Recreate it on Green before "
                              "cutover: renewals fail from the flip on" % (src, gt1.get("display_name") or "Tier-1")})
    return out


# ---------------------------------------------------------------- migpath: prefix lists
def prefix_covers(entry, net):
    if str(entry.get("action") or "").upper() != "PERMIT":
        return False
    n = str(entry.get("network") or "")
    if not n or n.upper() == "ANY":
        return False
    try:
        base = ipaddress.ip_network(n, strict=False)
    except ValueError:
        return False
    if net.version != base.version or net.network_address not in base or net.prefixlen < base.prefixlen:
        return False                   # subnet_of() is 3.7+; the tool runs on 3.6
    ge = int(entry["ge"]) if entry.get("ge") else base.prefixlen
    le = int(entry["le"]) if entry.get("le") else (base.prefixlen if not entry.get("ge") else net.max_prefixlen)
    return ge <= net.prefixlen <= le


def prefixes_with(prefixes, net):
    """PERMIT <net> ahead of the terminal deny. None when something already permits it."""
    prefixes = [dict(p) for p in prefixes or []]
    cut = next((i for i, p in enumerate(prefixes) if str(p.get("action") or "").upper() == "DENY"
                and str(p.get("network") or "").upper() in ("ANY", "0.0.0.0/0", "::/0")), len(prefixes))
    for p in prefixes[:cut]:
        if prefix_covers(p, net):
            return None, "already permitted by %s" % p.get("network")
    prefixes.insert(cut, {"network": str(net), "action": "PERMIT"})
    return prefixes, "inserted at %d of %d, ahead of the deny" % (cut + 1, len(prefixes))


def prefixes_without(prefixes, net):
    out = [dict(p) for p in prefixes or [] if not (str(p.get("network")) == str(net) and
           str(p.get("action") or "").upper() == "PERMIT" and not p.get("ge") and not p.get("le"))]
    return (out, "removed") if len(out) != len(prefixes or []) else (None, "not present")


def mig_pl_permits(prefixes, net):
    """A prefix list: the first line that matches decides; no line matching is a deny."""
    return _mig_pl_decides(prefixes, net)[0]


def mig_route_maps(green, paths):
    """The outbound filters that are route maps, read from Green's Global Manager with the prefix lists
    their entries match: {path: {"name", "status", "entries", "plists"}}. A prefix list is not in it."""
    out = {}
    for p in sorted(paths or []):
        if "/route-maps/" not in str(p):
            continue
        st, rm = gm_get(green["host"], green["_H"], _mig_rel(p))
        d = {"name": str(p).rsplit("/", 1)[-1], "status": st, "entries": [], "plists": {}}
        if st == 200 and isinstance(rm, dict):
            for e in rm.get("entries") or []:
                d["entries"].append({"action": str(e.get("action") or "").upper(),
                                     "prefix_lists": [str(x) for x in e.get("prefix_list_matches") or []],
                                     "communities": bool(e.get("community_list_matches")),
                                     "set": dict(e.get("set") or {})})
            for e in d["entries"]:
                for plp in e["prefix_lists"]:
                    if plp not in d["plists"]:
                        st2, pl = gm_get(green["host"], green["_H"], _mig_rel(plp))
                        d["plists"][plp] = (list(pl.get("prefixes") or [])
                                            if st2 == 200 and isinstance(pl, dict) else None)
        out[p] = d
    return out


def _mig_rm_set(s):
    s = s or {}
    parts = ["%s %s" % (k, s[k]) for k in ("as_path_prepend", "community", "med") if s.get(k) not in (None, "", [])]
    parts += ["%s %s" % (k, s[k]) for k, d in (("local_preference", 100), ("weight", 0)) if s.get(k) not in (None, d)]
    return ", ".join(parts)


def mig_filter_text(p, rms):
    name = str(p).rsplit("/", 1)[-1]
    rm = (rms or {}).get(p)
    if rm is None:
        return name
    if rm.get("status") != 200:
        return "%s: route map not readable (HTTP %s)" % (name, rm.get("status"))
    return "%s, route map: %s" % (name, "; ".join(
        "%d %s %s%s" % (i, e["action"], ", ".join(x.rsplit("/", 1)[-1] for x in e["prefix_lists"])
                        or ("communities" if e["communities"] else "-"),
                        (" set " + _mig_rm_set(e["set"])) if _mig_rm_set(e["set"]) else "")
        for i, e in enumerate(rm["entries"], 1)) or "no entries")


def mig_rm_verdict(rm, net):
    """How a route map treats the route to `net`, entries in order, first match wins:
    ("permit"|"deny", entry number, prefix list) for the entry that matches it; ("none", None, None)
    when none does (a route map ends in an implicit deny); ("unknown", entry number, why) when an
    entry before a match cannot be judged from here."""
    for i, e in enumerate(rm.get("entries") or [], 1):
        if e.get("communities"):
            return "unknown", i, "entry %d matches communities, which this tool does not judge" % i
        for plp in e.get("prefix_lists") or []:
            pl = (rm.get("plists") or {}).get(plp)
            if pl is None:
                return "unknown", i, "entry %d: prefix list %s not readable" % (i, plp.rsplit("/", 1)[-1])
            if mig_pl_permits(pl, net):
                return ("permit" if e.get("action") == "PERMIT" else "deny"), i, plp
    return "none", None, None


def mig_rm_target(rm, siblings):
    """The prefix list a new subnet joins: the one through which most of the Tier-1's other subnets
    already go out; with none, the first PERMIT entry's own list. (entry, path, why) or (None, None, why)."""
    votes = {}
    for n in siblings or []:
        v, i, plp = mig_rm_verdict(rm, n)
        if v == "permit":
            votes[(i, plp)] = votes.get((i, plp), 0) + 1
    if votes:
        (i, plp), k = sorted(votes.items(), key=lambda kv: (-kv[1], kv[0][0], kv[0][1]))[0]
        return i, plp, "where %d of the Tier-1's other subnets %s out" % (k, "goes" if k == 1 else "go")
    seen = set()
    for i, e in enumerate(rm.get("entries") or [], 1):
        if e.get("action") == "PERMIT" and not e.get("communities"):
            for plp in e.get("prefix_lists") or []:
                if plp not in seen:
                    return i, plp, "its first PERMIT entry"
        seen.update(e.get("prefix_lists") or [])
    return None, None, "it has no PERMIT entry with a prefix list of its own"


def site_of(res):
    return str(res.get("site") or "this site")


def mig_other_sites(green, t0, locales):
    """The Tier-0's other locations: whether each redistributes Tier-1 connected routes, and its
    neighbors' outbound filters, read with their prefix lists. [{"id", "t1_connected", "filters",
    "unfiltered", "plists": {path: prefixes|None}, "rmaps"}]."""
    out = []
    for l in locales:
        types = []
        for rule in ((l.get("route_redistribution_config") or {}).get("redistribution_rules") or []):
            types += rule.get("route_redistribution_types") or []
        d = {"id": l.get("id"), "t1_connected": "TIER1_CONNECTED" in types, "filters": set(), "unfiltered": 0,
             "plists": {}, "rmaps": {}}
        st, nb = gm_get(green["host"], green["_H"], "/tier-0s/%s/locale-services/%s/bgp/neighbors" % (t0.get("id"), l.get("id")))
        for n in _res(nb):
            fs = set()
            for rf in n.get("route_filtering") or []:
                fs.update(rf.get("out_route_filters") or [])
            if fs:
                d["filters"] |= fs
            else:
                d["unfiltered"] += 1
        d["rmaps"] = mig_route_maps(green, d["filters"])
        for p in sorted(d["filters"]):
            if p not in d["rmaps"]:
                st2, pl = gm_get(green["host"], green["_H"], _mig_rel(p))
                d["plists"][p] = list(pl.get("prefixes") or []) if st2 == 200 and isinstance(pl, dict) else None
        d["filters"] = sorted(d["filters"])
        out.append(d)
    return out


def mig_other_sites_verdict(others, net):
    """(state, detail) for one subnet: whether another location of the Tier-0 would advertise it too."""
    bad, unknown = [], []
    for d in others or []:
        if not d["t1_connected"]:
            continue
        if d["unfiltered"]:
            bad.append("%s: %d neighbor(s) with no outbound filter advertise every connected route" % (d["id"], d["unfiltered"]))
        for p in d["filters"]:
            name = p.rsplit("/", 1)[-1]
            rm = d["rmaps"].get(p)
            if rm is not None:
                if rm.get("status") != 200:
                    unknown.append("%s: route map %s not readable" % (d["id"], name))
                    continue
                v, i, x = mig_rm_verdict(rm, net)
                if v == "permit":
                    bad.append("%s: %s entry %d permits it" % (d["id"], name, i))
                elif v == "unknown":
                    unknown.append("%s: %s %s" % (d["id"], name, x))
            else:
                pl = d["plists"].get(p)
                if pl is None:
                    unknown.append("%s: prefix list %s not readable" % (d["id"], name))
                elif mig_pl_permits(pl, net):
                    bad.append("%s: %s permits it" % (d["id"], name))
    if bad:
        return "FAIL", "; ".join(bad) + ". Traffic entering there would cross to this site's gateway asymmetrically (uRPF " \
                                        "strict drops it). Deny it there first"
    if unknown:
        return "WARN", "; ".join(unknown) + ": check by hand"
    return "PASS", ", ".join(d["id"] for d in others or [] if d["t1_connected"]) or "no other location redistributes Tier-1 connected"


def mig_out_filter_plan(res, r, green):
    """Where the cutover permits r's subnet on the Tier-0's outbound filters. A prefix list gets it ahead
    of its terminal deny. A route map is judged entry by entry: already permitted, nothing is added;
    matched by no entry, it goes into the prefix list that carries the Tier-1's other subnets out (else
    the first PERMIT entry's), checked to permit it once added; denied by an entry, or not judged,
    the cutover refuses. Returns ([(prefix-list path, note)], infos, fails), each [(item, detail)]."""
    adds, infos, fails = [], [], []
    net = r["net"]
    t1p = (res.get("t1") or {}).get("path")
    sib = []
    for s_ in green.get("segments") or []:
        if not t1p or s_.get("id") == r["segment"] or s_.get("connectivity_path") != t1p:
            continue
        for sub in s_.get("subnets") or []:
            try:
                sib.append(ipaddress.ip_network(str(sub.get("gateway_address")), strict=False))
            except ValueError:
                pass
    for p in res.get("prefix_lists") or []:
        rm = (res.get("route_maps") or {}).get(p)
        if rm is None:
            adds.append((p, ""))
            continue
        item = "%s out through %s" % (net, rm["name"])
        if rm.get("status") != 200:
            fails.append((item, "route map not readable (HTTP %s): whether %s is advertised is unknown"
                          % (rm.get("status"), net)))
            continue
        v, i, x = mig_rm_verdict(rm, net)
        if v == "permit":
            infos.append((item, "entry %d permits it (%s): nothing to add" % (i, x.rsplit("/", 1)[-1])))
            continue
        if v != "none":
            fails.append((item, ("entry %d denies it (%s): it would not be advertised. Change the route map by hand, "
                                 "then run again" % (i, x.rsplit("/", 1)[-1])) if v == "deny" else
                          "%s: check by hand that it is advertised, then run again" % x))
            continue
        i, plp, why = mig_rm_target(rm, sib)
        if not plp:
            fails.append((item, "no entry permits it and %s: add it by hand, then run again" % why))
            continue
        new, _w = prefixes_with(rm["plists"].get(plp), net)
        sim = dict(rm, plists=dict(rm["plists"]))
        if new is not None:
            sim["plists"][plp] = new
        if mig_rm_verdict(sim, net)[0] != "permit":
            fails.append((item, "adding it to %s would not permit it (an earlier line of that list matches it "
                          "first): add it by hand, then run again" % plp.rsplit("/", 1)[-1]))
            continue
        adds.append((plp, " (%s entry %d, %s)" % (rm["name"], i, why)))
    return adds, infos, fails


# ---------------------------------------------------------------- migpath: diff and apply
def _mig_h(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, default=str).encode()).hexdigest()[:16]


def mig_items(results, tags=()):
    """The changes a plan would make, one [change, object, revision] each: what changes (hashed), the
    object ("side:path"), and the _revision the object had before this run wrote it. The same change
    to an object that changed since is a different change."""
    out = [[_mig_h([r["side"], r["kind"], r["path"], r["action"], r.get("change") or r.get("body")]),
            "%s:%s" % (r["side"], r["path"]), r.get("rev")]
           for r in results or [] if r["action"] in ("ADD", "UPDATE", "DELETE")]
    out += [[_mig_h(["tags", t["vm"], t.get("external_id"), t.get("add")]) if t.get("side", "Green") == "Green" else
             _mig_h(["tags", t["side"], t["vm"], t.get("external_id"), t.get("add")]),
             "tags:%s" % t["vm"] if t.get("side", "Green") == "Green" else "tags-%s:%s" % (t["side"].lower(), t["vm"]), None]
            for t in tags or [] if t["action"] == "ADD"]
    return sorted(out, key=lambda i: json.dumps(i, default=str))


def mig_wrote(results):
    """{"side:path": _revision after this run's last write to it}: a later run under the same reviewed
    plan knows those revisions are the plan's own doing."""
    return {"%s:%s" % (r["side"], r["path"]): r.get("rev_after") for r in results or []
            if r["action"] in ("ADD", "UPDATE") and r.get("http") in (200, 201, 202, 204)}


def mig_digest(results, tags=(), items=None):
    """Names exactly the changes a plan would make (objects, and tags to add); None when there are none.
    A plan run prints it; --commit --expect <digest> writes only what that plan holds (mig_review)."""
    items = mig_items(results, tags) if items is None else items
    return _mig_h(items) if items else None


def mig_journal_read(st_path):
    out = []
    try:
        with open(mig_journal_file(st_path)) as fh:
            for ln in fh:
                try:
                    out.append(json.loads(ln))
                except ValueError:
                    pass                    # a line cut short
    except OSError:
        pass
    return out


def mig_review(st_path, expect, digest, items):
    """--commit --expect <digest>: may this run write? Yes when its plan is the reviewed one, or the rest
    of it: every change this run would make is one the reviewed plan holds, on an object at the revision
    the plan read, or as a run under that plan left it (a run that stopped part way, run again). Any
    other change, or an object changed since, and nothing is written. The reviewed plan's changes and
    what its runs wrote come from the journal. Returns (ok, note)."""
    if expect == (digest or "none"):
        return True, None
    runs = [e for e in mig_journal_read(st_path) if expect in (e.get("digest"), e.get("expect"))]
    ref = next((e for e in reversed(runs) if e.get("digest") == expect and e.get("items")), None)
    now = "the plan now is %s" % digest if digest else "the plan now has no changes"
    if ref is None:
        return False, ("this is not the plan that was reviewed: --expect %s%s, %s. Nothing was written: review it "
                       "and run again" % (expect, "" if expect == "none" else " is not in this site's journal", now))
    held = {}
    for i in ref["items"]:
        if isinstance(i, list) and len(i) == 3:
            held.setdefault(i[0], []).append(i[2])
    own = {}                            # objects as the plan's own runs left them
    for e in runs:
        if e.get("commit"):
            own.update(e.get("wrote") or {})
    new = [i for i in items if i[0] not in held or (i[2] not in held[i[0]] and own.get(i[1], "?") != i[2])]
    if new:
        return False, ("this is not the plan that was reviewed: --expect %s, %s, with %d change(s) that plan does "
                       "not hold, or on objects changed since it read them. Nothing was written: review it and run "
                       "again" % (expect, now, len(new)))
    if not items:
        done = next((e for e in reversed(runs) if e.get("commit") and e.get("changed") and e.get("rc") == 0), None)
        return True, ("The reviewed plan %s was applied, completed by the run at %s." % (expect, done["ts"]) if done
                      else "Nothing of the reviewed plan %s is pending." % expect)
    return True, ("The rest of the reviewed plan %s: %d of its %d change(s), nothing else (plan %s)."
                  % (expect, len(items), len(ref["items"]), digest))


def mig_edge_bps(res):
    e = (res or {}).get("edges") or {}
    return (e.get("Green") or {}).get("bp_path"), (e.get("Blue") or {}).get("bp_path")


def mig_gateway_checks(rows, gseg, bseg, after_write=False, st=None):
    """Connectivity OFF on Green and on Blue means no gateway at all: a flip left half done. Rows whose
    segments were not read (not in gseg) are skipped; bseg maps a segment Blue no longer has to None.
    A segment this tool never cut over or rolled back that Blue keeps OFF is Blue's own setting: said so."""
    out = []
    for r in rows or []:
        sid = r.get("segment")
        if not sid or (r.get("source") or "gm-overlay") != "gm-overlay" or sid not in gseg or sid not in bseg:
            continue
        g, b = gseg[sid], bseg[sid]
        flipped = any(h.get("action") in ("cutover", "rollback") for h in
                      (((st or {}).get("segments") or {}).get(sid) or {}).get("history") or [])
        if st is not None and not flipped and g and b and _mig_conn(g) == "OFF" and _mig_conn(b) == "OFF":
            out.append({"area": "migpath", "item": "%s has no gateway on Blue" % sid, "state": "INFO",
                        "detail": "%s: Connectivity is OFF on Blue (Blue's own setting; this tool never changed it) "
                                  "and on Green (not cut over)" % (r.get("subnet") or sid)})
            continue
        if g and _mig_conn(g) == "OFF" and (b is None or _mig_conn(b) == "OFF"):
            out.append({"area": "migpath", "item": "%s has no gateway" % sid, "state": "FAIL" if after_write else "WARN",
                        "detail": "Connectivity is OFF on Green and %s. Finish it: fp --cutover %s --commit, or put "
                                  "Blue back: fp --rollback %s --commit" % ("on Blue" if b else "Blue's segment is gone",
                                                                             sid, sid)})
    return out


def mig_delete_wait(cfg, ghost, GH, rows, res, green_lms):
    """After the commit's Green deletes: wait until each reads 404 on the Global Manager (mig_delete_wait
    seconds, default 300). One still there is named with the Green Local Managers that still hold it."""
    left, t0 = {x["segment"]: x for x in rows}, time.time()
    limit = int(cfg.get("mig_delete_wait") or 300)
    while left:
        for sid in list(left):
            if gm_get(ghost, GH, "/segments/%s" % sid)[0] == 404:
                left.pop(sid)
        if not left or time.time() - t0 > limit:
            break
        time.sleep(5)
    item = "Green segments deleted"
    if not left:
        return {"area": "migpath", "item": item, "state": "PASS",
                "detail": "%d gone from NSX (read 404) after %ds" % (len(rows), int(time.time() - t0))}
    sub = {r.get("segment"): r.get("subnet") for r in (res.get("drop") or [])}
    where = {}
    for lm, user, pw in green_lms or []:
        if not pw:                      # never a sign-in with a password that is not that manager's own
            continue
        for sid in left:
            st_, _b = http("https://%s/policy/api/v1/global-infra/segments/%s" % (lm, sid), headers=_mig_H(user, pw), timeout=30)
            if st_ == 200:
                where.setdefault(sid, []).append(lm.split(".")[0])
    names = ["%s%s" % (sub.get(sid) or sid, " (on %s)" % ", ".join(where[sid]) if where.get(sid) else "") for sid in sorted(left)]
    return {"area": "migpath", "item": item, "state": "WARN",
            "detail": "%d of %d still marked for delete after %ds: %s. NSX finishes them on its own; the next fp lists "
                      "what is left as being deleted" % (len(left), len(rows), int(time.time() - t0),
                                                         ", ".join(names[:10]) + (" (+%d more)" % (len(names) - 10) if len(names) > 10 else ""))}


def mig_tags_placed(st, tag_rows):
    """Record which Green VM received each VM's Blue tags. From then on the tool leaves them alone."""
    for t in tag_rows or []:
        rec = ((st["segments"].get(t.get("segment")) or {}).get("vms") or {}).get(t["vm"])
        if rec is not None and t["action"] in ("ADD", "UNCHANGED") and t.get("external_id") \
                and rec.get("tags_placed_ext") != t["external_id"]:
            rec["tags_placed_ext"], rec["tags_on_green"] = t["external_id"], now()


def mig_apply(objs, commit, stop_on_error, blue_scope=None):
    """Objects in order. Each is read live first; creates are PATCHed whole, changes are PUT whole with
    their _revision, deletes are read back until gone. Every row records what it changes, which is
    what manual_steps.txt prints."""
    done = {}      # id -> final action, for dependencies
    gates = {}     # "blue-off:<seg>" -> satisfied?
    base = {}      # "side:path" -> its _revision as first read, before this run wrote it
    results = []
    halted = None
    for o in objs:
        row = {"side": o["side"], "kind": o["kind"], "id": o["id"], "path": o["path"], "segment": o.get("segment"),
               "host": o["host"], "action": None, "detail": o.get("note") or ""}
        if o.get("gate"):
            row["wait"] = "only once Blue's %s reads Connectivity OFF" % o.get("segment")
        elif o.get("after"):
            row["wait"] = "only after: %s" % ", ".join("%s %s" % d for d in o["after"])
        results.append(row)
        if halted:
            row["action"], row["detail"] = "BLOCKED", "not attempted: %s failed" % halted
            continue
        if blue_scope is not None and o["side"] == "Blue" and o["path"] not in blue_scope:
            row["action"], row["detail"] = "BLOCKED", "outside this run's scope: Blue writes are limited to %s" \
                % (", ".join(p.rsplit("/", 1)[-1] for p in sorted(blue_scope)) or "nothing")
            done[(o["side"], o["id"])] = "BLOCKED"
            continue
        dep = next((d for d in o.get("after") or [] if done.get(d) in ("BLOCKED", "ERROR")), None)
        need = o.get("needs") or (("depends on %s %s (%s)" % (dep[0], dep[1], done[dep])) if dep else None)
        if o.get("gate") and not gates.get(o["gate"]):
            need = need or "Blue's gateway is still on: its Connectivity must be OFF first"
        st, live = gm_get(o["host"], o["H"], o["path"])
        exists = st == 200 and isinstance(live, dict)
        pkey = "%s:%s" % (o["side"], o["path"])
        base.setdefault(pkey, live.get("_revision") if exists else None)
        if o.get("delete"):
            if st == 404:
                row["action"], row["detail"] = "UNCHANGED", "already gone"
            elif not exists:
                row["action"], row["detail"] = "ERROR", "read HTTP %s: not deleted" % st
                if stop_on_error:
                    halted = "%s %s" % (o["side"], o["id"])
            elif need:
                row["action"], row["detail"] = "BLOCKED", need
            else:
                row["action"], row["rev"] = "DELETE", base[pkey]
                if commit:
                    st2, b2 = gm_delete(o["host"], o["H"], o["path"])
                    if st2 not in (200, 202, 204) and o.get("drop") and live.get("bridge_profiles"):
                        # NSX may refuse a bridged segment's delete: its bridge off (as --unbridge does), then again
                        bare = json.loads(json.dumps(live))
                        bare["bridge_profiles"] = []
                        if gm_put(o["host"], o["H"], o["path"], bare)[0] in (200, 201):
                            st2, b2 = gm_delete(o["host"], o["H"], o["path"])
                    row["http"] = st2
                    gone = None
                    for _ in range(10 if st2 in (200, 202, 204) else 0):
                        st3, b3 = gm_get(o["host"], o["H"], o["path"])
                        if st3 == 404:
                            gone = "deleted, reads 404"
                        elif st3 == 200 and isinstance(b3, dict) and b3.get("marked_for_delete"):
                            gone = "marked for delete"
                        if gone:
                            break
                        time.sleep(3)
                    if gone:
                        row["detail"] = "%s%s" % (row["detail"] + ": " if row["detail"] else "", gone)
                    else:
                        row["action"], row["detail"] = "ERROR", "DELETE HTTP %s %s; still readable" % (
                            st2, str((b2 or {}).get("error_message") or "")[:150])
                        if stop_on_error:
                            halted = "%s %s" % (o["side"], o["id"])
            done[(o["side"], o["id"])] = row["action"]
            continue
        if o["kind"] == "connectivity" and o["side"] == "Blue" and exists and _mig_conn(live) == "OFF" \
                and o["id"].endswith("OFF"):
            gates["blue-off:%s" % o["segment"]] = True       # done by hand, or earlier
        if need and not (exists and o["mutate"] and _mig_view(o["mutate"](live)) == _mig_view(live)):
            row["action"], row["detail"] = "BLOCKED", need
            done[(o["side"], o["id"])] = "BLOCKED"
            continue
        if not exists:
            if st != 404:           # created only when NSX says it is not there: a failed read is not absence
                row["action"], row["detail"] = "ERROR", "read HTTP %s: nothing written for it" % st
                if stop_on_error:
                    halted = "%s %s" % (o["side"], o["id"])
            elif o.get("create") is None:
                row["action"], row["detail"] = "BLOCKED", "%s does not exist" % o["path"]
            else:
                row["action"], row["body"] = "ADD", o["create"]
        else:
            new = o["mutate"](live) if o["mutate"] else live
            row["action"] = "UNCHANGED" if _mig_view(new) == _mig_view(live) else "UPDATE"
            if row["action"] == "UPDATE":
                row["rev"] = base[pkey]
                row["change"] = [{"field": k, "to": new.get(k)} for k in MIG_MANAGED
                                 if json.dumps(new.get(k), sort_keys=True, default=str)
                                 != json.dumps(live.get(k), sort_keys=True, default=str)]
        if commit and row["action"] in ("ADD", "UPDATE"):
            if row["action"] == "ADD":
                st2, b2 = gm_patch(o["host"], o["H"], o["path"], o["create"])
            else:
                body = o["mutate"](live)
                body["_revision"] = live.get("_revision")
                st2, b2 = gm_put(o["host"], o["H"], o["path"], body)
            row["http"] = st2
            if st2 not in (200, 201, 202, 204):
                row["action"], row["detail"] = "ERROR", str((b2 or {}).get("error_message") or b2)[:200]
                if stop_on_error:
                    halted = "%s %s" % (o["side"], o["id"])
            else:
                row["rev_after"] = b2.get("_revision") if isinstance(b2, dict) else None
        if o["kind"] == "connectivity" and o["side"] == "Blue" and o["id"].endswith("OFF") \
                and row["action"] in ("UNCHANGED", "ADD", "UPDATE"):     # ERROR after a failed write never counts
            gates["blue-off:%s" % o["segment"]] = True
        done[(o["side"], o["id"])] = row["action"]
    return results


# ---------------------------------------------------------------- migpath: datapath and fabric
def parse_get_bridge(text):
    """Blocks from `get bridge`. 'State' appears twice: forwarding, then HA."""
    ports = []
    for block in re.split(r"(?=Bridge Port UUID\s*:)", text or ""):
        if "Bridge Port UUID" not in block:
            continue
        kv = re.findall(r"^\s*([A-Za-z][A-Za-z /]+?)\s*:\s*(.*?)\s*$", block, re.M)
        states = [v for k, v in kv if k == "State"]
        d = dict(kv)
        ports.append({"segment": d.get("Attached Logical Switch Name"), "vlan": d.get("VLAN ID"),
                      "forwarding": states[0] if states else None, "ha": states[1] if len(states) > 1 else None,
                      "device": d.get("Device"), "device_state": d.get("Device State")})
    return ports


def mig_edge_pw_key(cfg, site, side):
    """The setting a side's bridge edge admin password comes from at this site, to name in a message:
    sites.<site>.<side>.bridge.admin_password when the site has its own, else the one kept for every site."""
    key = "nsx_edge_password" if side == "Green" else "mig_blue_edge_password"
    return "%s_%s" % (key, site) if "%s_%s" % (key, site) in cfg else key


def _mig_bridge_why(checks, side, state, cfg, site):
    """One side's bridge reading this run, in a few words; names the setting to fix when its edges refused
    the password."""
    if state == "PASS":
        return "%s PASS" % side
    ed = [c_ for c_ in checks if c_["item"].startswith(side + " ") and c_["item"].endswith(" get bridge")]
    if any(is_auth_failure(c_["detail"]) for c_ in ed):
        return "%s %s: %s refused the password in %s" % (side, state, ", ".join(c_["item"].split(" ")[1] for c_ in ed),
                                                        mig_edge_pw_key(cfg, site, side))
    if ed:
        return "%s %s: %s" % (side, state, ed[0]["detail"][:80])
    if any(c_["item"] == "%s edges" % side for c_ in checks):
        return "%s %s: no password given (%s)" % (side, state, mig_edge_pw_key(cfg, site, side))
    return "%s %s" % (side, state)


def mig_verify(cfg, site, res, lm, outdir):
    """`get bridge` on both bridge pairs. Per transit VLAN: one Active and forwarding,
    one Standby, on each side. Not collected is reported as SKIP, never as FAIL."""
    checks, raw = [], {}

    def c(item, state, detail=""):
        checks.append({"area": "bridge", "item": item, "state": state, "detail": str(detail)[:300]})

    euser = cfg.get("nsx_edge_ssh_user") or "admin"
    domain = cfg.get("mig_edge_domain") or cfg.get("fed_gm_domain") or ""
    fq = {}
    if lm is not None:
        for n in fed_edge_nodes(lm):
            fq[str(n.get("name")).lower()] = n.get("fqdn")
    for side, key in (("Green", "nsx_edge_password"), ("Blue", "mig_blue_edge_password")):
        info = res["edges"].get(side) or {}
        names = info.get("names") or []
        if not names:
            continue
        var = mig_edge_pw_key(cfg, site, side)
        base = os.environ.get("FLEETPARITY_%s" % key.upper()) or cfg.get(key) or ""
        if not base and not DRY:
            base = getpass.getpass("      %s bridge edges %s '%s' password (%s; Enter to skip): " % (
                side, ", ".join(names), euser, _mig_shown(var)))
        if not base:
            c("%s edges" % side, "SKIP", "no password: %s" % var)
            continue
        seen = {}
        for n in names:
            target = fq.get(n.lower()) or (("%s.%s" % (n, domain)) if domain and "." not in n else n)
            ok, out = ssh_exec(target, euser, base, "get bridge", timeout=30)
            raw["%s:%s" % (side, n)] = out[-20000:]
            if not ok:
                auth = is_auth_failure(out)
                c("%s %s get bridge" % (side, n), "FAIL" if auth else "SKIP",
                  "%s; the password in %s was refused" % (str(out)[:90].rstrip(". "), var) if auth else str(out)[:120])
                continue
            seen[n] = parse_get_bridge(out)
        for r in res["rows"]:
            if not seen:
                c("%s bridge VLAN %s" % (side, r["vlan"]), "SKIP", "no edge answered")
                continue
            ports = [dict(p, edge=e) for e, ps in seen.items() for p in ps if str(p.get("vlan")) == str(r["vlan"])]
            act = [p for p in ports if str(p.get("ha")).lower() == "active"
                   and str(p.get("forwarding")).lower() == "forwarding" and str(p.get("device_state")).lower() == "up"]
            stb = [p for p in ports if str(p.get("ha")).lower() == "standby"]
            if len(act) == 1 and len(stb) == 1:
                c("%s bridge VLAN %s" % (side, r["vlan"]), "PASS", "%s active on %s (%s), standby on %s"
                  % (r["segment"], act[0]["edge"], act[0]["device"], stb[0]["edge"]))
            else:
                c("%s bridge VLAN %s" % (side, r["vlan"]), "FAIL", "%s: active %d, standby %d. The manager may say "
                  "realized; the edge is the truth." % (r["segment"], len(act), len(stb)))
    if outdir:
        write_json(outdir, "bridge_verify", raw)
    return checks


def _mig_bridge_vlans(obj):
    """{port: set(vlans)} from `bridge -j vlan show`, either JSON shape iproute2 has used."""
    out = {}
    items = obj.items() if isinstance(obj, dict) else [(x.get("ifname"), x.get("vlans")) for x in obj or []]
    for port, vl in items:
        s = out.setdefault(str(port), set())
        for v in vl or []:
            lo = int(v.get("vlan", 0))
            hi = int(v.get("vlanEnd", lo))
            s.update(range(lo, hi + 1))
    return out


def _mig_vid_set(tokens):
    out = set()
    for t in tokens or []:
        for part in str(t).replace(",", " ").split():
            m = re.fullmatch(r"(\d+)-(\d+)", part)
            if m:
                lo, hi = sorted((int(m.group(1)), int(m.group(2))))
                out.update(range(lo, hi + 1))
            elif part.isdigit():
                out.add(int(part))
    return out


def mig_ifaces_parse(text):
    """/etc/network/interfaces as NVUE renders it (ifupdown2): {interface: {attribute: [values]}}."""
    out, cur = {}, None
    for raw in (text or "").splitlines():
        ln = raw.split("#", 1)[0].rstrip()
        if not ln.strip():
            continue
        if not raw[:1].isspace():
            m = re.match(r"iface\s+(\S+)", ln)
            cur = out.setdefault(m.group(1), {}) if m else None
            continue
        if cur is not None:
            parts = ln.split()
            cur.setdefault(parts[0], []).extend(parts[1:])
    return out


def mig_leaf_model(ifaces, kernel):
    """Per bridge port: 'inherit' (carries the bridge VLANs), 'own' (its own VLAN list), 'access',
    or 'unknown' when the configuration was not read. NVIDIA: a bridge port inherits the bridge
    VIDs by default; a port-level VLAN list overrides them."""
    aware = sorted(n for n, d in (ifaces or {}).items() if [x.lower() for x in d.get("bridge-vlan-aware") or []] == ["yes"])
    br = "br_default" if "br_default" in aware or not aware else aware[0]
    b = (ifaces or {}).get(br) or {}
    ports = {}
    for p, vl in (kernel or {}).items():
        if p == br:
            continue
        d = (ifaces or {}).get(p) or {}
        if ifaces is None:
            mode, own = "unknown", None
        elif d.get("bridge-access"):
            mode, own = "access", _mig_vid_set(d["bridge-access"])
        elif d.get("bridge-vids"):
            mode, own = "own", _mig_vid_set(d["bridge-vids"])
        else:
            mode, own = "inherit", None
        ports[p] = {"mode": mode, "own": own, "vlans": set(vl)}
    return {"bridge": br, "bridge_vids": _mig_vid_set(b.get("bridge-vids")), "ports": ports}


MIG_NV_DIFF = "nv config diff      # only the transit VLANs added, nothing removed. Anything else: nv config detach, and stop"


def mig_leaf_commands(model, ports, want):
    """Exact NVUE lines for one leaf. Each line names the full VLAN list it leaves behind, the list read
    now plus the transit VLANs, so it is right whether NVUE merges VLANs into a list or replaces the
    list; `nv config diff` then shows only additions before anything is applied. The bridge line puts
    the transit VLANs on every port that inherits the bridge VLANs. A port line is written only for a
    port with its own VLAN list: on a port that inherits, a port line would prune it to its list."""
    want, br = set(want), model["bridge"]
    lines, notes = [], []
    if want - model["bridge_vids"]:
        if model["bridge_vids"]:
            lines.append("nv set bridge domain %s vlan %s" % (br, _mig_rtext(_mig_ranges(model["bridge_vids"] | want))))
        else:
            notes.append("%s: its VLAN list was not read, so no bridge line is written. Add %s to the list "
                         "`nv config show -o commands | grep 'bridge domain %s vlan'` prints, then nv config diff"
                         % (br, ",".join(str(v) for v in sorted(want)), br))
    for p in ports:
        info = model["ports"].get(p)
        if not info:
            notes.append("%s: not a port of %s; add it to the bridge first. No line written for it." % (p, br))
        elif info["mode"] == "access":
            notes.append("%s: access port for VLAN %s; a port facing a bridge-edge host must be a trunk. No line written."
                         % (p, ",".join(str(v) for v in sorted(info["own"]))))
        elif info["mode"] == "own":
            if want - info["own"]:
                lines.append("nv set interface %s bridge domain %s vlan %s"
                             % (p, br, _mig_rtext(_mig_ranges(info["own"] | want))))
            else:
                notes.append("%s: its own VLAN list already has them" % p)
        elif info["mode"] == "inherit":
            notes.append("%s: inherits the bridge VLANs; the bridge line covers it, no port line" % p)
        else:
            notes.append("%s: configuration not read; no line written" % p)
    if lines:
        # Cumulus Linux 5.8 and earlier do not save on apply: without save, a reboot drops the VLANs
        lines += [MIG_NV_DIFF, "nv config apply", "nv config save"]
    return lines, notes


def mig_leaf_ports(cfg, site):
    """{leaf short name: [ports]} from mig_bridge_ports_<site>: [leaf1:swp10, leaf2:swp10, ...]."""
    out = {}
    for it in _mig_items(_mig_key(cfg, "mig_bridge_ports", site)):
        h, _sep, p = it.partition(":")
        h, p = h.strip().split(".")[0].lower(), p.strip()
        if h and p and p not in out.setdefault(h, []):
            out[h].append(p)
    return out


def mig_leaves(cfg, site, res, outdir, st=None, reset=False, soft=False):
    """Transit VLANs on the leaves, read-only (`bridge -j vlan show`, `ip -j addr show` and
    `cat /etc/network/interfaces`, which NVUE renders): on every port facing a bridge-edge host and
    on the peer link, never given an SVI, and no port has lost a VLAN it carried when first read.
    Returns (checks, {leaf: exact NVUE lines}). soft: a build that read the leaves only to write the
    lines reports a VLAN not yet on a port as WARN; the lines are applied after it."""
    checks, raw, cmds = [], {}, {}
    missing = "WARN" if soft else "FAIL"

    def c(item, state, detail=""):
        checks.append({"area": "fabric", "item": item, "state": state, "detail": str(detail)[:400]})

    hosts = _mig_items(_mig_key(cfg, "mig_bridge_leaves", site) or cfg.get("leaf_hosts_%s" % site))
    user, pw = _mig_leaf_creds(cfg)
    if not pw:
        return [{"area": "fabric", "item": "leaves", "state": "SKIP", "detail": "no password"}], {}
    pool = set(_mig_vlans(_mig_key(cfg, "mig_transit_vlans", site)))
    whole = str(cfg.get("mig_leaf_vlans") or "").strip().lower() == "pool"
    want = sorted(pool) if whole and pool else sorted({r["vlan"] for r in res["rows"]})
    pmap = mig_leaf_ports(cfg, site)
    if not pmap:
        c("ports facing the bridge-edge hosts", "WARN", "set mig_bridge_ports_%s ([leaf:port, ...]): the tool then "
          "reads each port and writes the exact lines" % site)
    for x in sorted(set(pmap) - {h.split(".")[0].lower() for h in hosts}):
        c("mig_bridge_ports_%s" % site, "WARN", "%s is not in mig_bridge_leaves_%s: its ports are not read" % (x, site))
    mem = st.setdefault("leaves", {}) if st is not None else {}
    for h in hosts:
        short = h.split(".")[0]
        ok, o = ssh_exec(h, user, pw, "PATH=$PATH:/usr/sbin:/sbin bridge -j vlan show", timeout=20)
        ok2, o2 = ssh_exec(h, user, pw, "ip -j addr show", timeout=20) if ok else (False, "")
        ok3, o3 = ssh_exec(h, user, pw, "cat /etc/network/interfaces", timeout=20) if ok else (False, "")
        raw[h] = {"bridge": o[-20000:], "addr": o2[-20000:], "interfaces": o3[-60000:]}
        if not ok:
            c("%s reachable" % h, "FAIL" if is_auth_failure(o) else "SKIP", str(o)[:120])
            continue
        try:
            kernel = _mig_bridge_vlans(json.loads(o))
            ifs = json.loads(o2 or "[]")
            svis = {str(i.get("ifname")) for i in ifs}
            # an address makes an SVI a gateway; IPv6 link-local alone does not
            addrs = {str(i.get("ifname")): ["%s/%s" % (a.get("local"), a.get("prefixlen")) for a in i.get("addr_info") or []
                                            if a.get("family") == "inet" or (a.get("family") == "inet6"
                                                                            and a.get("scope") == "global")]
                     for i in ifs}
        except Exception as e:
            c("%s output parses" % h, "SKIP", str(e)[:100])
            continue
        model = mig_leaf_model(mig_ifaces_parse(o3) if ok3 else None, kernel)
        ports = list(pmap.get(short.lower()) or [])
        if ports:
            ports += [p for p in ("peerlink",) if p in kernel and p not in ports]
            for p in ports:
                have = kernel.get(p)
                item = "%s %s carries the transit VLANs" % (short, p)
                if have is None:
                    c(item, missing, "%s is not a port of the bridge" % p)
                    continue
                miss = [v for v in want if v not in have]
                c(item, missing if miss else "PASS", ("missing %s: apply the lines in switch_requirements.txt"
                                                      % _mig_rtext(_mig_ranges(miss))) if miss
                  else _mig_rtext(_mig_ranges(want)))
            if ok3:
                lines, notes = mig_leaf_commands(model, ports, want)
                cmds[short] = {"host": h, "bridge": model["bridge"], "lines": lines, "notes": notes, "ports": ports}
            else:
                c("%s port configuration" % short, "WARN", "/etc/network/interfaces not readable (%s): no lines "
                  "written for this leaf" % str(o3)[:80])
        else:
            for v in want:
                on = sorted(p for p, vs in kernel.items() if v in vs and p.startswith("swp"))
                c("%s VLAN %s on host ports" % (short, v), "PASS" if on else "FAIL",
                  ", ".join(on[:12]) + (" ..." if len(on) > 12 else "") if on else "not on any swp port")
        for v in want:
            names = sorted({"vlan%s" % v, "vlan%s-v0" % v} & svis)
            held = ["%s %s" % (n_, a_) for n_ in names for a_ in addrs.get(n_) or []]
            if held:
                c("%s VLAN %s is layer 2 only" % (short, v), "FAIL", "%s: a transit VLAN carries no gateway. "
                  "Remove it: nv unset interface %s" % (", ".join(held), names[0]))
            elif names:
                c("%s VLAN %s is layer 2 only" % (short, v), "WARN", "%s exists with no address, so it routes nothing. "
                  "Remove it when convenient: nv unset interface %s" % (", ".join(names), names[0]))
        rec, lost_any, since = mem.setdefault(short, {}), False, None
        for p in ports:
            if p not in kernel:
                continue
            was = rec.get(p)
            if was is None or reset:
                rec[p] = {"vlans": sorted(kernel[p]), "since": now()}
                continue
            since = since or was["since"]
            lost = sorted(set(was["vlans"]) - kernel[p] - pool)
            if lost:
                lost_any = True
                own_ = (model["ports"].get(p) or {}).get("own")
                fix_ = ("nv set interface %s bridge domain %s vlan %s" % (p, model["bridge"], _mig_rtext(_mig_ranges(set(own_) | set(lost))))
                        if (model["ports"].get(p) or {}).get("mode") == "own" and own_ else
                        "nv set bridge domain %s vlan %s" % (model["bridge"], _mig_rtext(_mig_ranges(set(model["bridge_vids"]) | set(lost)))))
                c("%s %s kept its VLANs" % (short, p), "FAIL", "lost %s since %s. Restore: %s; then nv config diff "
                  "(only additions), nv config apply" % (",".join(str(v) for v in lost), was["since"], fix_))
            else:
                rec[p]["vlans"] = sorted(set(was["vlans"]) | kernel[p])
        if since and not lost_any:
            c("%s ports kept their VLANs" % short, "PASS", "every VLAN they carried since %s" % since)
    if outdir:
        write_json(outdir, "leaves_migpath", raw)
    return checks, cmds


# ---------------------------------------------------------------- migpath: documents
def mig_switch_spec(cfg, site, res, cmds=None):
    hosts = _mig_items(_mig_key(cfg, "mig_bridge_leaves", site) or cfg.get("leaf_hosts_%s" % site))
    L = ["TRANSIT VLANS   %s   %s" % (site, now()), "=" * 74, "",
         "Layer 2 only. No SVI. On the ports facing the hosts that run",
         "the Green bridge edges (%s) and the Blue bridge edges (%s)." % (
             ", ".join((res["edges"].get("Green") or {}).get("names") or []) or "?",
             ", ".join((res["edges"].get("Blue") or {}).get("names") or []) or "?"),
         "Leaves: %s" % (", ".join(h.split(".")[0] for h in hosts) or "set mig_bridge_leaves_%s" % site), "",
         "  VLAN  segment                         subnet              name", "  " + "-" * 74]
    for r in sorted(res["rows"], key=lambda x: x["vlan"] or 0):
        L.append("  %4s  %-30s  %-18s  %s" % (r["vlan"], r["segment"][:30], r["subnet"], (r.get("name") or "")[:30]))
    vl = ",".join(str(v) for v in sorted({r["vlan"] for r in res["rows"]})) or "<none planned>"
    if cmds:
        L += ["", "Per leaf (Cumulus Linux 5, NVUE), exactly as written. Read from each port this run:", ""]
        for short in sorted(cmds):
            d = cmds[short]
            L.append("%s   ssh %s@%s" % (short, cfg.get("leaf_user") or "cumulus", d["host"]))
            L += ["  %s" % x for x in d["lines"]] or ["  nothing to change: the listed ports carry %s" % vl]
            L += ["  # %s" % n for n in d["notes"]]
            L.append("")
        for h in hosts:
            if h.split(".")[0] not in cmds:
                L += ["%s   not read this run: no lines written. Re-run with --check-leaves." % h.split(".")[0], ""]
    else:
        L += ["", "On each leaf (Cumulus Linux 5, NVUE): the bridge's VLAN list as it is now, plus the transit VLANs",
              "  nv config show -o commands | grep 'bridge domain br_default vlan'",
              "  nv set bridge domain br_default vlan <the bridge's list from that line>,%s" % vl,
              "  " + MIG_NV_DIFF,
              "  nv config apply",
              "  nv config save",
              "The bridge line puts the VLANs on every port that inherits the bridge VLANs. A port with its own",
              "VLAN list needs a port line as well, its list plus the transit VLANs; a port line on a port that",
              "inherits prunes it to that list. Set mig_bridge_ports_%s: the tool then reads each port and" % site,
              "writes the exact lines for each leaf here."]
    if str(cfg.get("mig_leaf_vlans") or "").strip().lower() == "pool":
        L[3:3] = ["mig_leaf_vlans: pool. The lines carry the whole transit pool %s, so the leaves are"
                  % _mig_rtext(_mig_ranges(_mig_vlans(_mig_key(cfg, "mig_transit_vlans", site)))),
                  "changed once; no later run needs them."]
    L += ["", "Check: fleetparity.py migpath --config <cfg> --check-leaves", ""]
    return "\n".join(L)


def mig_steps(cfg, site, res, a):
    L = ["MIGRATION STRATEGY   %s   values from this run   %s" % (site, now()), "=" * 74, ""]
    cmd = "python3 fleetparity.py migpath --config %s" % (a.config or "<config>")
    if getattr(a, "test", False):
        for r in res["rows"]:
            s = r["segment"]
            L += ["TEST   %s   %s   gw %s   transit %s" % (s, r["subnet"], r["gateway"], r["vlan"]),
                  "  build      %s --test --commit" % cmd,
                  "  switch     the lines in switch_requirements.txt, then  %s --test --check-leaves" % cmd,
                  "  verify     %s --test --verify --check-leaves" % cmd,
                  "  move       %s --test --move --commit   (vMotion, then its NSX tags; --vm a,b or --vm wave.csv: "
                  "only those)" % cmd,
                  "  cutover    %s --test --cutover %s --commit" % (cmd, s),
                  "  rollback   %s --test --rollback %s --commit" % (cmd, s),
                  "  cutover    %s --test --cutover %s --commit" % (cmd, s),
                  "  unbridge   %s --test --unbridge %s --commit   (undo: --test --cutover %s --commit)" % (cmd, s, s),
                  "  retire     %s --test --retire %s --commit   (no undo)" % (cmd, s),
                  "  no impact  %s --test --impact" % cmd,
                  "  undo       VMs back: %s --test --return --vm a,b (or --vm wave.csv) --commit" % cmd,
                  "  undo       the test build: %s --test --remove --commit" % cmd,
                  "  undo       the Blue test segment: %s --test --setup --remove --commit" % cmd, ""]
        return "\n".join(L)
    sc = _mig_items(_mig_key(cfg, "mig_scope", site))
    rows = sorted(res["rows"], key=lambda x: x["vlan"] or 0)
    L.append("SCOPE   mig_scope_%s: %s   %d segment%s" % (site, ", ".join(sc) or "not set", len(rows),
                                                          "" if len(rows) == 1 else "s"))
    for r in rows:
        L.append("  %-30s %-18s gw %-15s transit %s" % (r["segment"][:30], r["subnet"], r["gateway"], r["vlan"]))
    L += ["  build      %s, then %s --commit --expect <the digest it prints>   (undo: list the segment in mig_skip_%s, "
          "the same two)" % (cmd, cmd, site),
          "  switch     the lines in switch_requirements.txt, then  %s --check-leaves" % cmd,
          "  verify     %s --verify" % cmd,
          "  move       %s --move --vm wave.csv --commit   (vMotion, then NSX tags; or the names in mig_move_vms_%s)"
          % (cmd, site),
          "             undo: %s --return --vm wave.csv --commit (back where they were, tags too)" % cmd]
    strict_ = not _mig_true(_mig_key(cfg, "mig_cutover_with_blue_vms", site))
    for r in rows:
        h = r["subnet"] or r["segment"]
        L += ["  %s  %s" % (h, r["segment"]),
              "    cutover    %s --cutover %s --commit   (%sundo: --rollback)"
              % (cmd, h, "once no VM is left on Blue; " if strict_ else ""),
              "    unbridge   %s --unbridge %s --commit   (once no VM is left on Blue; undo: --cutover)" % (cmd, h),
              "    retire     %s --retire %s --commit   (no undo)" % (cmd, h),
              "    rollback   %s --rollback %s --commit   (until retired)" % (cmd, h)]
    L += ["  no impact  %s --impact" % cmd,
          "  edges      %s --edges --commit   (undo: %s --edges --remove --commit, once nothing is bridged)" % (cmd, cmd), ""]
    return "\n".join(L)


def mig_manual_steps(site, label, results, users, tags=None, tag_host=None, tag_user="admin"):
    """What the run does, call by call, in order, every path resolved: the track for doing it by hand."""
    L = ["MANUAL STEPS   %s   %s   %s" % (site, label, now()), "=" * 74,
         "The calls this run makes, in order, with every path resolved. For use only when the tool",
         "cannot run. An update is: GET the object, set the fields shown, PUT the whole object back.",
         "Each step is safe to run again: a create runs only if the object is absent (404), a delete",
         "only if it is present (200), and an update carries the _revision it read, so NSX refuses it",
         "if the object changed since: read it again. curl prompts for each password.", ""]
    n = 0
    for t in tags or []:
        if t.get("action") == "ADD" and t.get("external_id"):
            n += 1
            L += ["%d  Green NSX tags on %s   [ADD]" % (n, t["vm"]),
                  "   curl -k -u %s -X POST -H 'Content-Type: application/json' \\" % tag_user,
                  "     -d '%s' \\" % json.dumps({"external_id": t["external_id"], "tags": t["add"]}, sort_keys=True),
                  "     'https://%s/api/v1/fabric/virtual-machines?action=add_tags'" % tag_host, ""]
    for r in results:
        n += 1
        url = "https://%s/global-manager/api/v1/global-infra%s" % (r.get("host"), r["path"])
        u = users.get(r.get("host")) or "admin"
        act = r["action"]
        L.append("%d  %s %s %s   [%s]" % (n, r["side"], r["kind"], r["id"], act))
        if act == "UNCHANGED":
            L.append("   already in place%s" % (": %s" % r["detail"] if r.get("detail") else ""))
        elif act in ("BLOCKED", "ERROR", "HELD"):
            L.append("   %s: %s" % (act.lower(), r.get("detail")))
        elif act == "ADD":
            L += ["   [ \"$(curl -sk -u %s -o /dev/null -w '%%{http_code}' %s)\" = 404 ] && \\" % (u, url),
                  "   curl -k -u %s -X PATCH -H 'Content-Type: application/json' \\" % u,
                  "     -d '%s' \\" % json.dumps(r.get("body"), sort_keys=True), "     %s" % url]
        elif act == "UPDATE":
            f = re.sub(r"[^A-Za-z0-9_.-]+", "_", "%s_%s" % (r["side"], r["id"])).strip("_") + ".json"
            L.append("   curl -k -u %s %s > %s" % (u, url, f))
            for ch in r.get("change") or []:
                L.append("   in %s set \"%s\" to %s" % (f, ch["field"], json.dumps(ch["to"], sort_keys=True)))
            L += ["   curl -k -u %s -X PUT -H 'Content-Type: application/json' -d @%s \\" % (u, f), "     %s" % url]
        elif act == "DELETE":
            L.append("   [ \"$(curl -sk -u %s -o /dev/null -w '%%{http_code}' %s)\" = 200 ] && curl -k -u %s -X DELETE %s"
                     % (u, url, u, url))
        if r.get("wait") and act not in ("UNCHANGED", "BLOCKED", "ERROR", "HELD"):
            L.append("   %s" % r["wait"])
        L.append("")
    return "\n".join(L)


def mig_impact_checks(a, cfg, site, blue, balarms, rows, res, outdir, st, scope_key):
    """Blue now against a baseline: the one the state holds for this scope (--impact), or the
    snapshot in an earlier run's evidence (--impact DIR). A change outside the scope fails; new open
    Blue alarms are listed for the operator to explain."""
    if a.impact == "@state":
        base = (st.get("baselines") or {}).get(scope_key) if scope_key else None
        if not base:
            sys.exit("no baseline recorded for %s. Record one with: migpath --config <cfg>%s --baseline"
                     % (scope_key or "this scope", " --test" if getattr(a, "test", False) else ""))
        fn = "the %s baseline (%s)" % (scope_key, base.get("evidence"))
    else:
        fn = a.impact if os.path.isfile(a.impact) else os.path.join(a.impact, "blue_snapshot.json")
        if not os.path.exists(fn):
            sys.exit("no blue_snapshot.json in %s: pass the evidence directory of an earlier migpath run" % a.impact)
        with open(fn) as fh:
            base = json.load(fh)
    scope = mig_blue_scope(a, cfg, site, blue, res, rows)
    imp = mig_impact(base.get("objects") or {}, _mig_norm(blue["snapshot"]), scope)
    touched = imp["changed"] + imp["added"] + imp["removed"]
    out = [{"area": "impact", "item": "Blue changes since %s" % base.get("taken", "baseline"),
            "state": "FAIL" if imp["out_of_scope"] else "PASS",
            "detail": ("outside the scope: %s" % ", ".join(imp["out_of_scope"])) if imp["out_of_scope"] else
                      ("%d in scope: %s" % (len(touched), ", ".join(p.rsplit("/", 1)[-1] for p in touched))
                       if touched else "nothing changed on Blue")}]
    new_alarms = {}
    for host, was in sorted((base.get("alarms") or {}).items()):
        now_ = (balarms or {}).get(host)
        if was is None or now_ is None:
            out.append({"area": "impact", "item": "Blue open alarms on %s" % host, "state": "WARN",
                        "detail": "not readable %s" % ("in the baseline" if was is None else "now")})
            continue
        new = sorted(set(now_) - set(was))
        new_alarms[host] = {i: now_[i] for i in new}
        out.append({"area": "impact", "item": "Blue open alarms on %s" % host, "state": "WARN" if new else "PASS",
                    "detail": "; ".join("%s/%s on %s (%s)" % (now_[i].get("feature_name"), now_[i].get("event_type"),
                                                           now_[i].get("entity_id"), now_[i].get("severity"))
                                        for i in new[:4]) + (" (+%d more)" % (len(new) - 4) if len(new) > 4 else "")
                              if new else "no new open alarm since the baseline"})
    write_json(outdir, "impact_report", {"baseline": fn, "baseline_taken": base.get("taken"), "impact": imp,
                                         "new_alarms": new_alarms})
    return out


# ---------------------------------------------------------------- migpath: bridge edges (--edges)
# The bridge edge pair on each side, built from a reference edge on the same Local Manager: its
# placement, management network, TEP pool, DNS and NTP. Each new edge gets one more switch, on a
# spare fastpath vNIC, attached to the bridge VLAN zone and to a trunk port group made for it on the
# reference edge's VDS. Transport nodes and edge clusters use the /api/v1 fabric calls, which NSX
# 4.2.3 and 9.1.1 both serve; the zone is a Policy object. Every step reads first, so a run that
# stopped part way is finished by running it again.
MIG_BRIDGE_SWITCH = "nvds-migration-bridge"
MIG_OWN = {"scope": "fleetparity", "tag": "migration-bridge"}
MIG_PTZ = "/policy/api/v1/infra/sites/default/enforcement-points/default/transport-zones"
MIG_FF = ("SMALL", "MEDIUM", "LARGE", "XLARGE")
MIG_OWN_PG = "fleetparity migpath"
_V = "{urn:vim25}"
_XSI = "{http://www.w3.org/2001/XMLSchema-instance}"
_SOAPENV = "{http://schemas.xmlsoap.org/soap/envelope/}"


def _mig_lm(host, H, path, method="GET", body=None, timeout=60, retries=1):
    return http("https://%s%s" % (host, path), method=method, headers=H, body=body, timeout=timeout, retries=retries)


def _mig_lm_list(host, H, path):
    out, cur = [], None
    for _ in range(50):
        p = path if not cur else path + ("&" if "?" in path else "?") + "cursor=" + urllib.parse.quote(str(cur))
        st, b = _mig_lm(host, H, p)
        if st != 200 or not isinstance(b, dict):
            return None, st
        out.extend(_res(b))
        cur = b.get("cursor")
        if not cur:
            break
    return out, 200


def _mig_ranges(vlans):
    out = []
    for v in sorted(set(vlans)):
        if out and v == out[-1][1] + 1:
            out[-1][1] = v
        else:
            out.append([v, v])
    return [tuple(x) for x in out]


def _mig_rtext(rs):
    return ",".join(("%d-%d" % r) if r[0] != r[1] else str(r[0]) for r in rs)


def _mig_vernum(v):
    return tuple(int(x) for x in re.findall(r"\d+", str(v or ""))[:3])


def _mig_owned(o):
    return any(t.get("scope") == MIG_OWN["scope"] and t.get("tag") == MIG_OWN["tag"] for t in (o or {}).get("tags") or [])


def _mig_pw_rule(pw):
    """What a password lacks against NSX's default appliance rule; checked before anything is written."""
    pw = pw or ""
    return [n for n, ok in (("12 characters", len(pw) >= 12), ("a lower-case letter", re.search(r"[a-z]", pw)),
                            ("an upper-case letter", re.search(r"[A-Z]", pw)), ("a digit", re.search(r"\d", pw)),
                            ("a special character", re.search(r"[^A-Za-z0-9]", pw)),
                            ("5 different characters", len(set(pw)) >= 5)) if not ok]


def _mig_new_pw(env, cfg, keys, label):
    """A password for new edges: from the environment or the config, else typed twice. Never stored."""
    v = os.environ.get(env)
    if v:
        return v
    for k in keys:
        if cfg.get(k):
            return str(cfg[k])
    for _ in range(3):
        try:
            p1 = getpass.getpass("      %s: " % label)
            p2 = getpass.getpass("      %s, again: " % label)
        except EOFError:
            break
        if p1 and p1 == p2:
            return p1
        print("      the two entries differ or are empty")
    sys.exit("no %s: nothing was written. Set %s or type it at the prompt" % (label, env))


def mig_lm_of(host, H, loc, sites=None):
    """(the Local Manager of one location, as its Global Manager has it registered; why not)."""
    s_ = next((x for x in sites or [] if loc in (x.get("id"), x.get("display_name"))), None)
    for ci in (s_ or {}).get("site_connection_info") or []:
        if ci.get("fqdn"):
            return str(ci["fqdn"]).strip(), None
    st, ep = gm_get(host, H, "/sites/%s/enforcement-points/default" % ((s_ or {}).get("id") or loc))
    for ci in (ep or {}).get("connection_info") or [] if st == 200 and isinstance(ep, dict) else []:
        a_ = ci.get("enforcement_point_address") or ci.get("fqdn")
        if a_:
            return str(a_).strip(), None
    return None, "location %s on %s: no Local Manager address (HTTP %s)" % (loc, host, st)


# ---- lists kept in a .csv: a wave of VMs (move_vms, return_vms), or of segments (scope, skip)
MIG_LIST_FILES = (("mig_move_vms", "vm"), ("mig_return_vms", "vm"), ("mig_scope", "segment"), ("mig_skip", "segment"))
_MIG_COLS = {"vm": ("vm", "vm name", "vm_name", "vmname", "name", "virtual machine", "virtual_machine"),
             "segment": ("subnet", "segment", "cidr", "network", "segment_name", "name")}
_MIG_SUBNET_COLS = ("subnet", "segment", "cidr", "network")


def mig_read_list_file(path, kind):
    """(values, {VM lower: subnet}, error) from one .csv a list of the config names. Its VM column (vm, name,
    vm_name) for a VM list, its subnet column (subnet, segment, cidr) for a segment list, else its first column;
    for a VM list also its subnet column, the segment that VM must be on. A first row that names a known column
    is the header. Blank rows and rows starting with # are skipped. Saved from Excel (UTF-8 with a BOM, ; or tab
    between columns) it reads the same. migpath_vms_<site>.csv and migpath_segments_<site>.csv, filtered to the
    rows wanted, are such files."""
    try:
        with open(path, newline="", encoding="utf-8-sig") as fh:
            text = fh.read()
    except (OSError, UnicodeDecodeError) as e:
        return None, None, str(e)
    try:
        dialect = csv.Sniffer().sniff(text[:4096], delimiters=",;\t") if text.strip() else csv.excel
    except csv.Error:
        dialect = csv.excel
    rows = [r for r in csv.reader(io.StringIO(text), dialect)
            if any(c.strip() for c in r) and not r[0].strip().startswith("#")]
    if not rows:
        return [], {}, None
    head = [c.strip().lower() for c in rows[0]]
    col = next((head.index(n) for n in _MIG_COLS[kind] if n in head), None)
    sub = next((head.index(n) for n in _MIG_SUBNET_COLS if n in head), None) if kind == "vm" else None
    body = rows[1:] if col is not None or sub is not None else rows
    col = 0 if col is None else col
    vals, expect = [], {}
    for r in body:
        v = r[col].strip() if col < len(r) else ""
        if not v:
            continue
        vals.append(v)
        if sub is not None and sub < len(r) and r[sub].strip():
            expect[v.lower()] = r[sub].strip()
    return vals, expect, None


def mig_list_files(cfg, site, base):
    """Each item of move_vms, return_vms, scope and skip (the site's and the shared ones) that names a .csv is
    replaced by what the file lists, so a wave is a file and the config names the waves. A file not read stops
    the run before anything is read. Kept for the run: cfg["_list_from"] {(key, item lower): file} and
    cfg["_vm_subnet"] {VM lower: (subnet, file)}. Returns checks."""
    checks = []
    frm, want = cfg.setdefault("_list_from", {}), cfg.setdefault("_vm_subnet", {})
    for key, kind in MIG_LIST_FILES:
        for k in (key, "%s_%s" % (key, site)):
            items = _mig_items(cfg.get(k))
            if not any(str(x).lower().endswith(".csv") for x in items):
                continue
            out = []
            for it in items:
                if not str(it).lower().endswith(".csv"):
                    out.append(it)
                    continue
                path = it if os.path.isabs(it) else os.path.join(base, it)
                vals, exp, err = mig_read_list_file(path, kind)
                if vals is None:
                    checks.append({"area": "config", "item": "%s, listed in %s" % (it, k), "state": "FAIL",
                                   "detail": "not read (%s): its %s are not known" % (err, "VMs" if kind == "vm" else "segments")})
                    continue
                if not vals:
                    checks.append({"area": "config", "item": "%s, listed in %s" % (it, k), "state": "WARN",
                                   "detail": "no rows: it names nothing"})
                for v in vals:
                    frm.setdefault((key, v.lower()), it)
                for v, s_ in exp.items():
                    want[v] = (s_, it)
                out += vals
            cfg[k] = out
    return checks


def _mig_seg_is(value, r):
    """True when `value` (a subnet, a segment name or id, as a wave file gives it) names row r's segment."""
    v = str(value or "").strip()
    if v in (r.get("segment"), r.get("name"), r.get("subnet")):
        return True
    try:
        return r.get("net") is not None and ipaddress.ip_network(v, strict=False) == r["net"]
    except ValueError:
        return False


def mig_config_checks(cfg):
    """The config as a whole, every site at once, before anything is read from a manager: transit VLANs
    that are VLANs, no bridge edge name or address used twice, no two sites on one leaf with overlapping
    transit VLANs, a [primary, backup] pair per side. A FAIL here stops the run."""
    out = []

    def c(item, state, detail):
        out.append({"area": "config", "item": item, "state": state, "detail": detail})
    sites = [str(x) for x in _mig_items(cfg.get("mig_sites"))]
    names, ips, pools = {}, {}, {}
    for x in sites:
        raw = _mig_items(_mig_key(cfg, "mig_transit_vlans", x))
        vl = _mig_vlans(raw)
        bad_ = sorted({v for v in vl if not 1 <= v <= 4094})
        junk = [it for it in raw if not re.fullmatch(r"\d+(\s*-\s*\d+)?", str(it).strip())]
        if bad_ or junk:
            c("transit VLANs of %s" % x, "FAIL", "%s: VLAN IDs run 1-4094" % (", ".join(junk) or "%d-%d" % (bad_[0], bad_[-1])))
        pools[x] = set(vl)
        infra = set(_mig_vlans(_mig_key(cfg, "mig_infra_vlans", x)))
        if infra & pools[x]:
            c("transit VLANs of %s" % x, "FAIL", "%s also in mig_infra_vlans_%s: a transit VLAN is never infrastructure"
              % (_mig_rtext(_mig_ranges(sorted(infra & pools[x]))), x))
        for side, pre in (("Green", "mig_"), ("Blue", "mig_blue_")):
            ed = [str(e).strip() for e in _mig_items(cfg.get("%sbridge_edges_%s" % (pre, x))) if str(e).strip()]
            ip_ = [str(i).strip() for i in _mig_items(cfg.get("%sbridge_edge_ips_%s" % (pre, x))) if str(i).strip()]
            if ed and len(ed) != 2:
                c("%s bridge edges of %s" % (side, x), "FAIL", "%s: name two, [primary, backup]" % ", ".join(ed))
            if ip_ and len(ip_) != len(ed):
                c("%s bridge edge addresses of %s" % (side, x), "FAIL", "%d address(es) for %d edge(s)" % (len(ip_), len(ed)))
            for e in ed:
                names.setdefault(e.lower().split(".")[0], []).append("%s %s" % (x, side))
            for i in ip_:
                try:
                    ipaddress.ip_address(i)
                except ValueError:
                    c("%s bridge edge addresses of %s" % (side, x), "FAIL", "%r is not an address" % i)
                ips.setdefault(i, []).append("%s %s" % (x, side))
    for n, where in sorted(names.items()):
        if len(where) > 1:
            c("bridge edge %s" % n, "FAIL", "named for %s: one edge, one place" % " and ".join(where))
    for i, where in sorted(ips.items()):
        if len(where) > 1:
            c("bridge edge address %s" % i, "FAIL", "given to %s" % " and ".join(where))
    if cfg.get("_v2"):                  # a sign-in in one place: in each site's block, or once for every site
        top = {v: ".".join(k) for k, v in reversed(_CFG_V2_SHARED)}
        for k in _CFG_SITE_SIGNINS:
            per = [x for x in sites if "%s_%s" % (k, x) in cfg]
            if per and cfg.get(k) not in (None, "") and k in top:
                c("%s at the top of the file" % top[k], "FAIL", "set once for every site there, and again in %s: keep one "
                  "place. fp --by-site moves it into each site's block" % ", ".join("%s_%s" % (k, x) for x in per))
    leaves = {x: {str(h).lower() for h in _mig_items(cfg.get("mig_bridge_leaves_%s" % x))} for x in sites}
    for i, x in enumerate(sites):
        for y in sites[i + 1:]:
            both = pools.get(x, set()) & pools.get(y, set())
            if leaves[x] & leaves[y] and both:
                c("transit VLANs of %s and %s" % (x, y), "FAIL", "both on %s and both use %s: one VLAN, one segment"
                  % (", ".join(sorted(leaves[x] & leaves[y])), _mig_rtext(_mig_ranges(sorted(both)))))
    return out


def mig_edge_cfg(cfg, site, side):
    pre = "mig_" if side == "Green" else "mig_blue_"

    def k(key, default=None):
        return _mig_key(cfg, pre + key, site, default)
    return {"side": side, "pre": pre,
            "lm": str((cfg.get("nsx_lm_host_%s" % site) if side == "Green" else _mig_key(cfg, "mig_blue_lm_host", site))
                      or "").strip(),
            "template": k("bridge_edge_template"), "cluster": k("bridge_edge_cluster"),
            "edges": _mig_items(k("bridge_edges")), "ips": _mig_items(k("bridge_edge_ips")),
            "tz": k("bridge_vlan_tz"),
            "pg": str(k("bridge_trunk_pg") or ("pg-migration-bridge-%s%s" % ("" if side == "Green" else "blue-", site))),
            "ff": str(k("bridge_edge_form_factor") or "MEDIUM").upper(),
            "uplink": str(_mig_key(cfg, "mig_bridge_uplink_profile", site) or "nsx-edge-single-nic-uplink-profile"),
            "domain": str(cfg.get("mig_edge_domain") or cfg.get("fed_gm_domain") or "").strip(". "),
            "vlans": _mig_vlans(_mig_key(cfg, "mig_transit_vlans", site))}


# ---- vCenter: vSphere Web Services (SOAP). vCenter's REST API lists port groups but cannot create one.
class MigVim(object):
    def __init__(self, host):
        self.host, self.cookie, self.pc, self.sm, self.ver = host, None, None, None, "6.7"

    def call(self, method, inner, timeout=90):
        env = ('<?xml version="1.0" encoding="UTF-8"?>'
               '<soapenv:Envelope xmlns:soapenv="http://schemas.xmlsoap.org/soap/envelope/" '
               'xmlns:xsd="http://www.w3.org/2001/XMLSchema" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">'
               '<soapenv:Body><%s xmlns="urn:vim25">%s</%s></soapenv:Body></soapenv:Envelope>' % (method, inner, method))
        hdr = {"Content-Type": "text/xml; charset=utf-8", "SOAPAction": '"urn:vim25/%s"' % self.ver}
        if self.cookie:
            hdr["Cookie"] = self.cookie
        req = urllib.request.Request("https://%s/sdk" % self.host, data=env.encode("utf-8"), headers=hdr, method="POST")
        try:
            with urllib.request.urlopen(req, context=CTX, timeout=timeout) as r:
                st, raw, ck = r.status, r.read(), r.headers.get("Set-Cookie")
        except urllib.error.HTTPError as e:
            st, raw, ck = e.code, e.read(), None
        except Exception as e:
            return None, "no answer from %s: %s" % (self.host, e)
        m = re.search(r'vmware_soap_session="?[^";]+"?', ck or "")
        if m:
            self.cookie = m.group(0)
        try:
            body = ET.fromstring(raw).find(_SOAPENV + "Body")
        except ET.ParseError:
            return None, "HTTP %s, not SOAP: %s" % (st, raw[:160].decode("utf-8", "replace"))
        if body is None or not len(body):
            return None, "HTTP %s, empty SOAP body" % st
        if body[0].tag == _SOAPENV + "Fault":
            return None, (body[0].findtext("faultstring") or "SOAP fault").strip()[:300]
        return body[0], None

    def login(self, user, pw):
        st, b = http("https://%s/sdk/vimServiceVersions.xml" % self.host, timeout=30)
        m = re.search(r"<name>\s*urn:vim25\s*</name>\s*<version>\s*([\d.]+)\s*</version>",
                      (b or {}).get("_raw") or "" if isinstance(b, dict) else "")
        if m:
            self.ver = m.group(1)
        r, err = self.call("RetrieveServiceContent", '<_this type="ServiceInstance">ServiceInstance</_this>')
        if err:
            return err
        rv = r.find(_V + "returnval")
        self.pc = rv.findtext(_V + "propertyCollector") if rv is not None else None
        self.sm = rv.findtext(_V + "sessionManager") if rv is not None else None
        self.om = (rv.findtext(_V + "setting") if rv is not None else None) or "VpxSettings"
        self.uuid = rv.findtext(_V + "about/" + _V + "instanceUuid") if rv is not None else None
        if not self.pc or not self.sm:
            return "no property collector in the service content"
        r, err = self.call("Login", '<_this type="SessionManager">%s</_this><userName>%s</userName><password>%s</password>'
                           % (xml_escape(self.sm), xml_escape(user or ""), xml_escape(pw or "")))
        return err

    def props(self, typ, objs, paths):
        """{moref: {path: <val> element}} for objects of one type."""
        spec = "<specSet><propSet><type>%s</type>%s</propSet>%s</specSet><options/>" % (
            typ, "".join("<pathSet>%s</pathSet>" % p for p in paths),
            "".join('<objectSet><obj type="%s">%s</obj></objectSet>' % (typ, xml_escape(o)) for o in objs))
        r, err = self.call("RetrievePropertiesEx", '<_this type="PropertyCollector">%s</_this>%s' % (xml_escape(self.pc), spec))
        out = {}
        while not err and r is not None:
            rv = r.find(_V + "returnval")
            if rv is None:
                break
            for o in rv.findall(_V + "objects"):
                out[o.findtext(_V + "obj")] = {p.findtext(_V + "name"): p.find(_V + "val") for p in o.findall(_V + "propSet")}
            tok = rv.findtext(_V + "token")
            if not tok:
                break
            r, err = self.call("ContinueRetrievePropertiesEx", '<_this type="PropertyCollector">%s</_this><token>%s</token>'
                               % (xml_escape(self.pc), xml_escape(tok)))
        return (None, err) if err else (out, None)

    def task(self, method, this_type, this, spec, limit=300):
        """Run a vCenter task to its end: (result moref or text, error)."""
        r, err = self.call(method, '<_this type="%s">%s</_this>%s' % (this_type, xml_escape(this), spec))
        if err:
            return None, err
        tid, t0 = r.findtext(_V + "returnval"), time.time()
        while True:
            got, err = self.props("Task", [tid], ["info"])
            if err:
                return None, err
            info = (got.get(tid) or {}).get("info")
            state = info.findtext(_V + "state") if info is not None else None
            if state == "success":
                return info.findtext(_V + "result") or "", None
            if state == "error":
                return None, (info.findtext(_V + "error/" + _V + "localizedMessage") or "task failed").strip()[:300]
            if time.time() - t0 > limit:
                return None, "task %s still %s after %d s" % (tid, state, limit)
            time.sleep(2)

    def logout(self):
        if self.cookie and self.sm:
            self.call("Logout", '<_this type="SessionManager">%s</_this>' % xml_escape(self.sm), timeout=20)


def _mig_pg_port(vlans):
    """VMwareDVSPortSetting for the bridge trunk, in schema order (checked against pyVmomi 9.1.1)."""
    return ('<defaultPortConfig xsi:type="VMwareDVSPortSetting">'
            '<vlan xsi:type="VmwareDistributedVirtualSwitchTrunkVlanSpec"><inherited>false</inherited>%s</vlan>'
            '<macManagementPolicy><inherited>false</inherited><allowPromiscuous>false</allowPromiscuous>'
            '<macChanges>false</macChanges><forgedTransmits>true</forgedTransmits><macLearningPolicy>'
            '<inherited>false</inherited><enabled>true</enabled><allowUnicastFlooding>true</allowUnicastFlooding>'
            '<limit>4096</limit><limitPolicy>DROP</limitPolicy></macLearningPolicy></macManagementPolicy>'
            '</defaultPortConfig>' % "".join("<vlanId><start>%d</start><end>%d</end></vlanId>" % r
                                             for r in _mig_ranges(vlans)))


def _mig_pg_view(el):
    """What a port group does for a bridge, read from its DVPortgroupConfigInfo."""
    d = {"trunk": [], "forged": False, "promisc": False, "learning": False, "flooding": False, "description": "",
         "version": None}
    if el is None:
        return d
    d["description"], d["version"] = el.findtext(_V + "description") or "", el.findtext(_V + "configVersion")
    dpc = el.find(_V + "defaultPortConfig")
    vl = dpc.find(_V + "vlan") if dpc is not None else None
    if vl is not None and "Trunk" in (vl.get(_XSI + "type") or ""):
        d["trunk"] = [(int(x.findtext(_V + "start") or 0), int(x.findtext(_V + "end") or 0))
                      for x in vl.findall(_V + "vlanId")]
    mm = dpc.find(_V + "macManagementPolicy") if dpc is not None else None
    ml = mm.find(_V + "macLearningPolicy") if mm is not None else None

    def t(e, n):
        return e is not None and (e.findtext(_V + n) or "").strip().lower() == "true"
    d.update(forged=t(mm, "forgedTransmits"), promisc=t(mm, "allowPromiscuous"), learning=t(ml, "enabled"),
             flooding=t(ml, "allowUnicastFlooding"))
    return d


def _mig_pg_gaps(view, vlans):
    """What a port group lacks to carry the bridge: empty when it is fit."""
    have = set()
    for a_, b_ in view.get("trunk") or []:
        have.update(range(a_, b_ + 1))
    gaps = []
    miss = sorted(set(vlans) - have)
    if miss:
        gaps.append("trunk lacks VLAN %s" % _mig_rtext(_mig_ranges(miss)))
    if not view.get("forged"):
        gaps.append("forged transmits rejected")
    if not (view.get("promisc") or (view.get("learning") and view.get("flooding"))):
        gaps.append("no MAC learning with unknown-unicast flooding")
    return gaps


def mig_edge_vc(cfg, site, side, server):
    """Log in to the vCenter NSX deploys this side's edges through (the reference edge's compute manager)."""
    key = "blue" if side == "Blue" else "green"
    user = cfg.get("mig_%s_vc_user" % key) or "administrator@vsphere.local"
    mine = {str(cfg.get(k) or "").strip().lower() for k in (
        ("mig_blue_vc_%s" % site, "mig_blue_vc_remote_%s" % site) if side == "Blue" else ("mig_green_vc_%s" % site,))}
    own = str(server).lower() in mine
    pw = ((os.environ.get("FLEETPARITY_MIG_%s_VC_PASSWORD" % key.upper()) or cfg.get("mig_%s_vc_password" % key))
          if own else None)
    # another vCenter (the management one, say): its own setting, never a password kept for a different vCenter
    pkey = "mig_%s_vc_password" % key if own else "mig_%s_edge_vc_password_%s" % (key, site)
    pw = pw or (None if own else cfg.get(pkey)) or os.environ.get(env_key("FLEETPARITY_MIG_EDGE_VC_PASSWORD", server)) or ""
    if not pw and not DRY:
        pw = getpass.getpass("      vCenter %s '%s' password (it deploys %s's bridge edges; %s): " % (
            server, user, side, _mig_shown(pkey)))
    v = MigVim(server)
    return v, v.login(user, pw)


# ---- reading and planning, one side
def _mig_tn_ips(tn):
    ndi = tn.get("node_deployment_info") or {}
    ips = {str(x) for x in (ndi.get("ip_addresses") or []) + (ndi.get("discovered_ip_addresses") or [])}
    vdc = (ndi.get("deployment_config") or {}).get("vm_deployment_config") or {}
    for s_ in vdc.get("management_port_subnets") or []:
        ips.update(str(x) for x in s_.get("ip_addresses") or [])
    return ips


def _mig_dns(fqdn):
    try:
        return sorted({ai[4][0] for ai in socket.getaddrinfo(fqdn, None, socket.AF_INET)})
    except (socket.gaierror, UnicodeError, OSError):
        return []


def _mig_ptr(ip):
    try:
        return socket.gethostbyaddr(ip)[0]
    except (socket.herror, socket.gaierror, OSError):
        return None


def _mig_answers(ip):
    """True when something answers ping at ip."""
    try:
        return subprocess.run(["ping", "-c", "2", "-W", "1", ip], stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL, timeout=15).returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _mig_state_text(s):
    """(state, deployment state, every failure message NSX gives) from a transport node's state."""
    s = s or {}
    nds = (s.get("node_deployment_state") or {})
    msgs = [nds.get("failure_message"), s.get("failure_message")] + [
        x.get("failure_message") for x in s.get("details") or [] if isinstance(x, dict)]
    seen = []
    for m in msgs:
        if m and str(m) not in seen:
            seen.append(str(m))
    return s.get("state"), nds.get("state"), "; ".join(seen)


MIG_DRS_RULE = "fleetparity-migpath-%s-apart"      # %s: the bridge edge cluster


def mig_drs_read(vim, compute_id, names):
    """The cluster the reference edge is deployed into, the VMs named there, and the enabled
    anti-affinity rule that keeps them apart, if one exists. Reads only."""
    out = {"cluster": None, "cluster_name": None, "vms": {}, "rule": None, "error": None}
    cl = compute_id
    if str(compute_id).startswith("resgroup-"):
        got, err = vim.props("ResourcePool", [compute_id], ["owner"])
        val = ((got or {}).get(compute_id) or {}).get("owner")
        if err or val is None:
            out["error"] = "resource pool %s: %s" % (compute_id, err or "no owner")
            return out
        cl = val.text
    got, err = vim.props("ClusterComputeResource", [cl], ["name", "configurationEx", "host"])
    p_ = (got or {}).get(cl) or {}
    if err or p_.get("name") is None:
        out["error"] = "cluster %s: %s" % (cl, err or "not read")
        return out
    out["cluster"], out["cluster_name"] = cl, p_["name"].text
    hosts = [h.text for h in (p_.get("host") if p_.get("host") is not None else [])]
    got, err = vim.props("HostSystem", hosts, ["vm"]) if hosts else ({}, None)
    if err:
        out["error"] = "hosts of %s: %s" % (out["cluster_name"], err)
        return out
    vms = [v.text for h in (got or {}).values() for v in (h.get("vm") if h.get("vm") is not None else [])]
    got, err = vim.props("VirtualMachine", vms, ["name"]) if vms else ({}, None)
    if err:
        out["error"] = "VMs of %s: %s" % (out["cluster_name"], err)
        return out
    want = {str(n).lower() for n in names}
    for m, v in (got or {}).items():
        nm = v.get("name").text if v.get("name") is not None else ""
        if str(nm).lower() in want:
            out["vms"][str(nm).lower()] = m
    mine = set(out["vms"].values()) if len(out["vms"]) == len(names) else set()
    cfgx = p_.get("configurationEx")
    for rule in (cfgx.findall(_V + "rule") if cfgx is not None else []):
        if rule.get(_XSI + "type") != "ClusterAntiAffinityRuleSpec" or rule.findtext(_V + "enabled") != "true":
            continue
        if mine and mine <= {v.text for v in rule.findall(_V + "vm")}:
            out["rule"] = rule.findtext(_V + "name") or "?"
            break
    return out


def mig_drs_spec(name, vms):
    return ('<spec xsi:type="ClusterConfigSpecEx"><rulesSpec><operation>add</operation>'
            '<info xsi:type="ClusterAntiAffinityRuleSpec"><enabled>true</enabled><name>%s</name><userCreated>true</userCreated>%s'
            '</info></rulesSpec></spec><modify>true</modify>' % (
                xml_escape(name), "".join('<vm type="VirtualMachine">%s</vm>' % xml_escape(v) for v in vms)))


def mig_edge_side(cfg, site, e, H, lmread, vc_login):
    """One side: pre-flight checks and the plan rows. Reads only. `lmread` is what mig_edge_lm_read
    returned; vc_login(server) gives a logged-in MigVim and an error. Returns (checks, rows, ctx)."""
    side, host = e["side"], e["lm"]
    checks, rows = [], []
    x = {"side": side, "host": host, "H": H, "e": e, "vim": None}

    def c(item, state, detail=""):
        checks.append({"area": "edges", "item": "%s %s" % (side, item), "state": state, "detail": str(detail)[:400]})

    def row(kind, id_, path, action, detail="", **kw):
        r = {"side": side, "kind": kind, "id": id_, "path": path, "host": host, "action": action, "detail": detail}
        r.update(kw)
        rows.append(r)
        return r

    if not lmread.get("version"):
        c("Local Manager %s" % host, "FAIL", "HTTP %s" % lmread.get("status"))
        return checks, rows, x
    c("Local Manager", "INFO", "%s  NSX %s" % (host, lmread["version"]))
    unread = ["%s (HTTP %s)" % (k, lmread.get(k + "_status")) for k in ("tns", "ecs", "tzs", "hsps")
              if lmread.get(k) is None]
    if unread:
        c("fabric read", "FAIL", "not read: %s" % ", ".join(unread))
        return checks, rows, x
    tns = [t for t in lmread["tns"] if (t.get("node_deployment_info") or {}).get("resource_type") == "EdgeNode"]
    byname = {}
    for t in tns:
        byname.setdefault(str(t.get("display_name") or "").strip().lower(), []).append(t)
    names = e["edges"]
    if len(names) != 2:
        c("bridge edges", "FAIL", "%sbridge_edges_%s must be [primary, backup]" % (e["pre"], site))
    if not e["cluster"] or not e["tz"]:
        c("bridge names", "FAIL", "set %sbridge_edge_cluster_%s and %sbridge_vlan_tz_%s" % (e["pre"], site, e["pre"], site))
    if e["ff"] not in MIG_FF:
        c("form factor", "FAIL", "%s is not one of %s" % (e["ff"], ", ".join(MIG_FF)))
    if not e["vlans"]:
        c("transit VLANs", "FAIL", "set mig_transit_vlans_%s: the trunk carries them" % site)

    # the reference edge: the one named, else an edge already in the subnet the new edges' addresses are in
    if not e["template"] and names:
        want = [str(i).strip() for i in e["ips"] if str(i).strip()] or [
            ip_ for n in names for ip_ in _mig_dns(n if "." in n or not e["domain"] else "%s.%s" % (n, e["domain"]))]
        cands = []
        for t_ in sorted(tns, key=lambda q: str(q.get("display_name") or "")):
            if str(t_.get("display_name") or "").strip().lower() in {str(n).lower() for n in names} or not want:
                continue
            full = t_
            if not (((t_.get("node_deployment_info") or {}).get("deployment_config") or {}).get("vm_deployment_config")):
                st_, full = _mig_lm(host, H, "/api/v1/transport-nodes/%s" % t_.get("id"))
                full = full if st_ == 200 and isinstance(full, dict) else {}
            nd_ = full.get("node_deployment_info") or {}
            vd_ = (nd_.get("deployment_config") or {}).get("vm_deployment_config") or {}
            try:
                sb_ = (vd_.get("management_port_subnets") or [{}])[0]
                net_ = ipaddress.ip_interface("%s/%s" % ((sb_.get("ip_addresses") or [""])[0], sb_.get("prefix_length"))).network
                if all(ipaddress.ip_address(w) in net_ for w in want) and vd_.get("vc_id"):
                    cands.append((t_.get("display_name"), net_))
            except (ValueError, TypeError):
                continue
        if cands:
            e["template"] = cands[0][0]
            c("reference edge", "INFO", "found: %s, the first edge in %s, where %s are" % (
                cands[0][0], cands[0][1], ", ".join(want)))
        elif want:
            c("reference edge", "FAIL", "no edge on %s has its management address in the subnet of %s: set the side's "
              "bridge.template to the edge to copy" % (host, ", ".join(want)))
    hits = byname.get(str(e["template"] or "").strip().lower()) or []
    t = None
    if not e["template"]:
        c("reference edge", "FAIL", "set %sbridge_edge_template_%s to an edge on %s to copy" % (e["pre"], site, host))
    elif len(hits) != 1:
        c("reference edge", "FAIL", "%s: %s on %s" % (e["template"], "not found" if not hits else "%d edges" % len(hits), host))
    else:
        st_, t = _mig_lm(host, H, "/api/v1/transport-nodes/%s" % hits[0].get("id"))
        if st_ != 200 or not isinstance(t, dict):
            c("reference edge", "FAIL", "%s: read HTTP %s" % (e["template"], st_))
            t = None
    x["template"] = t
    ndi = (t or {}).get("node_deployment_info") or {}
    dc = ndi.get("deployment_config") or {}
    vdc = dc.get("vm_deployment_config") or {}
    mnet = spare = pg_src = None
    if t is not None:
        subs = vdc.get("management_port_subnets") or []
        try:
            mnet = ipaddress.ip_interface("%s/%s" % ((subs[0].get("ip_addresses") or [""])[0], subs[0].get("prefix_length")))
        except (ValueError, IndexError, TypeError):
            mnet = None
        used, static = set(), []
        for hs in (t.get("host_switch_spec") or {}).get("host_switches") or []:
            used.update(str(p.get("device_name")) for p in hs.get("pnics") or [])
            specs = [hs.get("ip_assignment_spec") or {}] + list(hs.get("ip_assignment_specs") or [])
            static += [hs.get("host_switch_name") for s_ in specs if str(s_.get("resource_type") or "").startswith("StaticIp")
                       and "Pool" not in str(s_.get("resource_type"))]
        spare = next((n for n in ("fp-eth0", "fp-eth1", "fp-eth2", "fp-eth3") if n not in used), None)
        # A bridge edge runs no Tier-0. When the reference edge's four vNICs are all in use, a switch that
        # carries only VLAN zones and no TEP is its Tier-0 uplink switch: the copy leaves it out, and the
        # bridge takes the first vNIC that frees.
        x["drop_switches"] = []
        if not spare:
            tzt = {}
            for z in lmread["tzs"]:
                for k in ("realization_id", "unique_id", "id"):
                    if z.get(k):
                        tzt[str(z[k])] = z.get("tz_type")
            for hs in (t.get("host_switch_spec") or {}).get("host_switches") or []:
                eps = hs.get("transport_zone_endpoints") or []
                tep = str((hs.get("ip_assignment_spec") or {}).get("resource_type") or "")
                if eps and all(tzt.get(str(e.get("transport_zone_id"))) == "VLAN_BACKED" for e in eps) \
                        and tep in ("", "AssignedByDhcp"):
                    x["drop_switches"].append(hs.get("host_switch_name"))
                    for p in hs.get("pnics") or []:
                        used.discard(str(p.get("device_name")))
            spare = next((n for n in ("fp-eth0", "fp-eth1", "fp-eth2", "fp-eth3") if n not in used), None)
            if spare:
                c("spare vNIC", "INFO", "%s uses fp-eth0 to fp-eth3; the copy leaves out %s, its Tier-0 uplink switch, "
                  "which a bridge edge does not need, and the bridge takes %s" % (
                      e["template"], ", ".join(x["drop_switches"]), spare))
        nets = vdc.get("data_network_ids") or []
        idx = sorted(int(u[-1]) for u in used if re.fullmatch(r"fp-eth[0-3]", u))
        pg_src = nets[idx[0]] if idx and idx[0] < len(nets) else None
        if ndi.get("deployment_type") not in (None, "VIRTUAL_MACHINE") or not vdc.get("vc_id"):
            c("reference edge", "FAIL", "%s is not a VM NSX deployed through a vCenter" % e["template"])
            t = x["template"] = None
        elif not mnet or mnet.version != 4:
            c("reference edge", "FAIL", "%s: no static IPv4 management address to take the subnet from" % e["template"])
            t = x["template"] = None
        else:
            c("reference edge", "PASS", "%s: management %s, %s, vCenter compute %s" % (
                e["template"], mnet.network, dc.get("form_factor"), vdc.get("compute_id")))
        if static:
            c("TEP addresses", "FAIL", "%s takes its TEPs from a static list: new edges cannot reuse them. "
              "Use a reference edge whose TEPs come from a pool or DHCP" % ", ".join(static))
            t = x["template"] = None
        if t is not None and not spare:
            c("spare vNIC", "FAIL", "%s uses fp-eth0 to fp-eth3 for overlay: no vNIC left for the bridge. Use a "
              "reference edge with a free vNIC or one whose second switch carries only Tier-0 uplinks" % e["template"])
        if t is not None and not str(pg_src or "").startswith("dvportgroup-"):
            c("reference VDS", "FAIL", "%s's data vNICs are on %s, not a vSphere distributed port group: the trunk "
              "port group is made on that VDS" % (e["template"], pg_src or "nothing"))
    x.update(mnet=mnet, spare=spare, pg_src=pg_src)

    # uplink profile for the bridge switch: one uplink, nothing standby
    ups = [p for p in lmread["hsps"] if p.get("resource_type") == "UplinkHostSwitchProfile"
           and str(p.get("display_name") or "").lower() == e["uplink"].lower()]
    up = ups[0] if len(ups) == 1 else None
    team = (up or {}).get("teaming") or {}
    if not up:
        c("uplink profile", "FAIL", "%s: %s on %s. Set mig_bridge_uplink_profile to a profile with one uplink"
          % (e["uplink"], "not found" if not ups else "%d profiles" % len(ups), host))
    elif len(team.get("active_list") or []) != 1 or team.get("standby_list"):
        c("uplink profile", "FAIL", "%s must have exactly one active uplink and none standby" % e["uplink"])
        up = None
    x["uplink_id"] = (up or {}).get("id")
    x["uplink_name"] = ((team.get("active_list") or [{}])[0] or {}).get("uplink_name") if up else None

    # vCenter: the reference edge's compute manager
    vc_server = None
    if t is not None:
        st_, cm = _mig_lm(host, H, "/api/v1/fabric/compute-managers/%s" % vdc.get("vc_id"))
        vc_server = cm.get("server") if st_ == 200 and isinstance(cm, dict) else None
        if not vc_server:
            c("vCenter", "FAIL", "compute manager %s: read HTTP %s" % (vdc.get("vc_id"), st_))
    x["vc"] = vc_server
    pg, dvs, dvs_type, dvs_name = None, None, None, None
    if vc_server and str(pg_src or "").startswith("dvportgroup-"):
        vim, err = vc_login(vc_server)
        if err:
            c("vCenter", "FAIL", "%s: %s" % (vc_server, err))
        else:
            x["vim"] = vim
            got, err = vim.props("DistributedVirtualPortgroup", [pg_src], ["config.distributedVirtualSwitch"])
            val = ((got or {}).get(pg_src) or {}).get("config.distributedVirtualSwitch")
            if err or val is None:
                c("reference VDS", "FAIL", "%s on %s: %s" % (pg_src, vc_server, err or "not found"))
            else:
                dvs, dvs_type = val.text, val.get("type") or "VmwareDistributedVirtualSwitch"
                got, err = vim.props(dvs_type, [dvs], ["name", "portgroup", "summary.productInfo.version"])
                p_ = (got or {}).get(dvs) or {}
                dvs_name = p_.get("name").text if p_.get("name") is not None else dvs
                dvs_ver = p_.get("summary.productInfo.version").text if p_.get("summary.productInfo.version") is not None else ""
                pgs = [m.text for m in (p_.get("portgroup") if p_.get("portgroup") is not None else [])]
                got, err2 = vim.props("DistributedVirtualPortgroup", pgs, ["name"]) if pgs else ({}, None)
                if err or err2:
                    c("reference VDS", "FAIL", "%s: port groups not read: %s" % (dvs_name, err or err2))
                    dvs = None
                elif _mig_vernum(dvs_ver) < (6, 6):
                    c("reference VDS", "FAIL", "%s is VDS %s: MAC learning needs 6.6.0. Upgrade the VDS, or bridge "
                      "from edges on another VDS" % (dvs_name, dvs_ver or "unknown"))
                    dvs = None
                else:
                    hit = [m for m, v in got.items() if (v.get("name").text if v.get("name") is not None else "") == e["pg"]]
                    if hit:
                        got, err = vim.props("DistributedVirtualPortgroup", hit[:1], ["config"])
                        pg = {"moref": hit[0], "view": _mig_pg_view(((got or {}).get(hit[0]) or {}).get("config"))}
                    c("vCenter", "PASS", "%s, VDS %s (%d port groups)" % (vc_server, dvs_name, len(pgs)))
    x.update(pg=pg, dvs=dvs, dvs_type=dvs_type, dvs_name=dvs_name)

    # addresses of the new edges: DNS, or the config; in the reference edge's subnet; not in use
    used_ips = {}
    for tn_ in lmread["tns"]:
        for ip_ in _mig_tn_ips(tn_):
            used_ips.setdefault(ip_, tn_.get("display_name"))
    x["edges"] = {}
    for i, n in enumerate(names):
        have = byname.get(n.lower()) or []
        fq = n if "." in n or not e["domain"] else "%s.%s" % (n, e["domain"])
        dns = _mig_dns(fq)
        conf = e["ips"][i] if i < len(e["ips"]) else None
        ip, bad = None, None
        if conf:
            try:
                ip = str(ipaddress.ip_address(conf))
            except ValueError:
                bad = "%sbridge_edge_ips_%s: %r is not an address" % (e["pre"], site, conf)
            if ip and dns and ip not in dns:
                bad = "DNS says %s is %s; the config says %s" % (fq, ", ".join(dns), ip)
        elif len(dns) == 1:
            ip = dns[0]
        else:
            bad = ("no DNS record for %s: create its A and PTR records%s, or set %sbridge_edge_ips_%s" % (
                fq, " in %s" % mnet.network if mnet else "", e["pre"], site) if not dns
                else "%s resolves to %s: one address only" % (fq, ", ".join(dns)))
        x["edges"][n] = {"fqdn": fq, "ip": ip, "tn": have[0] if len(have) == 1 else None}
        if len(have) > 1:
            c("edge %s" % n, "FAIL", "%d edges named %s on %s" % (len(have), n, host))
            continue
        if have:
            c("edge %s" % n, "INFO", "exists on %s" % host)
            continue
        if not bad and mnet and ipaddress.ip_address(ip) not in mnet.network:
            bad = "%s is outside %s, the reference edge's management subnet" % (ip, mnet.network)
        if not bad and ip in used_ips:
            bad = "%s is the address of %s" % (ip, used_ips[ip])
        if not bad and ip and _mig_answers(ip):
            bad = "%s answers ping: something already has it" % ip
        if bad:
            c("edge %s address" % n, "FAIL", bad)
            x["edges"][n]["ip"] = None
            continue
        ptr = _mig_ptr(ip)
        c("edge %s address" % n, "PASS" if ptr and ptr.rstrip(".").lower() == fq.lower() else "WARN",
          "%s %s%s" % (fq, ip, "" if ptr and ptr.rstrip(".").lower() == fq.lower() else
                       ", no DNS record" if not dns else ", reverse DNS %s" % (ptr or "missing")))

    # the plan: zone, trunk, edges, cluster
    tzs = [z for z in lmread["tzs"] if str(z.get("display_name") or "").lower() == str(e["tz"] or "").lower()]
    tid = tzs[0].get("id") if tzs else ns_id(e["tz"])
    tzp = "%s/%s" % (MIG_PTZ, tid)
    x["tz_rid"] = None
    if len(tzs) > 1:
        row("transport-zone", e["tz"], tzp, "BLOCKED", "%d zones named %s" % (len(tzs), e["tz"]))
    elif tzs and tzs[0].get("tz_type") != "VLAN_BACKED":
        row("transport-zone", e["tz"], tzp, "BLOCKED", "%s is %s, not VLAN" % (e["tz"], tzs[0].get("tz_type")))
    elif tzs:
        x["tz_rid"] = tzs[0].get("realization_id") or tzs[0].get("unique_id") or tzs[0].get("id")
        row("transport-zone", e["tz"], tzp, "UNCHANGED", "VLAN zone")
    elif e["tz"]:
        row("transport-zone", e["tz"], tzp, "ADD", "VLAN zone on %s" % host, body={
            "display_name": e["tz"], "tz_type": "VLAN_BACKED", "tags": [dict(MIG_OWN)],
            "description": "fleetparity migpath: bridge zone for the migration"})
    pgp = "vc:%s/%s/%s" % (vc_server, dvs_name, e["pg"])
    want = {"name": e["pg"], "vds": dvs_name, "trunk": _mig_rtext(_mig_ranges(e["vlans"])), "mac_learning": True,
            "unknown_unicast_flooding": True, "forged_transmits": True, "promiscuous": False}
    if not dvs:
        row("port-group", e["pg"], pgp, "BLOCKED", "the reference edge's VDS was not read")
    elif pg:
        gaps = _mig_pg_gaps(pg["view"], e["vlans"])
        if not gaps:
            row("port-group", e["pg"], pgp, "UNCHANGED", "trunk %s, fit for the bridge" % _mig_rtext(pg["view"]["trunk"]))
        elif pg["view"]["description"].startswith(MIG_OWN_PG):
            row("port-group", e["pg"], pgp, "UPDATE", "; ".join(gaps), change=[{"field": "defaultPortConfig", "to": want}],
                rev=pg["view"]["version"])
        else:
            row("port-group", e["pg"], pgp, "BLOCKED", "exists, not made by this tool: %s. Fix it by hand or name "
                "another in %sbridge_trunk_pg_%s" % ("; ".join(gaps), e["pre"], site))
    else:
        row("port-group", e["pg"], pgp, "ADD", "trunk %s, MAC learning, on %s" % (want["trunk"], dvs_name), body=want)
    ref = {"edge": e["template"], "revision": (t or {}).get("_revision")}
    for n in names:
        ed = x["edges"].get(n) or {}
        tn_ = ed.get("tn")
        path = "/transport-nodes/%s" % n
        if not tn_ and (t is None or not ed.get("ip") or not spare):
            row("edge", n, path, "BLOCKED", "not planned: %s" % ("the reference edge is not usable" if t is None else
                                                                  "no address for it" if not ed.get("ip") else "no spare vNIC"))
            continue
        if tn_:
            sws = (tn_.get("host_switch_spec") or {}).get("host_switches") or []
            br = [hs for hs in sws if any(z.get("transport_zone_id") in (x["tz_rid"],) for z in hs.get("transport_zone_endpoints") or [])]
            st_, s_ = _mig_lm(host, H, "/api/v1/transport-nodes/%s/state" % tn_.get("id"))
            state, dstate, msg = _mig_state_text(s_ if st_ == 200 and isinstance(s_, dict) else {})
            ed["state"] = state
            if not x["tz_rid"] or not br:
                row("edge", n, path, "BLOCKED", "exists without the bridge zone %s: %s. Delete it or name another edge"
                    % (e["tz"], "made by this tool" if _mig_owned(tn_) else "not made by this tool"))
            elif state in ("failed", "orphaned") or str(dstate).endswith("FAILED"):
                row("edge", n, path, "BLOCKED", "deployment failed: %s. Delete %s in NSX and run again"
                    % (msg or dstate or state, n))
            else:
                row("edge", n, path, "UNCHANGED", "bridge on %s, %s" % (",".join(hs.get("host_switch_name") or "?" for hs in br),
                                                                     "ready" if state == "success" else "deploying: %s" % (dstate or state)))
            continue
        spec = {"display_name": n, "hostname": ed.get("fqdn"), "form_factor": e["ff"], "reference": ref,
                "management": "%s/%s" % (ed.get("ip"), mnet.network.prefixlen if mnet else "?"),
                "gateway": vdc.get("default_gateway_addresses"),
                "placement": {"vcenter": vc_server, "compute_id": vdc.get("compute_id"), "storage_id": vdc.get("storage_id"),
                              "management_network_id": vdc.get("management_network_id")},
                "bridge": {"switch": MIG_BRIDGE_SWITCH, "vnic": spare, "port_group": e["pg"], "zone": e["tz"],
                           "uplink_profile": e["uplink"]}}
        spec["bridge"]["without"] = list(x.get("drop_switches") or [])
        row("edge", n, path, "ADD", "%s %s, as %s%s, bridge on %s" % (
            spec["management"], e["ff"], e["template"],
            " without %s" % ", ".join(spec["bridge"]["without"]) if spec["bridge"]["without"] else "", spare), body=spec)
    ecs = [q for q in lmread["ecs"] if str(q.get("display_name") or "").lower() == str(e["cluster"] or "").lower()]
    ecp = "/edge-clusters/%s" % e["cluster"]
    x["ec"] = ecs[0] if len(ecs) == 1 else None
    if len(ecs) > 1:
        row("edge-cluster", e["cluster"], ecp, "BLOCKED", "%d edge clusters named %s" % (len(ecs), e["cluster"]))
    elif ecs:
        mem = {m.get("transport_node_id") for m in ecs[0].get("members") or []}
        ids = [((x["edges"].get(n) or {}).get("tn") or {}).get("id") for n in names]
        if all(ids) and set(ids) <= mem:
            row("edge-cluster", e["cluster"], ecp, "UNCHANGED", ", ".join(names))
        elif _mig_owned(ecs[0]):
            row("edge-cluster", e["cluster"], ecp, "UPDATE", "add %s" % ", ".join(
                n for n, i in zip(names, ids) if not i or i not in mem), rev=ecs[0].get("_revision"),
                change=[{"field": "members", "to": names}])
        else:
            row("edge-cluster", e["cluster"], ecp, "BLOCKED", "exists, not made by this tool, without %s"
                % ", ".join(n for n, i in zip(names, ids) if not i or i not in mem))
    elif e["cluster"]:
        row("edge-cluster", e["cluster"], ecp, "ADD", "%s primary, %s backup" % tuple(names) if len(names) == 2 else "",
            body={"display_name": e["cluster"], "members": names})
    # DRS: the pair kept on separate hosts by an anti-affinity rule on their cluster, read from vCenter
    x["drs"] = None
    if x.get("vim") and vdc.get("compute_id") and names:
        d = x["drs"] = mig_drs_read(x["vim"], vdc.get("compute_id"), names)
        rid, dpath = "%s apart" % ", ".join(names), "vc:%s" % (d.get("cluster") or vdc.get("compute_id"))
        deployed = all((x["edges"].get(n) or {}).get("state") == "success" for n in names)
        if d["error"]:
            c("DRS rule", "WARN", "not read from %s: %s. Keep the pair on separate hosts by hand" % (x["vc"], d["error"]))
        elif d["rule"]:
            row("drs-rule", rid, dpath, "UNCHANGED", "%s on %s" % (d["rule"], d["cluster_name"]))
        elif len(d["vms"]) == len(names):
            row("drs-rule", rid, dpath, "ADD", "anti-affinity rule %s on %s" % (MIG_DRS_RULE % e["cluster"], d["cluster_name"]),
                body={"cluster": d["cluster"], "vms": [d["vms"][n.lower()] for n in names]})
        elif deployed:
            row("drs-rule", rid, dpath, "BLOCKED", "%s not in vCenter cluster %s" % (
                ", ".join(n for n in names if n.lower() not in d["vms"]), d["cluster_name"]))
        else:
            row("drs-rule", rid, dpath, "ADD", "anti-affinity rule %s on %s, once the edges are deployed"
                % (MIG_DRS_RULE % e["cluster"], d["cluster_name"]), body={"cluster": d["cluster"], "vms": []})
    # No edge is deployed into a pair that cannot be completed: a blocked zone, trunk or edge blocks
    # the edges and the cluster of that side. The zone and the trunk, harmless alone, are still made.
    blockers = [q for q in rows if q["action"] == "BLOCKED" and q["kind"] not in ("edge-cluster", "drs-rule")]
    for r in rows:
        if blockers and r["kind"] in ("edge", "edge-cluster", "drs-rule") and r["action"] in ("ADD", "UPDATE"):
            r["action"], r["detail"] = "BLOCKED", "not attempted: %s %s is blocked" % (blockers[0]["kind"], blockers[0]["id"])
            r.pop("body", None)
            r.pop("change", None)
    return checks, rows, x


def mig_edge_lm_read(host, H):
    d = {}
    st, v = _mig_lm(host, H, "/api/v1/node/version", timeout=30)
    d["version"] = v.get("product_version") if st == 200 and isinstance(v, dict) else None
    d["status"] = st
    if d["version"]:
        for key, path in (("tns", "/api/v1/transport-nodes?page_size=1000"),
                          ("ecs", "/api/v1/edge-clusters?page_size=1000"), ("tzs", MIG_PTZ),
                          ("hsps", "/api/v1/host-switch-profiles?include_system_owned=true&page_size=1000")):
            d[key], d[key + "_status"] = _mig_lm_list(host, H, path)
    return d


def mig_edge_body(x, spec, pg_moref, tz_rid, users):
    """The /api/v1/transport-nodes body for one new edge: the reference edge with this edge's name,
    address, form factor and credentials, its read-only fields and host pinning removed, RTEP left
    off, SSH on for --verify, and the bridge switch added on the spare vNIC."""
    t = json.loads(json.dumps(x["template"]))
    tn = {k: t[k] for k in ("resource_type", "host_switch_spec", "node_deployment_info", "failure_domain_id") if k in t}
    tn.update(display_name=spec["display_name"], tags=[dict(MIG_OWN)],
              description="fleetparity migpath: migration bridge edge, built as %s" % spec["reference"]["edge"])
    ndi = tn["node_deployment_info"]
    for k in [k for k in ndi if k.startswith("_") or k in ("id", "external_id", "fqdn", "ip_addresses",
                                                              "discovered_ip_addresses", "discovered_node_id",
                                                              "description", "tags")]:
        ndi.pop(k)
    ndi["display_name"] = spec["display_name"]
    dc = ndi.setdefault("deployment_config", {})
    dc["form_factor"] = spec["form_factor"]
    dc["node_user_settings"] = users
    vdc = dc.setdefault("vm_deployment_config", {})
    for k in ("host_id", "resource_allocation"):
        vdc.pop(k, None)
    ip, plen = spec["management"].split("/")
    vdc["management_port_subnets"] = [{"ip_addresses": [ip], "prefix_length": int(plen)}]
    nets = list(vdc.get("data_network_ids") or [])
    i = int(spec["bridge"]["vnic"][-1])
    while len(nets) <= i:
        nets.append(nets[0] if nets else pg_moref)
    nets[i] = pg_moref
    vdc["data_network_ids"] = nets
    ns = ndi.setdefault("node_settings", {})
    ns.update(hostname=spec["hostname"], enable_ssh=True, allow_ssh_root_login=False)
    hss = tn.setdefault("host_switch_spec", {"resource_type": "StandardHostSwitchSpec", "host_switches": []})
    hss["host_switches"] = [{k: v for k, v in hs.items() if k != "host_switch_id" and not k.startswith("_")}
                            for hs in hss.get("host_switches") or []
                            if hs.get("host_switch_name") not in (spec["bridge"].get("without") or [])] + [{
        "host_switch_name": MIG_BRIDGE_SWITCH, "host_switch_mode": "STANDARD", "host_switch_type": "NVDS",
        "host_switch_profile_ids": [{"key": "UplinkHostSwitchProfile", "value": x["uplink_id"]}],
        "pnics": [{"device_name": spec["bridge"]["vnic"], "uplink_name": x["uplink_name"]}],
        "transport_zone_endpoints": [{"transport_zone_id": tz_rid}]}]
    return tn


def mig_bridge_infra_paths(cfg, site, snap, pre="mig_blue_"):
    """The migration's own bridge objects in a Global Manager snapshot, by name: its bridge zone, its
    bridge edge cluster, the two edges named for it and its bridge profile. A change to them is the
    migration's; any other edge added to that cluster is not."""
    names = {str(v).strip().lower() for v in (_mig_key(cfg, pre + "bridge_vlan_tz", site),
                                              _mig_key(cfg, pre + "bridge_edge_cluster", site)) if v}
    edges = {v.lower() for v in _mig_items(_mig_key(cfg, pre + "bridge_edges", site))}
    bpn = str(_mig_key(cfg, pre + "bridge_profile", site) or "bp-migration-%s" % site).strip().lower()
    out = set()
    for p, o in (snap or {}).items():
        n = str((o or {}).get("display_name") or "").strip().lower()
        if "/edge-nodes/" in p:
            if n in edges:
                out.add(p)
        elif ("/transport-zones/" in p or "/edge-clusters/" in p) and n in names:
            out.add(p)
        elif "/edge-bridge-profiles/" in p and n == bpn:
            out.add(p)
    return out


# ---- applying
def _mig_err(b):
    return str((b or {}).get("error_message") or (b or {}).get("_error") or b)[:200] if isinstance(b, dict) else str(b)[:200]


def mig_edges_apply(sides, rows, cfg, users_for, st, outdir):
    """Writes the planned rows, side by side: zone, trunk, edges; then waits for every edge; then the
    clusters. A failure stops what depends on it on that side only."""
    wait_s = int(cfg["mig_edge_deploy_wait"]) if cfg.get("mig_edge_deploy_wait") not in (None, "") else 1800
    poll_s = float(cfg.get("mig_edge_poll_seconds") or 20)
    own = st.setdefault("edges", {})
    waiting = []
    for x in sides:
        side, host, H = x["side"], x["host"], x["H"]
        mine = [r for r in rows if r["side"] == side]
        rec = own.setdefault(side, {"nodes": {}})
        stop = None
        for r in mine:
            if r["kind"] == "edge-cluster":
                continue
            if stop and r["action"] in ("ADD", "UPDATE"):
                r["action"], r["detail"] = "BLOCKED", "not attempted: %s failed" % stop
                continue
            if r["kind"] == "transport-zone" and r["action"] == "ADD":
                st2, b2 = _mig_lm(host, H, r["path"], "PATCH", r["body"])
                r["http"] = st2
                rid, b3 = None, None
                for _ in range(20 if st2 in (200, 201) else 0):
                    st3, b3 = _mig_lm(host, H, r["path"])
                    rid = (b3 or {}).get("realization_id") if st3 == 200 and isinstance(b3, dict) else None
                    if rid:
                        break
                    time.sleep(3)
                if not rid:
                    r["action"], r["detail"] = "ERROR", ("PATCH HTTP %s %s" % (st2, _mig_err(b2)) if st2 not in (200, 201)
                                                         else "created, no realization id after 60 s: run again")
                    stop = "zone %s" % r["id"]
                else:
                    x["tz_rid"], r["rev_after"] = rid, (b3 or {}).get("_revision")
                    rec["zone"] = {"id": r["path"].rsplit("/", 1)[-1], "realization_id": rid, "created": now()}
            elif r["kind"] == "transport-zone" and r["action"] != "UNCHANGED":
                stop = "zone %s" % r["id"]
            elif r["kind"] == "port-group" and r["action"] in ("ADD", "UPDATE"):
                vim = x["vim"]
                if r["action"] == "ADD":
                    spec = ("<spec><name>%s</name><numPorts>8</numPorts>%s<description>%s</description>"
                            "<type>earlyBinding</type><autoExpand>true</autoExpand></spec>" % (
                                xml_escape(x["e"]["pg"]), _mig_pg_port(x["e"]["vlans"]),
                                xml_escape("%s: migration bridge trunk, %s" % (MIG_OWN_PG, side))))
                    res_, err = vim.task("CreateDVPortgroup_Task", x["dvs_type"], x["dvs"], spec)
                else:
                    spec = "<spec><configVersion>%s</configVersion>%s</spec>" % (
                        xml_escape(str(x["pg"]["view"]["version"])), _mig_pg_port(x["e"]["vlans"]))
                    res_, err = vim.task("ReconfigureDVPortgroup_Task", "DistributedVirtualPortgroup", x["pg"]["moref"], spec)
                if err:
                    r["action"], r["detail"], r["http"] = "ERROR", "vCenter: %s" % err, 500
                    stop = "port group %s" % r["id"]
                else:
                    moref = res_ if r["action"] == "ADD" else x["pg"]["moref"]
                    x["pg"] = {"moref": moref, "view": {}}
                    r["http"], r["rev_after"] = 200, None
                    rec["port_group"] = {"name": r["id"], "moref": moref, "vcenter": x["vc"], "vds": x["dvs_name"],
                                         "created": now()}
            elif r["kind"] == "port-group" and r["action"] != "UNCHANGED":
                stop = "port group %s" % r["id"]
            elif r["kind"] == "edge" and r["action"] == "ADD":
                body = mig_edge_body(x, r["body"], x["pg"]["moref"], x["tz_rid"], users_for(side))
                st2, b2 = _mig_lm(host, H, "/api/v1/transport-nodes", "POST", body, timeout=180, retries=0)
                r["http"] = st2
                tid = b2.get("id") if st2 in (200, 201) and isinstance(b2, dict) else None
                if st2 == 0:         # no answer: it may have been created all the same
                    got, _s = _mig_lm_list(host, H, "/api/v1/transport-nodes?page_size=1000")
                    hit = [q for q in got or [] if str(q.get("display_name")).lower() == r["id"].lower()]
                    tid = hit[0].get("id") if len(hit) == 1 else None
                if not tid:
                    r["action"], r["detail"] = "ERROR", "POST HTTP %s %s" % (st2, _mig_err(b2))
                else:
                    x["edges"][r["id"]]["tn"] = {"id": tid, "display_name": r["id"]}
                    r["rev_after"] = (b2 or {}).get("_revision") if isinstance(b2, dict) else None
                    rec["nodes"][r["id"]] = {"id": tid, "created": now()}
                    waiting.append((x, r, tid))
            elif r["kind"] == "edge" and r["action"] == "UNCHANGED" and (x["edges"].get(r["id"]) or {}).get("state") != "success":
                waiting.append((x, r, x["edges"][r["id"]]["tn"]["id"]))
    # every new or still-deploying edge, both sides at once
    t0, seen, ready = time.time(), {}, set()
    pending = list(waiting)
    while pending:
        for item in list(pending):
            x, r, tid = item
            st3, s3 = _mig_lm(x["host"], x["H"], "/api/v1/transport-nodes/%s/state" % tid)
            state, dstate, msg = _mig_state_text(s3 if st3 == 200 and isinstance(s3, dict) else {})
            if state == "success":
                ready.add((x["side"], r["id"]))
                pending.remove(item)
                log("-- %s edge %s ready (%d s)" % (x["side"], r["id"], time.time() - t0))
            elif state in ("failed", "orphaned") or str(dstate).endswith("FAILED"):
                r["action"], r["detail"] = "ERROR", "deployment failed: %s" % (msg or dstate or state)
                pending.remove(item)
            elif seen.get(tid) != (state, dstate):
                seen[tid] = (state, dstate)
                log("-- %s edge %s: %s" % (x["side"], r["id"], dstate or state or "HTTP %s" % st3))
        if not pending:
            break
        if time.time() - t0 > wait_s:
            for x, r, tid in pending:
                r["wait"] = "not ready after %d s" % wait_s
            break
        time.sleep(poll_s)
    for x in sides:
        side = x["side"]
        mine = [r for r in rows if r["side"] == side]
        for r in [r for r in mine if r["kind"] == "edge-cluster" and r["action"] in ("ADD", "UPDATE")]:
            def up(q):        # ready this run, or found ready
                return q["action"] in ("ADD", "UNCHANGED") and ((side, q["id"]) in ready or (
                    q["action"] == "UNCHANGED" and (x["edges"].get(q["id"]) or {}).get("state") == "success"))
            late = [q["id"] for q in mine if q["kind"] == "edge" and not up(q)]
            prior = [q for q in mine if q["action"] in ("ERROR", "BLOCKED") and q["kind"] != "edge-cluster"]
            if prior or late:
                r["action"], r["detail"] = "BLOCKED", ("not attempted: %s %s %s" % (prior[0]["kind"], prior[0]["id"],
                                                                                  prior[0]["action"].lower())
                                                       if prior else "%s not ready: run again to finish" % ", ".join(late))
                continue
            ids = [x["edges"][n]["tn"]["id"] for n in x["e"]["edges"]]
            if r["action"] == "ADD":
                body = {"display_name": x["e"]["cluster"], "tags": [dict(MIG_OWN)],
                        "description": "fleetparity migpath: migration bridge edges",
                        "members": [{"transport_node_id": i} for i in ids]}
                st2, b2 = _mig_lm(x["host"], x["H"], "/api/v1/edge-clusters", "POST", body, retries=0)
            else:
                cur = json.loads(json.dumps(x["ec"]))
                have = {m.get("transport_node_id") for m in cur.get("members") or []}
                cur["members"] = (cur.get("members") or []) + [{"transport_node_id": i} for i in ids if i not in have]
                st2, b2 = _mig_lm(x["host"], x["H"], "/api/v1/edge-clusters/%s" % cur.get("id"), "PUT", cur)
            r["http"] = st2
            if st2 not in (200, 201) or not isinstance(b2, dict):
                r["action"], r["detail"] = "ERROR", "HTTP %s %s" % (st2, _mig_err(b2))
            else:
                r["rev_after"] = b2.get("_revision")
                own[side]["cluster"] = {"name": r["id"], "id": b2.get("id"), "created": now()}
        for r in [r for r in mine if r["kind"] == "drs-rule" and r["action"] == "ADD"]:
            def up(q):
                return q["action"] in ("ADD", "UNCHANGED") and ((side, q["id"]) in ready or (
                    q["action"] == "UNCHANGED" and (x["edges"].get(q["id"]) or {}).get("state") == "success"))
            late = [q["id"] for q in mine if q["kind"] == "edge" and not up(q)]
            prior = [q for q in mine if q["action"] in ("ERROR", "BLOCKED") and q["kind"] not in ("edge-cluster", "drs-rule")]
            if prior or late:
                r["action"], r["detail"] = "BLOCKED", ("not attempted: %s %s %s" % (prior[0]["kind"], prior[0]["id"],
                                                                                  prior[0]["action"].lower())
                                                       if prior else "%s not ready: run again to finish" % ", ".join(late))
                continue
            d = mig_drs_read(x["vim"], r["body"]["cluster"], x["e"]["edges"])       # the VMs exist once deployed
            if d["error"]:
                r["action"], r["detail"], r["http"] = "ERROR", "vCenter: %s" % d["error"], 500
                continue
            if d["rule"]:
                r["action"], r["detail"] = "UNCHANGED", "%s on %s, made since" % (d["rule"], d["cluster_name"])
                continue
            missing = [n for n in x["e"]["edges"] if n.lower() not in d["vms"]]
            if missing:
                r["action"], r["detail"], r["http"] = "ERROR", "%s not in vCenter cluster %s yet: run again" % (
                    ", ".join(missing), d["cluster_name"]), 500
                continue
            vms, rname = [d["vms"][n.lower()] for n in x["e"]["edges"]], MIG_DRS_RULE % x["e"]["cluster"]
            _res, err = x["vim"].task("ReconfigureComputeResource_Task", "ClusterComputeResource", d["cluster"],
                                      mig_drs_spec(rname, vms))
            if err:
                r["action"], r["detail"], r["http"] = "ERROR", "vCenter: %s" % err, 500
            else:
                r["http"], r["rev_after"], r["detail"] = 200, None, "%s on %s: %s" % (rname, d["cluster_name"], ", ".join(vms))
                own[side]["drs_rule"] = {"name": rname, "cluster": d["cluster"], "vms": vms, "vcenter": x["vc"],
                                         "created": now()}
    return rows


def mig_edges_manual(site, rows, sides):
    """The run as calls, for doing it by hand: every body resolved except what only exists after an
    earlier step (shown as <...>), and the passwords."""
    L = ["MANUAL STEPS   %s   bridge edges   %s" % (site, now()), "=" * 74,
         "The calls this run makes, in order. For use only when the tool cannot run. curl prompts for",
         "each password; the edge passwords are yours to fill in.", ""]
    xs = {x["side"]: x for x in sides}
    for n, r in enumerate(rows, 1):
        x = xs.get(r["side"]) or {}
        L.append("%d  %s %s %s   [%s]" % (n, r["side"], r["kind"], r["id"], r["action"]))
        if r["action"] == "UNCHANGED":
            L += ["   already in place: %s" % r["detail"], ""]
            continue
        if r["action"] in ("BLOCKED", "ERROR"):
            L += ["   %s: %s" % (r["action"].lower(), r["detail"]), ""]
            continue
        base = "https://%s" % r["host"]
        if r["kind"] == "transport-zone":
            L += ["   curl -k -u admin -X PATCH -H 'Content-Type: application/json' \\",
                  "     -d '%s' \\" % json.dumps(r["body"], sort_keys=True), "     %s%s" % (base, r["path"])]
        elif r["kind"] == "port-group":
            L += ["   vSphere Client, vCenter %s > VDS %s > New Distributed Port Group:" % (x.get("vc"), x.get("dvs_name")),
                  "     name %s, VLAN type: VLAN trunking %s," % (r["id"], _mig_rtext(_mig_ranges(x["e"]["vlans"]))),
                  "     MAC learning on, allow unicast flooding on, forged transmits Accept, promiscuous Reject"]
        elif r["kind"] == "edge":
            body = mig_edge_body(x, r["body"], (x.get("pg") or {}).get("moref") or "<moref of %s>" % x["e"]["pg"],
                                 x.get("tz_rid") or "<realization_id of %s>" % x["e"]["tz"],
                                 {"cli_username": "admin", "cli_password": "<admin password>",
                                  "root_password": "<root password>"}) if x.get("template") else r["body"]
            L += ["   curl -k -u admin -X POST -H 'Content-Type: application/json' \\",
                  "     -d '%s' \\" % json.dumps(body, sort_keys=True), "     %s/api/v1/transport-nodes" % base,
                  "   then until \"state\" is \"success\": curl -k -u admin %s/api/v1/transport-nodes/<id>/state" % base]
        elif r["kind"] == "edge-cluster":
            L += ["   curl -k -u admin -X POST -H 'Content-Type: application/json' \\",
                  "     -d '%s' \\" % json.dumps({"display_name": r["id"], "members": [
                      {"transport_node_id": "<id of %s>" % m} for m in x["e"]["edges"]]}, sort_keys=True),
                  "     %s/api/v1/edge-clusters" % base]
        elif r["kind"] == "drs-rule":
            L += ["   PowerCLI, vCenter %s:" % x.get("vc"),
                  "     New-DrsRule -Cluster '%s' -Name %s -KeepTogether:$false -VM %s"
                  % ((x.get("drs") or {}).get("cluster_name") or "<cluster>", MIG_DRS_RULE % x["e"]["cluster"], ",".join(x["e"]["edges"]))]
        L.append("")
    return "\n".join(L)


def mig_drs_rule_key(vim, cluster, name):
    """(key, error) of the DRS rule named `name` on a vCenter cluster; key None when it has none."""
    got, err = vim.props("ClusterComputeResource", [cluster], ["configurationEx"])
    if err:
        return None, err
    cfgx = ((got or {}).get(cluster) or {}).get("configurationEx")
    for rule in (cfgx.findall(_V + "rule") if cfgx is not None else []):
        if (rule.findtext(_V + "name") or "") == name:
            return rule.findtext(_V + "key"), None
    return None, None


def _mig_gone_err(e):
    """A vCenter answer that says the object no longer exists."""
    return bool(re.search(r"not found|already been deleted|has been deleted|does not exist", str(e or ""), re.I))


def mig_edge_remove_side(cfg, site, e, H, lmread, vc_login, gm, st):
    """--edges --remove, one side: what --edges and the build made for the bridge, taken apart in the reverse
    order: the bridge profile (once no segment is bridged on it), the edge cluster, the DRS rule, the two edges
    (NSX deletes their VMs), the trunk port group, the bridge zone. Only what this tool made: tagged by it
    (zone, edges, cluster), described by it (port group), named by it (DRS rule), or the bridge profile on
    these edges alone. Anything else is left, said so, and what depends on it stays too. Reads only.
    Returns (checks, rows, ctx). Each row's rank orders the dependencies: a row stays while an earlier rank
    stays."""
    side, host = e["side"], e["lm"]
    checks, rows = [], []
    x = {"side": side, "host": host, "H": H, "e": e, "vim": None, "gm": gm}

    def c(item, state, detail=""):
        checks.append({"area": "edges", "item": "%s %s" % (side, item), "state": state, "detail": str(detail)[:400]})

    def row(kind, id_, path, action, detail="", rank=0, **kw):
        r = {"side": side, "kind": kind, "id": id_, "path": path, "host": host, "action": action, "detail": detail,
             "rank": rank}
        r.update(kw)
        rows.append(r)
        return r

    if not lmread.get("version"):
        c("Local Manager %s" % host, "FAIL", "HTTP %s" % lmread.get("status"))
        return checks, rows, x
    c("Local Manager", "INFO", "%s  NSX %s" % (host, lmread["version"]))
    unread = ["%s (HTTP %s)" % (k, lmread.get(k + "_status")) for k in ("tns", "ecs", "tzs") if lmread.get(k) is None]
    if unread:
        c("fabric read", "FAIL", "not read: %s" % ", ".join(unread))
        return checks, rows, x
    rec = ((st or {}).get("edges") or {}).get(side) or {}
    names = [str(n) for n in e["edges"]]
    low = {n.lower() for n in names}
    tns = {str(t.get("display_name") or "").strip().lower(): t for t in lmread["tns"]
           if (t.get("node_deployment_info") or {}).get("resource_type") == "EdgeNode"}
    mine = {n: tns.get(n.lower()) for n in names}
    full = {}
    for n, t in mine.items():         # each edge whole: where NSX deployed it
        if t is not None:
            st_, f_ = _mig_lm(host, H, "/api/v1/transport-nodes/%s" % t.get("id"))
            full[n] = f_ if st_ == 200 and isinstance(f_, dict) else t

    # 0 the bridge profile, on the Global Manager
    bpn = str(_mig_key(cfg, e["pre"] + "bridge_profile", site) or "bp-migration-%s" % site)
    nodes = {}
    for ec in gm.get("edge_clusters") or []:
        for nd in ec.get("_nodes") or []:
            nodes[_mig_rel(nd.get("path"))] = str(nd.get("display_name") or "")
    bps = _mig_named(gm.get("bridge_profiles") or [], bpn)
    if len(bps) > 1:
        row("bridge-profile", bpn, "-", "BLOCKED", "%d bridge profiles named %s on %s" % (len(bps), bpn, gm["host"]))
    elif bps:
        bpp = _mig_rel(bps[0].get("path")) or "/sites/%s/enforcement-points/default/edge-bridge-profiles/%s" % (
            gm.get("site"), bps[0].get("id"))
        other = sorted({nodes.get(_mig_rel(p_)) or str(p_).rsplit("/", 1)[-1] for p_ in bps[0].get("edge_paths") or []
                        if (nodes.get(_mig_rel(p_)) or "").lower() not in low})
        on = sorted(s_.get("display_name") or s_.get("id") for s_ in gm.get("segments") or []
                    if any(_mig_rel(b_.get("bridge_profile_path")) == bpp for b_ in s_.get("bridge_profiles") or []))
        going = [s_.get("id") for s_ in gm.get("segments_deleting") or []
                 if any(_mig_rel(b_.get("bridge_profile_path")) == bpp for b_ in s_.get("bridge_profiles") or [])]
        if other:
            row("bridge-profile", bpn, bpp, "BLOCKED", "it bridges on %s too, not only this tool's edges: left, and the "
                "edges with it" % ", ".join(other))
        elif on:
            row("bridge-profile", bpn, bpp, "BLOCKED", "%d segment(s) still bridged on it: %s. Take them apart first: "
                "list them in mig_skip_%s, then fp and fp --commit --expect <the digest it prints>" % (
                    len(on), ", ".join(on[:6]) + (" ..." if len(on) > 6 else ""), site))
        elif going:
            row("bridge-profile", bpn, bpp, "BLOCKED", "%d segment(s) NSX is still deleting use it: run again once they "
                "are gone" % len(going))
        else:
            row("bridge-profile", bpn, bpp, "DELETE", "on %s, no segment bridged on it" % gm["host"],
                gm_host=gm["host"], _gm_H=gm["_H"])
    else:
        row("bridge-profile", bpn, "-", "UNCHANGED", "not on %s" % gm["host"])

    # 1 the edge cluster, on the Local Manager
    ecs = [q for q in lmread["ecs"] if str(q.get("display_name") or "").lower() == str(e["cluster"] or "").lower()]
    ids = {str((t or {}).get("id")): n for n, t in mine.items() if t is not None}
    if len(ecs) > 1:
        row("edge-cluster", e["cluster"], "-", "BLOCKED", "%d edge clusters named %s" % (len(ecs), e["cluster"]), rank=1)
    elif ecs:
        ec = ecs[0]
        ecp = "/api/v1/edge-clusters/%s" % ec.get("id")
        members = [str(m.get("transport_node_id")) for m in ec.get("members") or []]
        stran = [m for m in members if m not in ids]
        gec = (_mig_named(gm.get("edge_clusters") or [], e["cluster"]) or [None])[0]
        gecp = _mig_rel((gec or {}).get("path"))
        gws = sorted({p.split("/locale-services/")[0].rsplit("/", 1)[-1] for p, o in (gm.get("snapshot") or {}).items()
                      if "/locale-services/" in p and "/bgp/" not in p and gecp and _mig_rel(o.get("edge_cluster_path")) == gecp})
        if not _mig_owned(ec):
            row("edge-cluster", e["cluster"], ecp, "UNCHANGED", "left: not made by this tool", rank=1, stays=True)
        elif stran:
            row("edge-cluster", e["cluster"], ecp, "BLOCKED", "it holds %d edge(s) this tool did not make: left" % len(stran),
                rank=1)
        elif gws:
            row("edge-cluster", e["cluster"], ecp, "BLOCKED", "it runs %s: left" % ", ".join(gws), rank=1)
        else:
            row("edge-cluster", e["cluster"], ecp, "DELETE", "made by this tool: %s" % (", ".join(
                ids[m] for m in members) or "no member"), rank=1)
    else:
        row("edge-cluster", e["cluster"], "-", "UNCHANGED", "not on %s" % host, rank=1)

    # 2 the DRS rule that keeps the pair apart, in the vCenter NSX deployed them through
    vc_server, vdc0 = None, {}
    for n in names:
        if full.get(n):
            vdc0 = (((full[n].get("node_deployment_info") or {}).get("deployment_config") or {})
                    .get("vm_deployment_config") or {})
            if vdc0.get("vc_id"):
                st_, cm = _mig_lm(host, H, "/api/v1/fabric/compute-managers/%s" % vdc0.get("vc_id"))
                vc_server = cm.get("server") if st_ == 200 and isinstance(cm, dict) else None
                break
    vc_server = vc_server or (rec.get("drs_rule") or {}).get("vcenter") or (rec.get("port_group") or {}).get("vcenter")
    vim = None
    if vc_server:
        vim, err = vc_login(vc_server)
        if err:
            c("vCenter", "WARN", "%s: %s. Its DRS rule and trunk port group are not read" % (vc_server, err))
            vim = None
    x["vim"], x["vc"] = vim, vc_server
    rname = MIG_DRS_RULE % e["cluster"]
    cl = None
    if vim is not None and vdc0.get("compute_id"):
        cl = mig_drs_read(vim, vdc0.get("compute_id"), names).get("cluster")
    cl = cl or (rec.get("drs_rule") or {}).get("cluster")
    if vim is None:
        row("drs-rule", rname, "-", "UNCHANGED", "not read: no vCenter session" if vc_server else "no edge left to find "
            "its vCenter by", rank=2)
    elif not cl:
        row("drs-rule", rname, "-", "UNCHANGED", "no cluster known for the edges", rank=2)
    else:
        key, err = mig_drs_rule_key(vim, cl, rname)
        if err:
            row("drs-rule", rname, "vc:%s" % cl, "ERROR", "%s: %s" % (vc_server, err), rank=2)
        elif key is None:
            row("drs-rule", rname, "vc:%s" % cl, "UNCHANGED", "not on %s" % cl, rank=2)
        else:
            row("drs-rule", rname, "vc:%s" % cl, "DELETE", "on %s, %s" % (vc_server, cl), rank=2, cluster=cl, key=key)

    # 3 the two edges: NSX deletes the VMs it deployed
    for n in names:
        t = mine.get(n)
        if t is None:
            row("edge", n, "-", "UNCHANGED", "not on %s" % host, rank=2)
        elif not _mig_owned(full.get(n) or t):
            row("edge", n, "/api/v1/transport-nodes/%s" % t.get("id"), "UNCHANGED", "left: not made by this tool", rank=2,
                stays=True)
        else:
            row("edge", n, "/api/v1/transport-nodes/%s" % t.get("id"), "DELETE", "made by this tool: NSX deletes its VM too",
                rank=2)

    # 4 the trunk port group, on the VDS of the edges' data vNICs (else where the state says it was made)
    pg = None
    if vim is not None:
        cands = sorted({str(i) for n in names for i in ((((full.get(n) or {}).get("node_deployment_info") or {})
                       .get("deployment_config") or {}).get("vm_deployment_config") or {}).get("data_network_ids") or []
                        if str(i).startswith("dvportgroup-")})
        pgr = rec.get("port_group") or {}
        if pgr.get("moref") and pgr.get("vcenter") in (None, vc_server):
            cands = sorted(set(cands) | {pgr["moref"]})
        got, err = vim.props("DistributedVirtualPortgroup", cands, ["name", "config.description"]) if cands else ({}, None)
        if err and not _mig_gone_err(err):
            row("port-group", e["pg"], "-", "ERROR", "%s: %s" % (vc_server, err), rank=3)
            pg = False
        else:
            if err:                   # one of them is gone: each read on its own
                got = {}
                for m_ in cands:
                    g1, e1 = vim.props("DistributedVirtualPortgroup", [m_], ["name", "config.description"])
                    got.update(g1 or {})
            hit = [(m_, p_) for m_, p_ in (got or {}).items()
                   if (p_.get("name").text if p_.get("name") is not None else "") == e["pg"]]
            pg = hit[0] if hit else None
    if pg is False:
        pass
    elif vim is None:
        row("port-group", e["pg"], "-", "UNCHANGED", "not read: no vCenter session" if vc_server else
            "no edge or record left to find it by", rank=3)
    elif not pg:
        row("port-group", e["pg"], "-", "UNCHANGED", "not on %s" % vc_server, rank=3)
    else:
        desc = pg[1].get("config.description").text if pg[1].get("config.description") is not None else ""
        if not str(desc or "").startswith(MIG_OWN_PG):
            row("port-group", e["pg"], "vc:%s/%s" % (vc_server, pg[0]), "UNCHANGED", "left: not made by this tool", rank=3)
        else:
            row("port-group", e["pg"], "vc:%s/%s" % (vc_server, pg[0]), "DELETE", "made by this tool, on %s" % vc_server,
                rank=3, moref=pg[0])

    # 5 the bridge zone
    tzs = [z for z in lmread["tzs"] if str(z.get("display_name") or "").lower() == str(e["tz"] or "").lower()]
    if len(tzs) > 1:
        row("transport-zone", e["tz"], "-", "BLOCKED", "%d zones named %s" % (len(tzs), e["tz"]), rank=3)
    elif not tzs:
        row("transport-zone", e["tz"], "-", "UNCHANGED", "not on %s" % host, rank=3)
    elif not _mig_owned(tzs[0]):
        row("transport-zone", e["tz"], "%s/%s" % (MIG_PTZ, tzs[0].get("id")), "UNCHANGED", "left: not made by this tool",
            rank=3)
    else:
        row("transport-zone", e["tz"], "%s/%s" % (MIG_PTZ, tzs[0].get("id")), "DELETE", "made by this tool", rank=3)

    # what stays holds what depends on it
    for r in rows:
        if r["action"] != "DELETE":
            continue
        hold = next((q for q in rows if q["rank"] < r["rank"] and (q["action"] in ("BLOCKED", "ERROR") or q.get("stays"))),
                    None)
        if hold:
            r["action"], r["detail"] = "BLOCKED", "stays while %s %s stays" % (hold["kind"], hold["id"])
    return checks, rows, x


def _mig_wait_gone(read, limit, poll):
    """Until read() says 404: None, else why not after `limit` seconds."""
    t0 = time.time()
    while True:
        st_ = read()
        if st_ == 404:
            return None
        if time.time() - t0 > limit:
            return "still there after %ds (HTTP %s): run again" % (limit, st_)
        time.sleep(poll)


def mig_edges_remove_apply(sides, rows, cfg, st):
    """--edges --remove --commit: the planned deletes in their order, each read back until gone. A failure
    holds what depends on it, on that side only. What is gone leaves the state."""
    wait_s = int(cfg["mig_edge_deploy_wait"]) if cfg.get("mig_edge_deploy_wait") not in (None, "") else 1800
    poll_s = float(cfg.get("mig_edge_poll_seconds") or 20)
    del_s = int(cfg.get("mig_delete_wait") or 300)
    own = st.setdefault("edges", {})
    for x in sides:
        side, host, H = x["side"], x["host"], x["H"]
        rec = own.setdefault(side, {"nodes": {}})
        stop = None
        for r in [q for q in rows if q["side"] == side]:
            if r["action"] != "DELETE":
                continue
            if stop and r["rank"] > stop[0]:
                r["action"], r["detail"] = "BLOCKED", "not attempted: %s" % stop[1]
                continue
            err = None
            if r["kind"] == "bridge-profile":
                st2, b2 = gm_delete(r["gm_host"], r["_gm_H"], r["path"])
                r["http"] = st2
                err = ("DELETE HTTP %s %s" % (st2, _mig_err(b2)) if st2 not in (200, 202, 204) else
                       _mig_wait_gone(lambda r=r: gm_get(r["gm_host"], r["_gm_H"], r["path"])[0], del_s, 5))
            elif r["kind"] == "drs-rule":
                _r, e_ = x["vim"].task("ReconfigureComputeResource_Task", "ClusterComputeResource", r["cluster"],
                                       '<spec xsi:type="ClusterConfigSpecEx"><rulesSpec><operation>remove</operation>'
                                       '<removeKey xsi:type="xsd:int">%s</removeKey></rulesSpec></spec><modify>true</modify>'
                                       % xml_escape(str(r["key"])))
                r["http"] = 500 if e_ else 200
                err = "vCenter: %s" % e_ if e_ else None
                if not err:
                    rec.pop("drs_rule", None)
            elif r["kind"] == "port-group":
                t0, left = time.time(), None
                while True:                 # the edge VMs go with their transport nodes; then the port group is free
                    got, e_ = x["vim"].props("DistributedVirtualPortgroup", [r["moref"]], ["vm"])
                    vms_ = ((got or {}).get(r["moref"]) or {}).get("vm")
                    left = [v.text for v in (list(vms_) if vms_ is not None else [])]
                    if e_ or not left or time.time() - t0 > del_s:
                        break
                    time.sleep(10)
                if e_ and not _mig_gone_err(e_):
                    err = "vCenter: %s" % e_
                elif left:
                    err = "%d VM(s) still on it after %ds (%s): run again" % (len(left), del_s, ", ".join(left[:4]))
                elif not e_:
                    _r, e2 = x["vim"].task("Destroy_Task", "DistributedVirtualPortgroup", r["moref"], "")
                    err = "vCenter: %s" % e2 if e2 and not _mig_gone_err(e2) else None
                r["http"] = 500 if err else 200
                if not err:
                    rec.pop("port_group", None)
            else:                           # edge cluster, edge, zone: Local Manager objects
                st2, b2 = _mig_lm(host, H, r["path"], "DELETE", retries=0)
                r["http"] = st2
                limit, poll = (wait_s, poll_s) if r["kind"] == "edge" else (del_s, 5)
                err = ("DELETE HTTP %s %s" % (st2, _mig_err(b2)) if st2 not in (200, 202, 204, 404) else
                       _mig_wait_gone(lambda r=r: _mig_lm(host, H, r["path"])[0], limit, poll))
                if not err:
                    if r["kind"] == "edge":
                        (rec.get("nodes") or {}).pop(r["id"], None)
                    elif r["kind"] == "edge-cluster":
                        rec.pop("cluster", None)
                    else:
                        rec.pop("zone", None)
            if err:
                r["action"], r["detail"] = "ERROR", err
                stop = (r["rank"], "%s %s failed" % (r["kind"], r["id"]))
            else:
                r["detail"] += ", gone"
                log("-- %s %s %s: gone" % (side, r["kind"], r["id"]))
        if any(q["action"] == "DELETE" and q["side"] == side for q in rows):
            rec["removed"] = now()
    return rows


def mig_edges_remove_manual(site, rows):
    """--edges --remove as calls, for doing it by hand."""
    L = ["MANUAL STEPS   %s   bridge edges taken apart   %s" % (site, now()), "=" * 74,
         "The calls this run makes, in order. For use only when the tool cannot run. curl prompts for each password.", ""]
    for n, r in enumerate(rows, 1):
        L.append("%d  %s %s %s   [%s]" % (n, r["side"], r["kind"], r["id"], r["action"]))
        if r["action"] != "DELETE":
            L += ["   %s" % r["detail"], ""]
            continue
        if r["kind"] == "bridge-profile":
            L.append("   curl -k -u admin -X DELETE https://%s/global-manager/api/v1/global-infra%s" % (r["gm_host"], r["path"]))
        elif r["kind"] == "drs-rule":
            L.append("   vSphere Client: cluster %s > Configure > VM/Host Rules > %s > Delete" % (r.get("cluster"), r["id"]))
        elif r["kind"] == "port-group":
            L.append("   vSphere Client: %s > Delete, once no VM is on it" % r["id"])
        else:
            L += ["   curl -k -u admin -X DELETE https://%s%s" % (r["host"], r["path"]),
                  "   then until it answers 404: curl -k -u admin https://%s%s" % (r["host"], r["path"])]
        L.append("")
    return "\n".join(L)


def mig_edges_run(cfg, site, a, ctx, blue, bhost, BH, bsite, st, outdir, lms, green=None):
    """--edges: plan, and with --commit build, the bridge edge pair on each side. --edges --remove: take
    them apart again."""
    rm = bool(getattr(a, "remove", False))
    ctx["scope"] = "edges"
    blue_ok = _mig_blue_writes(cfg, a)
    bw = str(cfg.get("mig_blue_writes") or "").strip().lower()
    checks, rows, sides = [], [], []
    vcs = {}

    for side in ("Green", "Blue"):
        e = mig_edge_cfg(cfg, site, side)
        if side == "Blue" and not blue_ok:
            checks.append({"area": "edges", "item": "Blue bridge edges", "state": "INFO", "detail": (
                "not read or written: Blue writes are for --test runs (mig_blue_writes: test). Run --test --edges"
                if bw == "test" else "not read or written: mig_blue_writes is off")})
            continue
        host, user, pw = lms.get(side) or (None, None, None)
        if not e["lm"] or not host:
            checks.append({"area": "edges", "item": "%s Local Manager" % side, "state": "FAIL", "detail": "set %s" % (
                "nsx_lm_host_%s" % site if side == "Green" else "mig_blue_lm_host_%s" % site)})
            continue
        H = _mig_H(user, pw)
        log("-- %s Local Manager %s (edges, zones, profiles)" % (side, host))

        def vc_login(server, side_=side):
            if server not in vcs:
                vcs[server] = mig_edge_vc(cfg, site, side_, server)
            return vcs[server]
        if rm:
            c_, r_, x = mig_edge_remove_side(cfg, site, e, H, mig_edge_lm_read(host, H), vc_login,
                                             (green if side == "Green" else blue) or {}, st)
        else:
            c_, r_, x = mig_edge_side(cfg, site, e, H, mig_edge_lm_read(host, H), vc_login)
            write_json(outdir, "edges_%s_reference" % side.lower(), x.get("template") or {})
        checks += c_
        rows += r_
        sides.append(x)
    fails = [q for q in checks if q["state"] == "FAIL"]
    mig_print_header(site, (lms.get("Green") or ("-",))[0] or "-", (lms.get("Blue") or ("-",))[0] or "-",
                     "BRIDGE EDGES%s%s  %s" % ("  REMOVE" if rm else "", "  TEST SCOPE" if getattr(a, "test", False) else "",
                                             "COMMIT" if a.commit else "plan only, nothing is written"))
    mig_print_checks(checks)
    pending = [r for r in rows if r["action"] in ("ADD", "UPDATE", "DELETE")]
    items = mig_items(rows)
    digest = mig_digest(rows, (), items)
    ctx["digest"], ctx["items"] = digest, items
    commit = bool(a.commit and not fails)
    stopped = review = None
    if commit and a.expect:
        ok, review = mig_review(ctx["state_path"], a.expect, digest, items)
        if not ok:
            commit, stopped, review = False, review, None
    users = {}
    if commit and any(r["kind"] == "edge" and r["action"] == "ADD" for r in pending):
        euser = cfg.get("nsx_edge_ssh_user") or "admin"
        for side in sorted({r["side"] for r in pending if r["kind"] == "edge"}):
            b_ = side == "Blue"
            rk_ = "mig_blue_edge_root_password" if b_ else "mig_edge_root_password"
            adm = _mig_new_pw("FLEETPARITY_%s" % ("MIG_BLUE_EDGE_PASSWORD" if b_ else "NSX_EDGE_PASSWORD"), cfg,
                              ["mig_blue_edge_password" if b_ else "nsx_edge_password"],
                              "admin password for the new %s edges at %s (%s; --verify signs in with it)"
                              % (side, site, _mig_shown(mig_edge_pw_key(cfg, site, side))))
            root = _mig_new_pw("FLEETPARITY_%s" % ("MIG_BLUE_EDGE_ROOT_PASSWORD" if b_ else "MIG_EDGE_ROOT_PASSWORD"), cfg,
                               [rk_], "root password for the new %s edges at %s (%s)" % (
                                   side, site, _mig_shown("%s_%s" % (rk_, site) if "%s_%s" % (rk_, site) in cfg else rk_)))
            weak = ["admin: %s" % ", ".join(_mig_pw_rule(adm))] if _mig_pw_rule(adm) else []
            weak += ["root: %s" % ", ".join(_mig_pw_rule(root))] if _mig_pw_rule(root) else []
            if weak:
                commit, stopped = False, "the %s edge passwords do not meet NSX's rule (%s): nothing was written" % (
                    side, "; ".join(weak))
                break
            users[side] = {"cli_username": euser, "cli_password": adm, "root_password": root}
    changing = commit and bool(pending)
    ctx["commit"], ctx["changed"] = commit, False
    probes = mig_probes_start(mig_probe_targets(cfg, site, "edges", [], st), ctx) if changing else []
    results = rows
    if changing:
        results = (mig_edges_remove_apply(sides, rows, cfg, st) if rm else
                   mig_edges_apply(sides, rows, cfg, lambda s_: users.get(s_), st, outdir))
        ctx["changed"] = any(r.get("http") in (200, 201, 202, 204) for r in results)
        ctx["wrote"] = mig_wrote(results)
    post = mig_probe_checks(mig_probes_finish(probes, cfg), "edges")
    ctx["probes"] = []
    tally = mig_print_results(results, changing)
    blocked = [r for r in results if r["action"] == "BLOCKED"]
    print("")
    if not pending and not blocked:
        print("  No changes: %s." % ("nothing this tool made for the bridge edges is left" if rm else
                                     "the bridge edges are built as configured"))
    elif not commit and not stopped and pending:
        print("  plan %s: %d change(s)%s, nothing written. To apply exactly these: %s--edges%s --commit --expect %s" % (
            digest, len(pending), " and %d BLOCKED" % len(blocked) if blocked else "",
            "--test " if getattr(a, "test", False) else "", " --remove" if rm else "", digest))
    if review:
        print("  %s" % review)
    if a.commit and fails:
        print("  COMMIT BLOCKED: %d pre-flight FAIL" % len(fails))
    if stopped:
        print("  STOPPED: %s" % stopped)
    waits = [r for r in results if r.get("wait")]
    if waits:
        print("  STILL DEPLOYING: %s. Run the same command again: it waits for them, then forms the cluster"
              % ", ".join("%s %s" % (r["side"], r["id"]) for r in waits))
    leak = []
    if changing and any(r["side"] == "Blue" and r.get("http") for r in results):
        scope = mig_blue_scope(a, cfg, site, blue, {}, [])
        chk, leak = mig_blue_proof(bhost, BH, bsite, blue, scope, outdir,
                                   grow=lambda snap: mig_bridge_infra_paths(cfg, site, snap))
        post.append(chk)
    if post:
        print("")
        print("  AFTER THE CHANGE")
        mig_print_checks(post)
    clean = [{k: v for k, v in r.items() if not k.startswith("_")} for r in results]
    write_json(outdir, "migpath_checks", checks + post)
    write_json(outdir, "migpath_apply" if commit else "migpath_plan",
               {"mode": "edges", "commit": commit, "changed": ctx["changed"], "digest": digest, "site": site,
                "results": clean})
    with open(os.path.join(outdir, "manual_steps.txt"), "w") as fh:
        fh.write(mig_edges_remove_manual(site, results) if rm else mig_edges_manual(site, results, sides))
    for x in sides:
        if x.get("vim"):
            x["vim"].logout()
    if ctx["changed"]:
        S = " --site %s" % a.site if getattr(a, "site", None) else ""
        T = " --test" if getattr(a, "test", False) else ""
        mig_print_undo(ctx, outdir, ["fp%s%s --edges --commit: built again from the reference edges" % (S, T)] if rm else
                       ["fp%s%s --edges --remove --commit: taken apart again, once no segment is bridged on them" % (S, T)])
    print("  evidence: %s" % outdir)
    rc = 1 if (fails or tally["ERROR"] or leak or stopped or waits or (a.commit and blocked)
               or any(p["state"] == "FAIL" for p in post)) else 0
    return 2 if rc == 0 and a.detailed_exitcode and not a.commit and (pending or blocked) else rc


# ---------------------------------------------------------------- migpath: command
# ---------------------------------------------------------------- migpath: moving the VMs (--move)
MIG_VMOTION_LS = "config.vpxd.network.allowVmotionBetweenLogicalSwitches"   # Broadcom KB 322665


def _mig_xt(v):
    return v if str(v).startswith("xsd:") else str(v).split(":")[-1]


def _mig_vim_xml(el, name=None):
    """An element as vCenter returned it, written back in the default (vim25) namespace."""
    tag = name or el.tag.split("}")[-1]
    at = "".join(' xsi:type="%s"' % xml_escape(_mig_xt(v), {'"': "&quot;"}) for k, v in el.attrib.items() if k == _XSI + "type")
    at += "".join(' %s="%s"' % (k, xml_escape(v, {'"': "&quot;"})) for k, v in el.attrib.items() if "}" not in k)
    kids = list(el)
    return "<%s%s>%s</%s>" % (tag, at, "".join(_mig_vim_xml(k) for k in kids) if kids else xml_escape(el.text or ""), tag)


def _mig_thumbprint(host):
    """SHA-1 thumbprint of the certificate a vCenter serves, as vSphere writes it: AA:BB:..."""
    h_, _sep, p_ = host.rpartition(":") if host.count(":") == 1 else (host, "", "443")
    c_ = ssl.create_default_context()
    c_.check_hostname, c_.verify_mode = False, ssl.CERT_NONE
    with socket.create_connection((h_, int(p_ or 443)), timeout=15) as s_:
        with c_.wrap_socket(s_, server_hostname=h_) as t_:
            der = t_.getpeercert(binary_form=True)
    x = hashlib.sha1(der).hexdigest().upper()
    return ":".join(x[i:i + 2] for i in range(0, len(x), 2))


def _mig_vim_session(cfg, site, which):
    """A SOAP session on the vCenter mig_vc() signed in to, with the same credentials."""
    host, _H = mig_vc(cfg, site, which)
    if not host:
        return None, None, "not configured"
    return _mig_vim_host(host)


def _mig_vim_host(host):
    """A SOAP session on a vCenter this run has signed in to (mig_vc, mig_vc_host), same credentials."""
    if host in _MIG_VIM:
        return host, _MIG_VIM[host], None
    user, pw = _MIG_VC_PW.get(host) or (None, None)
    v = MigVim(host)
    err = v.login(user, pw)
    if err:
        return host, None, err
    if not _MIG_VIM:
        atexit.register(_mig_vim_logout)
    _MIG_VIM[host] = v
    return host, v, None


def _mig_vim_logout():
    """At exit: sign out of each SOAP session this run opened."""
    for v in list(_MIG_VIM.values()):
        try:
            v.logout()
        except Exception:
            pass
    _MIG_VIM.clear()


def mig_vc_option(vim, key):
    """(value, error) of one vCenter advanced setting; value None when it is not set."""
    got, err = vim.props("OptionManager", [vim.om], ["setting"])
    if err:
        return None, err
    val = ((got or {}).get(vim.om) or {}).get("setting")
    for o in (list(val) if val is not None else []):
        if o.findtext(_V + "key") == key:
            return (o.findtext(_V + "value") or ""), None
    return None, None


def _mig_host_nets(gv, refs):
    """{network name: [backing XML]} of the networks one host is connected to."""
    out = {}
    dv = [m for t, m in refs if t == "DistributedVirtualPortgroup"]
    if dv:
        got, err = gv.props("DistributedVirtualPortgroup", dv, ["name", "key", "config.distributedVirtualSwitch"])
        if err:
            return None, err
        uu = {}
        for m, p in got.items():
            d = p.get("config.distributedVirtualSwitch")
            if d is None or p.get("name") is None:
                continue
            if d.text not in uu:
                g2, e2 = gv.props(d.get("type") or "VmwareDistributedVirtualSwitch", [d.text], ["uuid"])
                u_ = ((g2 or {}).get(d.text) or {}).get("uuid")
                if e2 or u_ is None:
                    return None, "switch %s: %s" % (d.text, e2 or "no uuid")
                uu[d.text] = u_.text
            key = p["key"].text if p.get("key") is not None else m
            out.setdefault(p["name"].text, []).append(
                '<backing xsi:type="VirtualEthernetCardDistributedVirtualPortBackingInfo"><port><switchUuid>%s</switchUuid>'
                '<portgroupKey>%s</portgroupKey></port></backing>' % (xml_escape(uu[d.text]), xml_escape(key)))
    nw = [m for t, m in refs if t == "Network"]
    if nw:
        got, err = gv.props("Network", nw, ["name"])
        if err:
            return None, err
        for m, p in got.items():
            if p.get("name") is not None:
                out.setdefault(p["name"].text, []).append(
                    '<backing xsi:type="VirtualEthernetCardNetworkBackingInfo"><deviceName>%s</deviceName>'
                    '<network type="Network">%s</network></backing>' % (xml_escape(p["name"].text), xml_escape(m)))
    return out, None


def _mig_nic_net(bv, dev):
    """(network name, error): the network a VM's network adapter is on, from its backing."""
    b = dev.find(_V + "backing")
    t = _mig_xt(b.get(_XSI + "type") or "") if b is not None else ""
    if t == "VirtualEthernetCardDistributedVirtualPortBackingInfo":
        key = b.findtext(_V + "port/" + _V + "portgroupKey")
        got, err = bv.props("DistributedVirtualPortgroup", [key], ["name"])
        n = ((got or {}).get(key) or {}).get("name")
        return (n.text, None) if n is not None else (None, "port group %s: %s" % (key, err or "not found"))
    if t == "VirtualEthernetCardNetworkBackingInfo":
        return b.findtext(_V + "deviceName"), None
    return None, "a %s adapter" % (t or "backing-less")


# ---- which VMs: move_vms and return_vms, read the same way
def _mig_vm_listed(sel, name, r):
    """The selector of `sel` that names VM `name` on row `r`'s segment, else None: a name, a wildcard
    (app*), or segment:<subnet, name or id>."""
    lo_n = str(name).lower()
    for x in sel or []:
        lo = str(x).lower()
        if lo.startswith("segment:"):
            if str(x).split(":", 1)[1].strip() in (r.get("segment"), r.get("subnet"), r.get("name")):
                return x
        elif any(ch in lo for ch in "*?["):
            if fnmatch.fnmatchcase(lo_n, lo):
                return x
        elif lo_n == lo:
            return x
    return None


def _mig_vm_pick(sel, cands, there, rows, why_name, why_wild):
    """The VMs the selectors name, in their order, from `cands` [(name, moref, segment, vCenter)]. A
    selector that names nothing in `cands` and nothing in `there` (names already where the list wants
    them) comes back with the reason. Returns (picked, [(selector, reason)])."""
    picked, seen, miss = [], set(), []
    for x in sel:
        lo = x.lower()
        if lo.startswith("segment:"):
            tgt = x.split(":", 1)[1].strip()
            segs_ = {r["segment"] for r in rows if tgt in (r["segment"], r.get("subnet"), r.get("name"))}
            hits = [t for t in cands if t[2] in segs_]
            why = None if segs_ else "no segment of this scope is %s" % tgt
        elif any(ch in x for ch in "*?["):
            hits = [t for t in cands if fnmatch.fnmatchcase(t[0].lower(), lo)]
            why = None if hits or any(fnmatch.fnmatchcase(d_, lo) for d_ in there) else why_wild
        else:
            hits = [t for t in cands if t[0].lower() == lo]
            why = None if hits or lo in there else why_name
        if why:
            miss.append((x, why))
        for t in hits:
            if t[0].lower() not in seen:
                seen.add(t[0].lower())
                picked.append(t)
    return picked, miss


def mig_vc_landing(vim, vc, H, cl_name, ds_name, ckey, dkey):
    """Where VMs land in one vCenter: the cluster named, else its only one; its root resource pool; its
    datacenter's VM folder; its connected hosts out of maintenance; the datastore named, else the one every
    such host has (vSAN first). ckey, dkey: the config keys that name them. Returns (None, where) or (why
    not, None); the reason starts with "unread: " when vCenter did not answer."""
    st1, cls = http("https://%s/api/vcenter/cluster" % vc, headers=H, timeout=40)
    if st1 != 200 or not isinstance(cls, list):
        return "unread: %s: cluster list not readable (HTTP %s)" % (vc, st1), None
    hit = [x for x in cls if not cl_name or x.get("name") == cl_name]
    if len(hit) != 1:
        return "%s: %s. Set %s to one of: %s" % (
            vc, "no cluster named %s" % cl_name if cl_name and not hit else "%d clusters" % len(hit), ckey,
            ", ".join(sorted(str(x.get("name")) for x in cls)) or "none"), None
    cl, cl_name = hit[0].get("cluster"), hit[0].get("name")
    got, err = vim.props("ClusterComputeResource", [cl], ["resourcePool", "host", "parent"])
    p_ = (got or {}).get(cl) or {}
    pool = p_["resourcePool"].text if p_.get("resourcePool") is not None else None
    par, dc, folder = p_.get("parent"), None, None
    for _i in range(12):                # up through any folders to the datacenter
        if par is None:
            break
        if par.get("type") == "Datacenter":
            dc = par.text
            break
        g_, _e = vim.props(par.get("type") or "Folder", [par.text], ["parent"])
        par = ((g_ or {}).get(par.text) or {}).get("parent")
    if dc:
        g_, _e = vim.props("Datacenter", [dc], ["vmFolder"])
        f_ = ((g_ or {}).get(dc) or {}).get("vmFolder")
        folder = f_.text if f_ is not None else None
    hl = [x.text for x in (p_.get("host") if p_.get("host") is not None else [])]
    g_, err2 = vim.props("HostSystem", hl, ["name", "runtime.connectionState", "runtime.inMaintenanceMode", "network",
                                            "datastore"]) if hl else ({}, None)
    hosts, shared = [], None            # shared: the datastores every connected host of the cluster has
    for h, hp in sorted((g_ or {}).items(), key=lambda kv: kv[1]["name"].text if kv[1].get("name") is not None else kv[0]):
        if (hp.get("runtime.connectionState") is not None and hp["runtime.connectionState"].text == "connected"
                and (hp.get("runtime.inMaintenanceMode") is None or hp["runtime.inMaintenanceMode"].text != "true")):
            nets, dsl = hp.get("network"), hp.get("datastore")
            hosts.append({"moref": h, "name": hp["name"].text if hp.get("name") is not None else h,
                          "refs": [(x.get("type"), x.text) for x in (list(nets) if nets is not None else [])]})
            mine_ = {x.text for x in (list(dsl) if dsl is not None else [])}
            shared = mine_ if shared is None else shared & mine_
    if err or err2 or not pool or not folder:
        return "unread: %s: cluster %s not read whole (%s)" % (
            vc, cl_name, err or err2 or "no resource pool or VM folder"), None
    if not hosts:
        return "%s: no connected host out of maintenance in %s" % (vc, cl_name), None
    gd, err3 = vim.props("Datastore", sorted(shared or []), ["name", "summary.type"]) if shared else ({}, None)
    if err3:
        return "unread: %s: datastores of %s not read: %s" % (vc, cl_name, err3), None
    dsn = {m_: (q_["name"].text if q_.get("name") is not None else m_,
                q_["summary.type"].text if q_.get("summary.type") is not None else "") for m_, q_ in (gd or {}).items()}
    pick = [m_ for m_, (nm_, _t) in dsn.items() if nm_ == ds_name] if ds_name else (
        list(dsn) if len(dsn) == 1 else [m_ for m_, (_n, t_) in dsn.items() if str(t_).lower() == "vsan"])
    if len(pick) != 1:
        return "%s: %s. Set %s to one of: %s" % (
            vc, "no datastore named %s on every host of %s" % (ds_name, cl_name) if ds_name else
            "%d datastores on every host of %s" % (len(dsn), cl_name), dkey,
            ", ".join(sorted(nm_ for nm_, _t in dsn.values())) or "none"), None
    return None, {"cluster": cl, "cluster_name": cl_name, "pool": pool, "folder": folder, "hosts": hosts,
                  "ds": pick[0], "ds_name": dsn[pick[0]][0]}


def _mig_origin(vim, vc, p_, cache):
    """Where a VM is as it leaves, for its way back: vCenter, cluster, host, datastore (of its .vmx), resource
    pool and folder, from its runtime.host, resourcePool, parent and config.files.vmPathName in `p_`."""
    h = p_["runtime.host"].text if p_.get("runtime.host") is not None else None
    if h and h not in cache:
        g_, _e = vim.props("HostSystem", [h], ["name", "parent"])
        hp = (g_ or {}).get(h) or {}
        par, cln = hp.get("parent"), None
        if par is not None and par.get("type") == "ClusterComputeResource":
            g2, _e = vim.props("ClusterComputeResource", [par.text], ["name"])
            c2 = ((g2 or {}).get(par.text) or {}).get("name")
            cln = c2.text if c2 is not None else None
        cache[h] = (hp["name"].text if hp.get("name") is not None else None, cln)
    hname, cln = cache.get(h) or (None, None)
    vmx = p_["config.files.vmPathName"].text if p_.get("config.files.vmPathName") is not None else ""
    ds = re.match(r"\s*\[([^\]]+)\]", vmx or "")
    return {"vc": vc, "cluster": cln, "host": hname, "datastore": ds.group(1) if ds else None,
            "pool": p_["resourcePool"].text if p_.get("resourcePool") is not None else None,
            "folder": p_["parent"].text if p_.get("parent") is not None and p_["parent"].get("type") == "Folder" else None,
            "recorded": now()}


def _mig_folder_path(vim, folder, cache, depth=0):
    """The folder names from the datacenter's VM folder down to `folder`, as vCenter shows them ([] for the VM
    folder itself); None when a folder on the way is not readable."""
    if folder in cache:
        return cache[folder]
    g_, err = vim.props("Folder", [folder], ["name", "parent"])
    p_ = (g_ or {}).get(folder) or {}
    if err or p_.get("parent") is None or p_.get("name") is None or depth > 30:
        cache[folder] = None
    elif p_["parent"].get("type") == "Datacenter":
        cache[folder] = []
    else:
        up = _mig_folder_path(vim, p_["parent"].text, cache, depth + 1)
        cache[folder] = None if up is None else up + [p_["name"].text or ""]
    return cache[folder]


def _mig_vc_unescape(name):
    """A name as vCenter shows it (%2f, %5c, %25) back to what it was typed as: what CreateFolder takes."""
    return re.sub(r"%(2f|5c|25)", lambda m_: {"2f": "/", "5c": "\\", "25": "%"}[m_.group(1).lower()], name, flags=re.I)


def _mig_folder_child(vim, parent, name, cache):
    """(moref of `parent`'s child folder named `name`, error); the children of a folder are read once."""
    if parent not in cache:
        g_, err = vim.props("Folder", [parent], ["childEntity"])
        if err:
            return None, err
        val = ((g_ or {}).get(parent) or {}).get("childEntity")
        kids = [x.text for x in (list(val) if val is not None else []) if x.get("type") == "Folder"]
        named = {}
        if kids:
            g2, err2 = vim.props("Folder", kids, ["name"])
            if err2:
                return None, err2
            named = {q_["name"].text: m_ for m_, q_ in (g2 or {}).items() if q_.get("name") is not None}
        cache[parent] = named
    kids = cache[parent]
    hit = kids.get(name) or next((m_ for n_, m_ in kids.items() if str(n_).lower() == str(name).lower()), None)
    return hit, None


def _mig_folder_resolve(vim, root, path, cache):
    """(moref of the deepest folder of `path` that exists under `root`, the names under it still to create, error)."""
    cur = root
    for i, nm in enumerate(path):
        nxt, err = _mig_folder_child(vim, cur, nm, cache)
        if err:
            return None, None, err
        if not nxt:
            return cur, list(path[i:]), None
        cur = nxt
    return cur, [], None


def _mig_folder_make(vim, root, path, cache):
    """Every folder of `path` under `root`, the missing ones created in order. Returns (moref, error)."""
    cur, rest, err = _mig_folder_resolve(vim, root, path, cache)
    if err:
        return None, err
    for nm in rest:
        r_, err = vim.call("CreateFolder", '<_this type="Folder">%s</_this><name>%s</name>'
                           % (xml_escape(cur), xml_escape(_mig_vc_unescape(nm))))
        if err:                         # made meanwhile (DuplicateName): read the folder's children again
            cache.pop(cur, None)
            nxt, err2 = _mig_folder_child(vim, cur, nm, cache)
            if not nxt:
                return None, "CreateFolder %s: %s" % (nm, err2 or err)
        else:
            nxt = r_.findtext(_V + "returnval")
            cache.setdefault(cur, {})[nm] = nxt
        cur = nxt
    return cur, None


def _mig_relocate_spec(uuid, vc, user, pw, thumb, folder, ds, pool, host, changes):
    """RelocateVM_Task's spec to another vCenter (ServiceLocator), and its priority."""
    return ('<spec><service><instanceUuid>%s</instanceUuid><url>https://%s/sdk</url>'
            '<credential xsi:type="ServiceLocatorNamePassword"><username>%s</username><password>%s</password></credential>'
            '<sslThumbprint>%s</sslThumbprint></service><folder type="Folder">%s</folder>'
            '<datastore type="Datastore">%s</datastore><pool type="ResourcePool">%s</pool><host type="HostSystem">%s</host>'
            '%s</spec><priority>highPriority</priority>') % (
                xml_escape(uuid or ""), xml_escape(vc), xml_escape(user or ""), xml_escape(pw or ""),
                xml_escape(thumb), xml_escape(folder), xml_escape(ds), xml_escape(pool), xml_escape(host), changes)


def _mig_nic_changes(src, dev_list, hn, where):
    """deviceChange for each network adapter of a VM read on `src`: onto the network of the same name
    in `hn` ({name: [backing XML]} of host `where`, where it lands). Returns (XML, names, why not)."""
    nics = [d for d in list(dev_list) if d.find(_V + "macAddress") is not None]
    if not nics:
        return None, [], "no network adapter"
    changes, names = [], []
    for d in nics:
        nm, err = _mig_nic_net(src, d)
        if err:
            return None, names, "network adapter %s: %s" % (d.findtext(_V + "key"), err)
        back = hn.get(nm) or []
        if len(back) != 1:
            return None, names, "%s: %s on %s" % (nm, "no network of that name" if not back else
                                                 "%d networks of that name" % len(back), where)
        t = _mig_xt(d.get(_XSI + "type") or "")
        changes.append('<deviceChange><operation>edit</operation><device xsi:type="%s">%s</device></deviceChange>' % (
            xml_escape(t), "".join(back[0] if k.tag == _V + "backing" else _mig_vim_xml(k) for k in d)))
        names.append(nm)
    return "".join(changes), names, None


def _mig_setting_rows(row, side, host, v_, vc=None):
    """The vMotion-between-segments setting on one vCenter as a plan row."""
    val, err = mig_vc_option(v_, MIG_VMOTION_LS)
    if err:
        row(side, "vcenter-setting", MIG_VMOTION_LS, "vc:%s" % host, "ERROR", "%s: not read: %s" % (host, err), vc=vc)
    elif str(val).strip().lower() == "true":
        row(side, "vcenter-setting", MIG_VMOTION_LS, "vc:%s" % host, "UNCHANGED", "%s: true" % host, vc=vc)
    else:
        row(side, "vcenter-setting", MIG_VMOTION_LS, "vc:%s" % host, "UPDATE",
            "%s: %s -> true (Broadcom KB 322665)" % (host, "not set" if val is None else val), change={"to": "true"}, vc=vc)


def _mig_setting_apply(r, v_):
    """One vCenter's vMotion setting to true, read back. Returns what failed, else None."""
    _r, err = v_.call("UpdateOptions", '<_this type="OptionManager">%s</_this><changedValue><key>%s</key>'
                      '<value xsi:type="xsd:string">true</value></changedValue>' % (xml_escape(v_.om), xml_escape(MIG_VMOTION_LS)))
    val, err2 = mig_vc_option(v_, MIG_VMOTION_LS) if not err else (None, None)
    if err or err2 or str(val).strip().lower() != "true":
        r["action"], r["detail"] = "ERROR", "vCenter: %s" % (err or err2 or "read back %s" % val)
        return "the setting"
    r["detail"] += ", read back"
    return None


def mig_move_plan(cfg, site, res, st, checks, build_pending, only=None, hold=(), taken=0, skip_settings=()):
    """--move: the vCenter setting that allows vMotion between NSX segments, on Blue's and Green's
    vCenter; then one cross vCenter vMotion per VM of the scope still on Blue, each network adapter
    onto the network of the same name on Green, to a connected host of mig_green_cluster_<site> (round
    robin) and mig_green_datastore_<site>. Moves only a built scope whose leaf ports carry the transit
    VLAN and whose bridges this run found active. Where each VM is on Blue is recorded as it leaves, for
    its way back. `hold`: names mig_return_vms_<site> lists, which stay on Blue. `taken`: VMs this run
    returns, counted against move_batch. `skip_settings`: vCenters whose setting row the return plan
    holds. Reads only. Returns (rows, context)."""
    rows, m = [], {"vms": {}, "vim": {}}

    def row(side, kind, id_, path, action, detail="", **kw):
        r = {"side": side, "kind": kind, "id": id_, "path": path, "action": action, "detail": detail, "host": ""}
        r.update(kw)
        rows.append(r)
        return r

    bvc, gvc = _mig_key(cfg, "mig_blue_vc", site), _mig_key(cfg, "mig_green_vc", site)
    vms = []                            # (name, vm, segment, the Blue vCenter it is in)
    for r in res["rows"]:
        for n, v in sorted(((st.get("segments") or {}).get(r["segment"]) or {}).get("vms", {}).items()):
            if v.get("where") == "blue" and v.get("vm"):
                vms.append((n, v["vm"], r["segment"], v.get("vc") or bvc))
    # which VMs: the names listed (move_vms, or --vm), in their order: a name, a wildcard (app*), or
    # segment:<subnet, name or id> for every VM still on Blue there. The rest of the scope stays where it is.
    sel = [x.strip() for v in (only or []) for x in str(v).split(",") if x.strip()]
    hold = {str(x).lower() for x in hold or ()}
    segrow = {r["segment"]: r for r in res["rows"]}
    frm = cfg.get("_list_from") or {}
    if hold:                            # return_vms wins: what it lists stays on Blue
        for n, vm, seg, vc in [t for t in vms if t[0].lower() in hold]:
            if not sel or _mig_vm_listed(sel, n, segrow.get(seg) or {"segment": seg}):
                row("Blue", "vm-move", n, "vc:%s/%s" % (vc, vm), "UNCHANGED", "stays on Blue: mig_return_vms_%s lists "
                    "it too, and wins" % site, segment=seg)
        vms = [t for t in vms if t[0].lower() not in hold]
    if sel:
        done = {n.lower() for s_ in (st.get("segments") or {}).values() for n, v in (s_.get("vms") or {}).items()
                if v.get("where") == "green"}
        vms, miss = _mig_vm_pick(sel, vms, done | hold, res["rows"],
                                 "not on Blue on a built segment of this scope: misspelt, or its segment is not in the scope",
                                 "matches no VM on a built segment of this scope, on Blue or on Green")
        for x, why in miss:
            row("Blue", "vm-move", x, "vm:%s" % x, "BLOCKED", why)
    cl_name, ds_name = _mig_key(cfg, "mig_green_cluster", site), _mig_key(cfg, "mig_green_datastore", site)
    m.update(bvc=bvc, gvc=gvc)
    why = None
    short = [c_["item"] for c_ in checks if "carries the transit VLANs" in c_["item"] and c_["state"] != "PASS"]
    if not bvc or not gvc:
        why = "set mig_blue_vc_%s and mig_green_vc_%s" % (site, site)
    elif build_pending:
        why = "waits for the build (%d change(s) to NSX in this scope): the VMs move on the run after the one that " \
              "commits it" % build_pending
    elif short:
        why = "%s: not yet. A moved VM would lose its gateway" % short[0]
    # each VM's own checks, before it takes a place in the batch: on the segment its wave file names, and its
    # segment bridged on one transit VLAN on both sides, in NSX and on the edges this run (one Active each side)
    brv, want, kept = res.get("bridged_vlans"), cfg.get("_vm_subnet") or {}, []
    for t in vms if not why else []:
        n, vm, seg, vc = t
        r = segrow.get(seg) or {"segment": seg}
        exp, why_ = want.get(n.lower()), None
        gv, bv = (brv.get(seg) or ([], [])) if brv is not None else (None, None)
        bc = [c_ for c_ in checks if " bridge VLAN " in c_["item"] and c_["item"].rsplit(" ", 1)[-1] == str(r.get("vlan"))]
        if exp and not _mig_seg_is(exp[0], r):
            why_ = "%s lists it on %s; it is on %s" % (exp[1], exp[0], r.get("subnet") or r.get("name") or seg)
        elif gv is not None and (not gv or gv != bv or (r.get("vlan") is not None and gv != [r["vlan"]])):
            why_ = "its segment is not bridged on one transit VLAN on both sides: Green %s, Blue %s" % (
                ",".join(str(x) for x in gv) or "none", ",".join(str(x) for x in bv) or "none")
        elif len(bc) < 2 or any(c_["state"] != "PASS" for c_ in bc):
            seen_ = {c_["item"].split(" ", 1)[0]: c_["state"] for c_ in bc}
            why_ = "the bridges on VLAN %s were not found active on both sides this run (%s)" % (
                r.get("vlan"), "; ".join(_mig_bridge_why(checks, sd, seen_.get(sd, "not read"), cfg, site)
                                         for sd in ("Green", "Blue")))
        if why_:
            row("Blue", "vm-move", n, "vc:%s/%s" % (vc, vm), "BLOCKED", why_, segment=seg)
        else:
            kept.append(t)
    if not why:
        vms = kept
    if sel and not why:
        batch = str(_mig_key(cfg, "mig_move_batch", site) or "").strip()
        room = max(int(batch) - int(taken or 0), 0) if batch.isdigit() and int(batch) else None
        if room is not None and len(vms) > room:
            for n, vm, seg, vc in vms[room:]:
                row("Blue", "vm-move", n, "vc:%s/%s" % (vc, vm), "NEXT", "after this run's %s (move_batch %s%s): the same "
                    "command again takes it" % (batch, batch, ", returns first" if taken else ""), segment=seg)
            vms = vms[:room]
    if why:
        for n, vm, seg, vc in vms:
            row("Blue", "vm-move", n, "vc:%s/%s" % (vc, vm), "BLOCKED", why, segment=seg)
        return rows, m
    if not vms:
        return rows, m
    # each Blue vCenter the VMs are in, Green's, and the setting on each
    for side, host in [("Blue", h_) for h_ in sorted({vc for _n, _v, _s, vc in vms})] + [("Green", None)]:
        if side == "Green":
            host, v_, err = _mig_vim_session(cfg, site, "green")
        else:
            if host not in _MIG_VC_PW:
                mig_vc_host(cfg, host)
            host, v_, err = _mig_vim_host(host)
        if err:
            for n, vm, seg, vc in vms:
                row("Blue", "vm-move", n, "vc:%s/%s" % (vc, vm), "ERROR", "%s vCenter %s: %s" % (side, host, err), segment=seg)
            return rows, m
        key = "Green" if side == "Green" else host
        m["vim"][key] = v_
        if key not in set(skip_settings or ()):
            _mig_setting_rows(row, side, host, v_, vc=host)
    gv = m["vim"]["Green"]

    def block(n, vm, seg, detail, act="BLOCKED", vc=None):
        row("Blue", "vm-move", n, "vc:%s/%s" % (vc or bvc, vm), act, detail, segment=seg)

    # where they land: mig_green_cluster_<site> (or the only cluster), mig_green_datastore_<site> (or the shared one)
    _gh, GH = mig_vc(cfg, site, "green")
    land, L = mig_vc_landing(gv, gvc, GH, cl_name, ds_name, "mig_green_cluster_%s" % site, "mig_green_datastore_%s" % site)
    if not land:
        try:
            m["thumb"] = _mig_thumbprint(gvc)
        except (OSError, ssl.SSLError, ValueError) as e:
            land = "%s: certificate not read: %s" % (gvc, e)
    if land:
        for n, vm, seg, vc in vms:
            block(n, vm, seg, land.replace("unread: ", "", 1), "ERROR", vc)
        return rows, m
    hosts, cl_name, ds_name = L["hosts"], L["cluster_name"], L["ds_name"]
    tun = res.get("tunnels") or {}
    sick = [h for h in hosts if (tun.get(_mig_short(h["name"])) or {}).get("ok") is False]
    if sick and len(sick) == len(hosts):
        for n, vm, seg, vc in vms:
            block(n, vm, seg, "no host of %s reaches the Green edges over the overlay (%s: %s). Fix the tunnels first" % (
                cl_name, _mig_short(sick[0]["name"]), tun[_mig_short(sick[0]["name"])]["why"]), vc=vc)
        return rows, m
    hosts = [h for h in hosts if h not in sick]         # only hosts whose VMs reach the edges
    m.update(folder=L["folder"], ds=L["ds"], pool=L["pool"], uuid=gv.uuid)
    netcache, ocache = {}, {}
    # each VM lands in the folder of the same path on Green as on Blue (under the datacenter's VM folder); a
    # folder Green does not have yet is a vc-folder row, made at the commit before the first VM that needs it
    bfc, m["gfc"], first, need = {}, {}, len(rows), {}
    for i, (n, vm, seg, vc) in enumerate(vms):
        h = hosts[i % len(hosts)]
        bv = m["vim"][vc]
        got, err = bv.props("VirtualMachine", [vm], ["config.hardware.device", "runtime.host", "resourcePool", "parent",
                                                     "config.files.vmPathName"])
        p_ = (got or {}).get(vm) or {}
        devs = p_.get("config.hardware.device")
        if err or devs is None:
            block(n, vm, seg, "%s: %s not read: %s" % (vc, vm, err or "no devices"), "ERROR", vc)
            continue
        if h["moref"] not in netcache:
            netcache[h["moref"]] = _mig_host_nets(gv, h["refs"])
        hn, err = netcache[h["moref"]]
        if err:
            block(n, vm, seg, "%s %s networks not read: %s" % (gvc, h["name"], err), "ERROR", vc)
            continue
        changes, names, bad = _mig_nic_changes(bv, devs, hn, h["name"])
        if bad:
            block(n, vm, seg, bad, vc=vc)
            continue
        par_ = p_.get("parent")
        fpath = _mig_folder_path(bv, par_.text, bfc.setdefault(vc, {})) if par_ is not None and \
            par_.get("type") == "Folder" else []
        if fpath is None:
            block(n, vm, seg, "its folder on %s not read: it would land outside it on Green" % vc, "ERROR", vc)
            continue
        gfold, rest, ferr = _mig_folder_resolve(gv, L["folder"], fpath, m["gfc"])
        if ferr:
            block(n, vm, seg, "%s folders not read: %s" % (gvc, ferr), "ERROR", vc)
            continue
        fkey = "/".join(fpath)
        origin = _mig_origin(bv, vc, p_, ocache)
        origin["folder_path"] = fkey or None
        m["vms"][n] = {"vm": vm, "vc": vc, "segment": seg, "host": h["moref"], "host_name": h["name"],
                       "changes": changes, "from": origin, "folder": None if rest else gfold, "folder_path": fpath}
        if rest:
            need[fkey] = fpath
        vl_ = (segrow.get(seg) or {}).get("vlan")
        x_ = _mig_vm_listed(sel, n, segrow.get(seg) or {"segment": seg}) if sel else None
        row("Blue", "vm-move", n, "vc:%s/%s" % (vc, vm), "UPDATE", "from %s to %s %s, %s, %s, bridged on VLAN %s both sides, "
            "folder %s" % (vc, gvc, h["name"], ds_name, ", ".join(names), vl_, fkey or "(the VM folder)"), segment=seg,
            change={"vcenter": gvc, "host": h["name"], "datastore": ds_name, "networks": names, "bridge_vlan": vl_,
                    "folder": fkey},
            wave=frm.get(("mig_move_vms", str(x_).lower())) if x_ else None)
    if need:                            # parents first, ahead of the VMs that land in them
        made = []
        for fkey in sorted(need):
            made.append({"side": "Green", "kind": "vc-folder", "id": fkey, "path": "folder:%s/%s" % (gvc, fkey),
                         "action": "ADD", "detail": "on %s, as on Blue: its VMs land in it" % gvc, "host": "",
                         "change": {"folder": fkey}, "names": need[fkey]})
        rows[first:first] = made
    return rows, m


def mig_move_apply(cfg, site, rows, m, st):
    """The setting on each vCenter, read back; then each VM, one at a time, found on Green after its
    task. The first failure stops the rest. Where it came from goes into the state, for its way back."""
    stop, made = None, {}
    for r in rows:
        if r["action"] not in ("UPDATE", "ADD"):
            continue
        if stop:
            r["action"], r["detail"] = "BLOCKED", "not attempted: %s failed" % stop
            continue
        if r["kind"] == "vcenter-setting":
            stop = _mig_setting_apply(r, m["vim"]["Green"] if r["side"] == "Green" else m["vim"][r.get("vc")])
            continue
        if r["kind"] == "vc-folder":    # the folder as on Blue, every missing level made in order
            f_, err = _mig_folder_make(m["vim"]["Green"], m["folder"], r["names"], m.setdefault("gfc", {}))
            if err:
                r["action"], r["detail"], stop = "ERROR", "vCenter: %s" % err, "the folder %s" % r["id"]
            else:
                made[r["id"]] = f_
                r["detail"] += ", made"
            continue
        if r["action"] != "UPDATE":
            continue
        x = m["vms"][r["id"]]
        folder = x.get("folder") or made.get("/".join(x.get("folder_path") or []))
        if not folder:                  # its folder found or made by now, never the top VM folder by default
            folder, err = _mig_folder_make(m["vim"]["Green"], m["folder"], x.get("folder_path") or [], m.setdefault("gfc", {}))
            if err:
                r["action"], r["detail"], stop = "ERROR", "vCenter: %s" % err, "the folder of %s" % r["id"]
                continue
        user, pw = _MIG_VC_PW.get(m["gvc"]) or (None, None)
        spec = _mig_relocate_spec(m["uuid"], m["gvc"], user, pw, m["thumb"], folder, m["ds"], m["pool"], x["host"],
                                  x["changes"])
        log("-- vMotion %s to %s %s" % (r["id"], m["gvc"], x["host_name"]))
        t0 = time.time()
        _r, err = m["vim"][x["vc"]].task("RelocateVM_Task", "VirtualMachine", x["vm"], spec,
                                        limit=int(cfg.get("mig_move_wait") or 3600))
        if err:
            r["action"], r["detail"], stop = "ERROR", "vCenter: %s" % err, "the vMotion of %s" % r["id"]
            continue
        _gh, GH = mig_vc(cfg, site, "green")
        st_, got = http("https://%s/api/vcenter/vm?names=%s" % (m["gvc"], urllib.parse.quote(r["id"])), headers=GH, timeout=40)
        if st_ != 200 or not isinstance(got, list) or len(got) != 1:
            r["action"], r["detail"], stop = "ERROR", "the task ended but %s is not found once on %s (HTTP %s)" % (
                r["id"], m["gvc"], st_), "the vMotion of %s" % r["id"]
            continue
        rec = ((st["segments"].get(x["segment"]) or {}).get("vms") or {}).get(r["id"])
        if rec is not None:
            rec.update(where="green", on_green_since=now(), moved_by="fleetparity --move")
            if x.get("from"):
                rec["from"] = x["from"]
        r["detail"] += ", %ds, on %s" % (int(time.time() - t0), m["gvc"])
    return rows


# ---------------------------------------------------------------- migpath: VMs back to Blue (return_vms)
def mig_return_plan(cfg, site, res, st, checks, green, blue, sel, blue_writes, blm_host):
    """mig_return_vms_<site>: VMs this tool knows came from Blue, now on Green, moved back by cross vCenter
    vMotion to the Blue vCenter they left, each network adapter onto the network of the same name there.
    They land where they were (recorded as they left), else on mig_blue_cluster_<site> and
    mig_blue_datastore_<site>, else on that vCenter's only cluster and the datastore all its hosts share.
    Where Blue is the gateway, any time; where Green is (cut over), only while both bridges carry the
    segment and this run found them active. Their NSX tags, captured on Blue before they left, go back on
    Blue's Local Manager once its inventory has them: a Blue write, so a VM with tags waits for
    blue_writes. Reads only. Returns (rows, context); context["hold"]: every VM name the list names,
    wherever it is, which the forward move then leaves on Blue."""
    rows = []
    m = {"vms": {}, "vim": {}, "hold": set(), "settings": set(), "tags": {}, "uuid": {}, "thumb": {}}

    def row(side, kind, id_, path, action, detail="", **kw):
        r = {"side": side, "kind": kind, "id": id_, "path": path, "action": action, "detail": detail, "host": ""}
        r.update(kw)
        rows.append(r)
        return r

    bvc, gvc = _mig_key(cfg, "mig_blue_vc", site), _mig_key(cfg, "mig_green_vc", site)
    have = {r["segment"] for r in res.get("rows") or []}
    segrows = list(res.get("rows") or []) + [r for r in res.get("drop") or [] if r["segment"] not in have]
    known = []                          # (name, record, row): every VM the tool saw on Blue on these segments
    for r in segrows:
        for n, v in sorted((((st.get("segments") or {}).get(r["segment"]) or {}).get("vms") or {}).items()):
            known.append((n, v, r))
    m["hold"] = {n.lower() for n, v, r in known if _mig_vm_listed(sel, n, r)}
    cands = [(n, v.get("vm"), r["segment"], (v.get("from") or {}).get("vc") or v.get("vc") or bvc)
             for n, v, r in known if v.get("where") == "green"]
    there = {n.lower() for n, v, r in known if v.get("where") != "green"}
    picked, miss = _mig_vm_pick(sel, cands, there, segrows,
                                "not a VM this tool knows on Green on a segment of this scope: misspelt, or never on Blue here",
                                "matches no VM this tool knows on a segment of this scope, on Green or on Blue")
    for x, why in miss:
        row("Green", "vm-return", x, "vm:%s" % x, "BLOCKED", why)
    batch = str(_mig_key(cfg, "mig_move_batch", site) or "").strip()
    if batch.isdigit() and int(batch) and len(picked) > int(batch):
        for n, _vm, seg, _vc in picked[int(batch):]:
            row("Green", "vm-return", n, "vm:%s" % n, "NEXT", "after this run's %s (move_batch %s): the same command "
                "again takes it" % (batch, batch), segment=seg)
        picked = picked[:int(batch)]
    if not picked:
        return rows, m
    if not gvc:
        for n, _vm, seg, _vc in picked:
            row("Green", "vm-return", n, "vm:%s" % n, "BLOCKED", "set mig_green_vc_%s" % site, segment=seg)
        return rows, m
    rec_of = {n: v for n, v, r in known}
    gseg = {s.get("id"): s for s in green.get("segments") or []}
    bseg = {s.get("id"): s for s in blue.get("segments") or []}
    gbp, bbp = mig_edge_bps(res)
    sub_of = {r["segment"]: r.get("subnet") or r["segment"] for r in segrows}
    vlan_of = {r["segment"]: r.get("vlan") for r in segrows}
    short = [c_["item"] for c_ in checks if "carries the transit VLANs" in c_["item"] and c_["state"] != "PASS"]

    def bridged(o, bp):
        return bool(bp) and any(_mig_rel(e.get("bridge_profile_path")) == bp for e in (o or {}).get("bridge_profiles") or [])

    def gate(sid):                      # does the VM have a gateway on Blue once it is back?
        g, b = gseg.get(sid), bseg.get(sid)
        if not b:
            return "Blue's segment %s is gone (retired): there is no way back for its VMs" % sid
        if g and _mig_conn(g) == "ON":
            if not (bridged(g, gbp) and bridged(b, bbp)):
                return ("Green is its gateway and the bridges are off: on Blue it would have none. fp --cutover %s "
                        "--commit puts the bridges back (Green stays the gateway), or fp --rollback %s --commit"
                        % (sub_of[sid], sub_of[sid]))
            if short:
                return "%s: not yet. On Blue it would not reach Green's gateway" % short[0]
            bc = [c_ for c_ in checks if " bridge VLAN " in c_["item"] and c_["item"].rsplit(" ", 1)[-1] == str(vlan_of.get(sid))]
            if len(bc) < 2 or any(c_["state"] != "PASS" for c_ in bc):
                seen_ = {c_["item"].split(" ", 1)[0]: c_["state"] for c_ in bc}
                return "Green is its gateway and the bridges were not found active on both sides this run (%s)" % (
                    "; ".join(_mig_bridge_why(checks, sd, seen_.get(sd, "not read"), cfg, site) for sd in ("Green", "Blue")))
            return None
        if _mig_conn(b) != "ON":
            return "Connectivity is OFF on Blue and Green is not the gateway: no gateway to return it to"
        return None
    go, want = [], cfg.get("_vm_subnet") or {}
    segrow = {r["segment"]: r for r in segrows}
    frm = cfg.get("_list_from") or {}
    for n, vm, seg, vc in picked:
        tags = rec_of[n].get("tags") or []
        exp = want.get(n.lower())
        why = ("%s lists it on %s; it is on %s" % (exp[1], exp[0], sub_of.get(seg) or seg)
               if exp and not _mig_seg_is(exp[0], segrow.get(seg) or {"segment": seg}) else gate(seg))
        if not why and tags and not blue_writes:
            why = ("its %d NSX tag(s) go back on Blue's Local Manager, a Blue write: set mig_blue_writes_%s, or return it "
                   "by hand and tag it" % (len(tags), site))
        if not why and tags and not blm_host:
            why = "Blue's Local Manager not known (mig_blue_lm_host_%s): its NSX tags could not go back" % site
        if why:
            row("Green", "vm-return", n, "vm:%s" % n, "BLOCKED", why, segment=seg)
        else:
            go.append((n, vm, seg, vc))
    if not go:
        return rows, m
    # Green's vCenter, each Blue vCenter the VMs go back to, and the setting on each
    for side, host in [("Green", None)] + [("Blue", h_) for h_ in sorted({vc for _n, _v, _s, vc in go})]:
        if side == "Green":
            host, v_, err = _mig_vim_session(cfg, site, "green")
        else:
            if host not in _MIG_VC_PW:
                mig_vc_host(cfg, host)
            host, v_, err = _mig_vim_host(host)
        if err:
            for n, _vm, seg, _vc in go:
                row("Green", "vm-return", n, "vm:%s" % n, "ERROR", "%s vCenter %s: %s" % (side, host, err), segment=seg)
            return rows, m
        key = "Green" if side == "Green" else host
        m["vim"][key] = v_
        m["settings"].add(key)
        _mig_setting_rows(row, side, host, v_, vc=host)
    gv = m["vim"]["Green"]
    _gh, GH = mig_vc(cfg, site, "green")
    lands, rr, netcache, fcache = {}, {}, {}, {}
    for n, _vm, seg, vc in go:
        rec, frm_ = rec_of[n], rec_of[n].get("from") or {}
        tags = rec.get("tags") or []

        def no(detail, act="BLOCKED", n=n, seg=seg):
            row("Green", "vm-return", n, "vm:%s" % n, act, detail, segment=seg)
        # the VM on Green, by name: exactly one. None there and one on Blue: it is back already
        st_, got = http("https://%s/api/vcenter/vm?names=%s" % (gvc, urllib.parse.quote(n)), headers=GH, timeout=40)
        if st_ != 200 or not isinstance(got, list):
            no("%s: VM list HTTP %s" % (gvc, st_), "ERROR")
            continue
        _bh, BH = mig_vc_host(cfg, vc)
        if not got:
            st2, got2 = http("https://%s/api/vcenter/vm?names=%s" % (vc, urllib.parse.quote(n)), headers=BH, timeout=40) \
                if BH else (0, None)
            if st2 == 200 and isinstance(got2, list) and len(got2) == 1:
                rec.update(where="blue", vm=got2[0].get("vm"), vc=vc)
                row("Green", "vm-return", n, "vm:%s" % n, "UNCHANGED", "on Blue already, in %s" % vc, segment=seg)
            else:
                no("not found on %s, nor once on %s" % (gvc, vc))
            continue
        if len(got) > 1:
            no("%d VMs named %s on %s: rename one" % (len(got), n, gvc))
            continue
        gvm, bv = got[0].get("vm"), m["vim"][vc]
        if not BH:
            no("%s: %s" % (vc, _MIG_VC_WHY.get(vc) or "no session (sign-in failed)"), "ERROR")
            continue
        # where it lands: where it was, else mig_blue_cluster/_datastore, else the only cluster and the shared datastore
        tries = ([(frm_.get("cluster"), frm_.get("datastore"))] if frm_.get("cluster") and frm_.get("vc") in (None, vc) else [])
        tries.append((_mig_key(cfg, "mig_blue_cluster", site), _mig_key(cfg, "mig_blue_datastore", site)))
        land, L = None, None
        for cl_n, ds_n in tries:
            k_ = (vc, cl_n, ds_n)
            if k_ not in lands:
                lands[k_] = mig_vc_landing(bv, vc, BH, cl_n, ds_n, "mig_blue_cluster_%s" % site, "mig_blue_datastore_%s" % site)
            land, L = lands[k_]
            if not land:
                break
        if land:
            no(land.replace("unread: ", "", 1), "ERROR" if land.startswith("unread: ") else "BLOCKED")
            continue
        if vc not in m["thumb"]:
            try:
                m["thumb"][vc] = _mig_thumbprint(vc)
            except (OSError, ssl.SSLError, ValueError) as e:
                no("%s: certificate not read: %s" % (vc, e), "ERROR")
                continue
        m["uuid"][vc] = bv.uuid
        same = frm_.get("cluster") == L["cluster_name"]
        h = next((x for x in L["hosts"] if same and frm_.get("host") and x["name"] == frm_["host"]), None)
        if h is None:
            i_ = rr.get(vc, 0)
            rr[vc] = i_ + 1
            h = L["hosts"][i_ % len(L["hosts"])]
        pool, folder = L["pool"], L["folder"]
        for typ, mo, k in (("ResourcePool", frm_.get("pool"), "pool"), ("Folder", frm_.get("folder"), "folder")):
            if same and mo:                 # as it was, while that still exists
                g_, e_ = bv.props(typ, [mo], ["name"])
                if not e_ and (g_ or {}).get(mo):
                    if k == "pool":
                        pool = mo
                    else:
                        folder = mo
        got3, err3 = gv.props("VirtualMachine", [gvm], ["config.hardware.device"])
        devs = ((got3 or {}).get(gvm) or {}).get("config.hardware.device")
        if err3 or devs is None:
            no("%s: %s not read: %s" % (gvc, gvm, err3 or "no devices"), "ERROR")
            continue
        if (vc, h["moref"]) not in netcache:
            netcache[(vc, h["moref"])] = _mig_host_nets(bv, h["refs"])
        hn, err = netcache[(vc, h["moref"])]
        if err:
            no("%s %s networks not read: %s" % (vc, h["name"], err), "ERROR")
            continue
        changes, names, bad = _mig_nic_changes(gv, devs, hn, h["name"])
        if bad:
            no(bad)
            continue
        m["vms"][n] = {"gvm": gvm, "vc": vc, "segment": seg, "host": h["moref"], "host_name": h["name"], "pool": pool,
                       "folder": folder, "ds": L["ds"], "changes": changes, "tags": len(tags)}
        if tags:
            m["tags"][n] = {"tags": tags, "segment": seg}
        x_ = _mig_vm_listed(sel, n, segrow.get(seg) or {"segment": seg})
        if same and frm_.get("folder") and folder == frm_["folder"]:     # the folder it left, by its path on Blue
            fp_ = frm_.get("folder_path") or "/".join(_mig_folder_path(bv, folder, fcache.setdefault(vc, {})) or [])
            back_in = fp_ or "(the VM folder)"
        elif same and frm_.get("folder"):
            back_in = "(the VM folder: the one it left, %s, is gone)" % (frm_.get("folder_path") or frm_["folder"])
        else:
            back_in = "(the VM folder)"
        row("Green", "vm-return", n, "vc:%s/%s" % (gvc, gvm), "UPDATE", "from %s to %s %s, %s, %s, folder %s%s%s" % (
            gvc, vc, h["name"], L["ds_name"], ", ".join(names), back_in, "" if same else " (%s)" % (
                "not where it was: %s" % frm_.get("cluster") if frm_.get("cluster") else "where it was is not recorded"),
            "; %d NSX tag(s) back on Blue" % len(tags) if tags else ""), segment=seg,
            change={"vcenter": vc, "host": h["name"], "datastore": L["ds_name"], "networks": names},
            wave=frm.get(("mig_return_vms", str(x_).lower())) if x_ else None)
    return rows, m


def mig_return_apply(cfg, site, rows, m, st):
    """The setting on each vCenter, read back; then each VM back to Blue, one at a time, found there after
    its task. The first failure stops the rest. Its Blue NSX tags are then owed (mig_tags_owed)."""
    stop = None
    for r in rows:
        if r["action"] != "UPDATE":
            continue
        if stop:
            r["action"], r["detail"] = "BLOCKED", "not attempted: %s failed" % stop
            continue
        if r["kind"] == "vcenter-setting":
            stop = _mig_setting_apply(r, m["vim"]["Green"] if r["side"] == "Green" else m["vim"][r.get("vc")])
            continue
        x = m["vms"][r["id"]]
        user, pw = _MIG_VC_PW.get(x["vc"]) or (None, None)
        spec = _mig_relocate_spec(m["uuid"].get(x["vc"]), x["vc"], user, pw, m["thumb"][x["vc"]], x["folder"], x["ds"],
                                  x["pool"], x["host"], x["changes"])
        log("-- vMotion %s back to %s %s" % (r["id"], x["vc"], x["host_name"]))
        t0 = time.time()
        _r, err = m["vim"]["Green"].task("RelocateVM_Task", "VirtualMachine", x["gvm"], spec,
                                        limit=int(cfg.get("mig_move_wait") or 3600))
        if err:
            r["action"], r["detail"], stop = "ERROR", "vCenter: %s" % err, "the vMotion of %s" % r["id"]
            continue
        _bh, BH = mig_vc_host(cfg, x["vc"])
        st_, got = http("https://%s/api/vcenter/vm?names=%s" % (x["vc"], urllib.parse.quote(r["id"])), headers=BH, timeout=40)
        if st_ != 200 or not isinstance(got, list) or len(got) != 1:
            r["action"], r["detail"], stop = "ERROR", "the task ended but %s is not found once on %s (HTTP %s)" % (
                r["id"], x["vc"], st_), "the vMotion of %s" % r["id"]
            continue
        rec = ((st["segments"].get(x["segment"]) or {}).get("vms") or {}).get(r["id"])
        if rec is not None:
            rec.update(where="blue", vm=got[0].get("vm"), vc=x["vc"], on_blue_since=now(), moved_by="fleetparity return_vms")
            for k in ("on_green_since", "tags_placed_ext", "tags_on_green"):
                rec.pop(k, None)            # moved again later, it gets its tags on Green again
            if x.get("tags"):
                rec["tags_back"] = "owed"
        r["detail"] += ", %ds, on %s" % (int(time.time() - t0), x["vc"])
    return rows


def mig_tags_owed(res, st):
    """{vm: {"tags", "segment"}}: VMs returned to Blue whose captured NSX tags are not all back on Blue."""
    out = {}
    for r in list(res.get("rows") or []) + list(res.get("drop") or []):
        for n, v in sorted((((st.get("segments") or {}).get(r["segment"]) or {}).get("vms") or {}).items()):
            if v.get("tags_back") == "owed" and v.get("where") == "blue" and v.get("tags"):
                out[n] = {"tags": v["tags"], "segment": r["segment"]}
    return out


def mig_tags_back(st, rows):
    """VMs whose captured tags are all on Blue again: owed no more."""
    for t in rows or []:
        rec = ((st["segments"].get(t.get("segment")) or {}).get("vms") or {}).get(t["vm"])
        if rec is not None and rec.get("tags_back") == "owed" and (
                t["action"] == "UNCHANGED" or (t["action"] == "ADD" and "read back" in t["detail"])):
            rec["tags_back"] = "on Blue %s" % now()


class _MigTee(object):
    """What the operator saw, kept as console.txt beside the run's evidence. Prompts go to the
    terminal, not here, and no credential is ever printed."""

    def __init__(self, out, path):
        self.out, self.fh = out, open(path, "w")

    def write(self, s):
        self.out.write(s)
        self.fh.write(s)
        return len(s)

    def flush(self):
        self.out.flush()
        self.fh.flush()

    def isatty(self):
        return self.out.isatty()

    def close(self):
        self.fh.close()
        return self.out


def mig_print_header(site, ghost, bhost, mode):
    print("")
    print("=" * 74)
    print(" fleetparity %s  migpath  %s  ->  Green %s  |  Blue %s" % (__version__, site, ghost, bhost))
    print(" mode  : %s" % mode)
    print("=" * 74)


# ---------------------------------------------------------------- migpath: one config, Blue and Green per site
_CFG_V2_NOTES = {
    "blue.gm": "Blue's Global Manager", "green.gm": "Green's active Global Manager",
    "green.router_mac": "--router-mac sets it on every Green Local Manager",
    "green.local_as": "Green's Tier-0 AS as the leaves see it (route check)",
    "green.tier0": "blank: the Tier-0 of the sites' Tier-1s",
    "leaves.vlans": "pool: the leaf lines carry the whole transit range",
    "edges.domain": "DNS domain of the new bridge edges", "edges.deploy_wait": "seconds",
    "moves.batch": "at most this many VMs per --commit; blank: every one listed",
    "moves.wait": "seconds per vMotion", "moves.delete_wait": "seconds",
    "scope": "all, CIDRs, segment names or ids, t1:<Blue Tier-1>", "skip": "never bridged",
    "move_vms": "names, wildcards (app*), segment:<subnet>, or a wave .csv", "move_batch": "overrides moves.batch here",
    "return_vms": "back to Blue, same forms as move_vms; wins over move_vms",
    "cutover_with_blue_vms": "false: a subnet cuts over only once all its VMs are on Green",
    "blue_writes": "false: Green only. true: Blue's bridges too (change window). test: --test runs only",
    "transit_vlans": "one per bridged segment, on this site's leaf pair", "infra_vlans": "on the leaves already: never transit",
    "probes": "production addresses pinged across every change", "test_segments": "what --test acts on: name, id or subnet",
    "blue.location": "Blue's location on its Global Manager", "blue.lm": "blank: found on Blue's Global Manager",
    "blue.vcenter": "the others registered on Blue's Local Manager are read too",
    "blue.vcenter_remote": "blank: the other site's Blue vCenter", "green.lm": "blank: found on Green's Global Manager",
    "green.tier1": "the Tier-1 the migrated segments attach to", "green.vcenter": "where the VMs land",
    "green.cluster": "blank: that vCenter's only cluster", "green.datastore": "blank: the datastore all its hosts share",
    "blue.cluster": "returned VMs with no recorded origin; blank: that vCenter's only cluster",
    "blue.datastore": "blank: the datastore all its hosts share",
    "bridge.edges": "[primary, backup]", "bridge.ips": "or DNS A and PTR records",
    "bridge.template": "blank: an edge in the new edges' management subnet",
    "leaves.ports": "leaf:port facing every host that can run a bridge edge, both leaves",
}
_CFG_V2_BLANK_OK = {"skip", "move_vms", "return_vms", "move_batch", "cutover_with_blue_vms", "test_subnet", "test_blue_tier1", "state_file", "blue.lm",
                    "green.lm", "blue.vcenter_remote", "blue.cluster", "blue.datastore", "green.cluster", "green.datastore",
                    "blue.bridge.template",
                    "green.bridge.template", "blue.bridge.ips", "green.bridge.ips", "blue.bridge.trunk_pg",
                    "green.bridge.trunk_pg", "green.local_as", "leaves.tep", "leaves.user", "leaves.password",
                    "blue.lm_user", "blue.vc_user", "green.lm_user", "green.vc_user"}


def _cfg_scalar(v, in_list=False):
    """One value as YAML that reads back the same, with PyYAML or the minimal reader."""
    if v is None or (v == "" and not in_list):
        return ""                       # blank: not set
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return str(v)
    t = str(v)
    bad = t == "" or t != t.strip() or "#" in t or t[:1] in "'\"[]{}&*!|>%@`" or (in_list and any(ch in t for ch in ",[]"))
    if not bad:
        try:
            import yaml  # type: ignore
            bad = yaml.safe_load(("k: [%s]" if in_list else "k: %s") % t) != {"k": [t] if in_list else t}
        except ImportError:
            pass
        except Exception:
            bad = True
    return "'%s'" % t.replace("'", "''") if bad else t


def _cfg_quoted(v):
    """A password as YAML that reads back exactly, with PyYAML or the minimal reader: in single quotes."""
    return "'%s'" % str(v).replace("'", "''")


def _cfg_v2_lines(tree, order, indent, note_of):
    """YAML for one block of the layout: its keys in the layout's order, a note after each value."""
    out, done = [], set()
    for p_ in order:
        if p_[0] in done or not any(q[0] == p_[0] for q in tree):
            continue
        done.add(p_[0])
        subs = [(q, v) for q, v in tree.items() if q[0] == p_[0]]
        if len(subs) == 1 and len(subs[0][0]) == 1:
            k, v = subs[0][0][0], subs[0][1]
            note = note_of(k, v)
            if isinstance(v, (list, tuple)):
                items = [_cfg_scalar(x, True) for x in v]
                one = "%s%s: [%s]" % (indent, k, ", ".join(items))
                if len(one) > 100:
                    pad, rows, cur = " " * (len(indent) + len(k) + 3), [], ""
                    for i, it in enumerate(items):
                        piece = it + ("," if i < len(items) - 1 else "]")
                        if cur and len(cur) + len(piece) > 96:
                            rows.append(cur.rstrip())
                            cur = ""
                        cur += piece + " "
                    rows.append(cur.rstrip())
                    out += (["%s# %s" % (indent, note)] if note else []) + ["%s%s: [%s" % (indent, k, rows[0])]
                    out += [pad + r_ for r_ in rows[1:]]
                    continue
            else:
                one = ("%s%s: %s" % (indent, k, _cfg_quoted(v) if "password" in k and v not in (None, "")
                                     else _cfg_scalar(v))).rstrip()
            out.append("%-46s # %s" % (one, note) if note else one)
        else:
            out.append("%s%s:" % (indent, p_[0]))
            sub = {q[1:]: v for q, v in subs}
            out += _cfg_v2_lines(sub, [q[1:] for q in order if q[0] == p_[0] and len(q) > 1], indent + "  ",
                                 lambda k_, v_, h_=p_[0]: note_of("%s.%s" % (h_, k_), v_))
    return out


def mig_config_by_site(path):
    """--by-site: the config rewritten once in the layout people read. Above sites: only what serves every
    site (the two Global Managers, how new bridge edges are built, the vMotion pacing). Under sites.<site>:
    everything of that site, what to do there, then its Blue part, its Green part and its leaves, each with
    its own sign-ins (Local Manager, vCenter, bridge edges, leaves). Every password then says which site and
    side it is for, and its line names the system it signs in to. A sign-in kept once for every site is
    copied into each site; a Local Manager password kept under extra: for one host goes to the site whose
    manager it is. Keys the layout has no place for stay under extra:. Every value is read back and compared
    for every site, the Local Manager sign-ins as each run resolves them, before the file is replaced; the
    old file is kept beside it. Passwords are never printed."""
    if not path or not os.path.exists(path):
        sys.exit("config not found: %s" % path)
    old = read_config(path)
    sites = [str(x) for x in _mig_items(old.get("mig_sites"))]
    if not old.get("_v2"):
        for k in sorted(old):
            for root in ("mig_tier1_", "mig_blue_site_", "nsx_lm_host_", "mig_scope_", "mig_blue_lm_host_"):
                if k.startswith(root) and len(k) > len(root) and k[len(root):] not in sites:
                    sites.append(k[len(root):])
    if not sites:
        sys.exit("%s: no site found (mig_sites, or keys ending in _<site>)" % path)
    rev_site = {v: k for k, v in reversed(_CFG_V2_SITE)}
    rev_shared = {v: k for k, v in reversed(_CFG_V2_SHARED)}
    shared, trees, extra, moved, folded = {}, {x: {} for x in sites}, {}, [], []
    for k in sorted(old):
        if k.startswith("_") or k == "mig_sites":
            continue
        v = old[k]
        hit = max([x for x in sites if k.endswith("_" + x) and len(k) > len(x) + 1], key=len, default=None)
        if hit:
            base = k[:-len(hit) - 1]
            if base in rev_site:
                trees[hit][rev_site[base]] = v
            else:
                extra[k] = v
        elif k in _CFG_SITE_SIGNINS and k in rev_site:      # a site's sign-in kept once for every site: into each
            moved.append(".".join(rev_shared.get(k) or rev_site[k]))
            if k == "mig_blue_lm_password" and v in (None, ""):
                continue                # blank once for all reads as absent (the Blue Global Manager's); in a site it asks
            for x in sites:
                trees[x].setdefault(rev_site[k], v)
        elif k in rev_shared:
            shared[rev_shared[k]] = v
        elif k in rev_site:             # a site's setting given once for all: each site gets it, unless it has its own
            for x in sites:
                trees[x].setdefault(rev_site[k], v)
        else:
            extra[k] = v
    lm_of = {str(trees[x].get(("green", "lm")) or "").strip().lower(): x for x in sites if trees[x].get(("green", "lm"))}
    for k in sorted(extra):             # a Local Manager's own password, kept under extra: into its site
        for pre, p_ in (("nsx_admin_password_", ("green", "lm_password")), ("nsx_admin_user_", ("green", "lm_user"))):
            if k.startswith(pre) and k[len(pre):].lower() in lm_of:
                x = lm_of[k[len(pre):].lower()]
                trees[x][p_] = extra.pop(k)
                folded.append("extra.%s -> sites.%s.%s" % (k, x, ".".join(p_)))
                break
    if old.get("_v2") and not moved and not folded:
        print("  %s is already written per site, every sign-in in its site: nothing to do" % path)
        return 0
    for x in sites:                     # every sign-in a site can need is listed in it, blank where not known yet
        for k in _CFG_SITE_SIGNINS:     # (not Blue's Local Manager: listed blank it is asked for, absent it is the GM's)
            p_ = rev_site.get(k)
            if p_ and k != "mig_blue_lm_password" and any(q[0] == p_[0] for q in trees[x]):
                trees[x].setdefault(p_, "")
    name = os.path.basename(path)
    label = {x: str(trees[x].get(("blue", "location")) or x) for x in sites}

    def tv(x, *p):
        return trees[x].get(tuple(p))

    def system_of(x, k):
        """The system a sign-in of site x signs in to, named on its line."""
        if k.startswith("blue.lm"):
            return tv(x, "blue", "lm") or "Blue's Local Manager at %s (found on Blue's Global Manager)" % label[x]
        if k.startswith("blue.vc"):
            v_ = tv(x, "blue", "vcenter")
            return ("%s and the other vCenters on Blue's Local Manager at %s" % (v_, label[x])) if v_ else \
                "Blue's vCenters at %s" % label[x]
        if k.startswith("green.lm"):
            return tv(x, "green", "lm") or "Green's Local Manager at %s (found on Green's Global Manager)" % label[x]
        if k.startswith("green.vc"):
            return tv(x, "green", "vcenter") or "Green's vCenter at %s" % label[x]
        for sd in ("blue", "green"):
            if k.startswith(sd + ".bridge."):
                ed = ", ".join(str(e) for e in _mig_items(tv(x, sd, "bridge", "edges"))) or \
                    "the %s bridge edges at %s" % (sd.capitalize(), label[x])
                return ("root on %s" if "root" in k else "admin on %s") % ed
        if k.startswith("leaves."):
            lv = sorted({str(h).split(".")[0] for h in _mig_items(tv(x, "leaves", "bridge")) + _mig_items(tv(x, "leaves", "route"))})
            return ", ".join(lv) or "the leaves at %s" % label[x]
        return ""

    def note_of(k, v):
        n_ = _CFG_V2_NOTES.get(k) or _CFG_V2_NOTES.get(".".join(k.split(".")[-2:])) or ""
        if "password" in k and v in (None, ""):
            return "blank: asked for"
        return n_

    def shared_note(k, v):
        if k in ("blue.gm_password", "green.gm_password"):
            gm_ = shared.get((k.split(".")[0], "gm")) or ""
            return "%s%s" % (gm_, ". Blank: asked for" if v in (None, "") else "") if gm_ else note_of(k, v)
        return note_of(k, v)

    def site_note(x):
        def f(k, v):
            if "password" in k:
                s_ = system_of(x, k)
                return (s_ + (". Blank: asked for" if v in (None, "") else "")) if s_ else note_of(k, v)
            n_ = note_of(k, v)
            if v in (None, "", []) and k not in _CFG_V2_BLANK_OK:
                n_ = (n_ + " " if n_ else "") + "[set]"
            return n_
        return f
    every = ", ".join(label[x] for x in sites)
    out = ["# %s: fleetparity migpath, every site and both sides in one file." % name,
           "# Blue: the NSX the segments and VMs leave. Green: the NSX they land on. Keep it chmod 600.",
           "#   fp  = python3 fleetparity.py migpath --config %s                 (%s: %s)" % (name, label[sites[0]], sites[0])]
    out += ["#   fp1 = python3 fleetparity.py migpath --config %s --site %s   (%s: %s)" % (name, x, label[x], x)
            for x in sites[1:2]]
    out += ["# Above sites: only what serves every site (%s): the two Global Managers, how new bridge edges" % every,
            "# are built. Under sites.<site>: everything of that site, each with its own sign-ins: what to do",
            "# there, then its Blue, its Green and its leaves. Each password's line names the system it signs in",
            "# to. Blank: asked for, by name. A name the tool does not know stops the run.", "",
            "# " + "=" * 84 + " EVERY SITE (%s)" % every]
    order = [p_ for p_, _k in _CFG_V2_SHARED]
    heads = {"blue": "Blue's Global Manager: one for every site", "green": "Green's Global Manager: one for every site",
             "edges": "how the tool builds new bridge edges, every site", "moves": "vMotion pacing, every site",
             "leaves": "every site's leaves"}
    for sec in ("blue", "green", "edges", "moves", "leaves"):
        part = {p_: v for p_, v in shared.items() if p_[0] == sec}
        if part:
            lines = _cfg_v2_lines(part, [p_ for p_ in order if p_[0] == sec], "", shared_note)
            if lines and lines[0] == "%s:" % sec:
                lines[0] = "%-46s # %s" % (lines[0], heads[sec])
            out += lines + [""]
    out.append("sites:")
    sorder = [p_ for p_, _k in _CFG_V2_SITE]
    for x in sites:
        L = label[x]
        out += ["", "  # " + "=" * 86 + " %s" % L, "%-46s # %s: every value below is for %s only" % ("  %s:" % x, L, L)]
        tops = {p_: v for p_, v in trees[x].items() if len(p_) == 1}
        if tops:
            out.append("    # ---- %s: what to do" % L)
            out += _cfg_v2_lines(tops, [p_ for p_ in sorder if len(p_) == 1], "    ", site_note(x))
        for sec, what in (("blue", "%s Blue: the NSX we leave, and its sign-ins" % L),
                          ("green", "%s Green: the NSX we land on, and its sign-ins" % L),
                          ("leaves", "%s leaves, and their sign-in" % L)):
            part = {p_: v for p_, v in trees[x].items() if p_[0] == sec and len(p_) > 1}
            if part:
                out += ["    # ---- %s" % what]
                out += _cfg_v2_lines(part, [p_ for p_ in sorder if p_[0] == sec], "    ", site_note(x))
    if extra:
        out += ["", "# keys this layout has no place for, read as they are", "extra:"]
        out += ["  %s" % ln for ln in _cfg_v2_lines({(k,): v for k, v in extra.items()}, [(k,) for k in sorted(extra)], "",
                                                       lambda k_, v_: "")]
    text = "\n".join(out).rstrip() + "\n"
    tmp = path + ".by-site"
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as fh:
        fh.write(text)
    os.chmod(tmp, 0o600)
    new = read_config(tmp)

    def eff(cfg, x):                    # what a run at site x reads, the Local Manager sign-ins aside
        d = {k: v for k, v in cfg.items() if not k.startswith("_")}
        for k in list(d):
            if k.endswith("_" + x) and len(k) > len(x) + 1:
                d[k[:-len(x) - 1]] = cfg[k]
        return {k: v for k, v in d.items() if k != "mig_sites" and not any(k.endswith("_" + y) for y in sites)
                and not k.startswith(("nsx_admin_password", "nsx_admin_user"))}
    diffs = []
    for x in sites:
        a_, b_ = eff(old, x), eff(new, x)
        for k in sorted(set(a_) | set(b_)):
            same = a_.get(k) == b_.get(k) or (a_.get(k) in (None, "") and b_.get(k) in (None, ""))
            if not same and not (k == "mig_blue_vc_remote" and a_.get(k) in (None, "")):
                diffs.append("%s: %s %s" % (x, k, "reads differently" if "password" in k else "%r -> %r" % (a_.get(k), b_.get(k))))
        if mig_green_lm_signins(old, x, ask=False) != mig_green_lm_signins(new, x, ask=False):
            diffs.append("%s: a Green Local Manager would be signed in to differently" % x)
        ask_ = ["mig_blue_lm_password_%s" % x in c_ and c_.get("mig_blue_lm_password_%s" % x) in (None, "") for c_ in (old, new)]
        if ask_[0] != ask_[1]:          # listed blank, Blue's Local Manager password is asked for; absent, it is not
            diffs.append("%s: Blue's Local Manager password would %s" % (x, "be asked for" if ask_[1] else "no longer be asked for"))
    if (_mig_items(old.get("mig_sites")) or sites)[0] != _mig_items(new.get("mig_sites"))[0]:
        diffs.append("the default site would change")
    if diffs:
        print("  %s NOT rewritten: %d value(s) would read differently:" % (path, len(diffs)))
        for d_ in diffs[:20]:
            print("    %s" % d_)
        print("  the new layout is in %s (mode 600) for a look; nothing else changed" % tmp)
        return 1
    keep = _cfg_keep(path)
    os.replace(tmp, path)
    os.chmod(path, 0o600)
    print("  %s rewritten per site (%s), mode 600: every value read back the same for every site, the Local "
          "Manager sign-ins included." % (path, ", ".join("%s %s" % (label[x], x) for x in sites)))
    if moved:
        print("  into each site's block, from the top of the file: %s" % ", ".join(sorted(set(moved))))
    for f_ in folded:
        print("  %s" % f_)
    print("  each site's copy is the value the file had for every site: set the ones that differ per site.")
    print("  the old file: %s (mode 600)" % keep)
    return 0


def _cfg_keep(path):
    """A copy of the config before it is replaced, beside it, mode 600; never over an earlier copy."""
    keep, n = "%s.%s" % (path, time.strftime("%Y%m%d-%H%M%S")), 1
    while os.path.exists(keep):
        n += 1
        keep = "%s.%s-%d" % (path, time.strftime("%Y%m%d-%H%M%S"), n)
    shutil.copy2(path, keep)
    os.chmod(keep, 0o600)
    return keep


def _cfg_key_lines(lines):
    """[(line index, (key path), indent)] for every "key:" line of a YAML text, flow lists over several lines
    skipped, so a value can be found by its full name."""
    out, stack, cont = [], [], False
    for i, raw in enumerate(lines):
        body = _cfg_uncomment(raw).rstrip()
        if cont:
            cont = "]" not in body
            continue
        m = re.match(r"^(\s*)([A-Za-z0-9_.@-]+):(\s|$)", body)
        if not m:
            continue
        ind = len(m.group(1))
        while stack and stack[-1][0] >= ind:
            stack.pop()
        path = tuple(k for _i, k in stack) + (m.group(2),)
        out.append((i, path, ind))
        rest = body[m.end():].strip()
        if not rest:
            stack.append((ind, m.group(2)))
        elif rest.startswith("[") and "]" not in rest:
            cont = True
    return out


def mig_config_set(path, setting):
    """--set NAME (asked for, a password twice and never shown) or --set NAME=VALUE: one value of the config
    put in place by its full name, sites.site-b.blue.bridge.admin_password or green.gm_password. Only a
    name the layout knows; the line keeps its note; every other value is read back unchanged and this one
    as given before the file is replaced (the old one kept beside it, mode 600)."""
    import difflib
    if not path or not os.path.exists(path):
        sys.exit("config not found: %s" % path)
    name, _eq, given = str(setting).partition("=")
    name = name.strip()
    parts = tuple(name.split("."))
    old = read_config(path)
    if not old.get("_v2"):
        sys.exit("%s is not written per site: run fp --by-site first, then --set" % path)
    sites = [str(x) for x in _mig_items(old.get("mig_sites"))]
    if parts[:1] == ("sites",) and len(parts) > 2 and parts[1] in sites and parts[2:] in _CFG_V2_SITE_MAP:
        flat = "%s_%s" % (_CFG_V2_SITE_MAP[parts[2:]], parts[1])
    elif parts in _CFG_V2_SHARED_MAP:
        flat = _CFG_V2_SHARED_MAP[parts]
    else:
        near = difflib.get_close_matches(name, ["sites.%s.%s" % (x, ".".join(p_)) for x in sites for p_ in _CFG_V2_SITE_MAP]
                                         + [".".join(p_) for p_ in _CFG_V2_SHARED_MAP], 1)
        sys.exit("%s: not a name in %s%s" % (name, path, " (did you mean %s?)" % near[0] if near else ""))
    secret_ = "password" in parts[-1]
    if not _eq:
        if DRY:
            sys.exit("--set %s: give it as %s=VALUE in a dry run" % (name, name))
        if secret_:
            v1 = getpass.getpass("      %s (not shown): " % name)
            if v1 != getpass.getpass("      %s, again: " % name):
                sys.exit("the two did not match: nothing changed")
            given = v1
        else:
            given = input("      %s: " % name)
    lines = open(path).read().split("\n")
    keys = _cfg_key_lines(lines)
    hit = [(i, ind) for i, p_, ind in keys if p_ == parts]
    val = (_cfg_quoted(given) if secret_ else _cfg_scalar(given)) if given != "" else ""
    if hit:
        i, ind = hit[0]
        raw = lines[i]
        body = _cfg_uncomment(raw).rstrip()
        note = raw[len(body):].strip()
        note = re.sub(r"\.?\s*Blank: asked for\s*$", "", note) if given else note
        note = "" if note in ("#", "# blank: asked for") and given else note
        one = ("%s%s: %s" % (" " * ind, parts[-1], val)).rstrip()
        lines[i] = "%-46s %s" % (one, note) if note else one
    else:                               # not written yet: under its block, which must be there
        par = [(i, ind) for i, p_, ind in keys if p_ == parts[:-1]]
        if not par:
            sys.exit("%s: its block %s is not in %s: run fp --by-site first" % (name, ".".join(parts[:-1]), path))
        i, ind = par[0]
        kids = [j for j, p_, _d in keys if p_[:len(parts) - 1] == parts[:-1] and len(p_) >= len(parts)]
        at = (max(kids) if kids else i) + 1
        while at < len(lines) and lines[at].strip() and len(lines[at]) - len(lines[at].lstrip()) > ind + 2:
            at += 1                     # past a flow list's continuation lines
        lines.insert(at, ("%s%s: %s" % (" " * (ind + 2), parts[-1], val)).rstrip())
    tmp = path + ".set"
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as fh:
        fh.write("\n".join(lines))
    os.chmod(tmp, 0o600)
    new = read_config(tmp)
    bad = [k for k in sorted(set(old) | set(new)) if not k.startswith("_") and k != flat
           and not (old.get(k) == new.get(k) or (old.get(k) in (None, "") and new.get(k) in (None, "")))]
    got = new.get(flat)
    want_ok = ("" if got is None else str(got)) == given if secret_ else flat in new
    if bad or not want_ok:
        os.remove(tmp)
        sys.exit("%s NOT changed: %s" % (path, "it would read back differently" if not want_ok else
                                         "other values would change too: %s" % ", ".join(bad[:5])))
    keep = _cfg_keep(path)
    os.replace(tmp, path)
    os.chmod(path, 0o600)
    print("  %s set in %s%s; it reads back as given, nothing else changed (mode 600). The old file: %s" % (
        name, path, "" if secret_ else " to %s" % val, keep))
    return 0


_MIG_SHOWN_SITES = []        # with site blocks in the config: a site's key is shown as it is written there
_MIG_SHOWN = {"v2": False, "site": None}


def _mig_shown(text):
    """A key named the way the config is written: sites.site-a.scope for mig_scope_site-a, blue.vc_user
    for mig_blue_vc_user (with blocks of flat keys: site-a.mig_scope). File names are left alone."""
    text = str(text)
    if _MIG_SHOWN["v2"]:
        rev_site = {v: ".".join(k) for k, v in reversed(_CFG_V2_SITE)}
        rev_shared = {v: ".".join(k) for k, v in reversed(_CFG_V2_SHARED)}
        for site in _MIG_SHOWN_SITES:
            text = re.sub(r"\b([a-z][a-z0-9_]*[a-z0-9])_%s\b(?![.\w-])" % re.escape(site),
                          lambda m_, s_=site: ("sites.%s.%s" % (s_, rev_site[m_.group(1)])) if m_.group(1) in rev_site
                          else m_.group(0), text)

        def plain(m_):
            k = m_.group(1)
            if k in _CFG_SITE_SIGNINS and k in rev_site and _MIG_SHOWN["site"] and _MIG_SHOWN.get("signins_per_site"):
                return "sites.%s.%s" % (_MIG_SHOWN["site"], rev_site[k])
            if k in rev_shared:
                return rev_shared[k]
            if k in rev_site and _MIG_SHOWN["site"]:
                return "sites.%s.%s" % (_MIG_SHOWN["site"], rev_site[k])
            return k
        return re.sub(r"\b((?:mig|nsx|fed_ns|leaf)_[a-z0-9_]*[a-z0-9])\b(?![.\w-])", plain, text)
    for site in _MIG_SHOWN_SITES:
        text = re.sub(r"\b([a-z][a-z0-9_]*[a-z0-9])_%s\b(?![.\w-])" % re.escape(site),
                      lambda m_, s_=site: "%s.%s" % (s_, m_.group(1)), text)
    return text


def mig_print_checks(checks):
    order = {"FAIL": 0, "WARN": 1, "SKIP": 2, "INFO": 3, "PASS": 4}
    for x in sorted(checks, key=lambda x: order.get(x["state"], 5)):
        d, item = _mig_shown(x["detail"]), _mig_shown(x["item"])
        if x["state"] in ("FAIL", "WARN") and len(d) > 110:     # the reason is the point of the line: all of it
            import textwrap
            lines = textwrap.wrap(d, 110) or [""]
            print("  [%-4s] %-52s %s" % (x["state"], item[:52], lines[0]))
            for ln in lines[1:]:
                print("  %-59s %s" % ("", ln))
        else:
            print("  [%-4s] %-52s %s" % (x["state"], item[:52], d[:110]))


def mig_print_results(results, commit):
    print("")
    import textwrap
    for r in results:
        d = _mig_shown(r["detail"])
        lines = (textwrap.wrap(d, 90) or [""]) if r["action"] in ("ERROR", "BLOCKED") or r.get("kind") in (
            "vm-move", "vm-return", "vc-folder") else [d[:110]]
        print("  [%-9s] %-5s %-14s %-34s %s" % (r["action"], r["side"], r["kind"], r["id"][:34], lines[0]))
        for ln in lines[1:]:
            print("  %-68s %s" % ("", ln))
    tally = collections.Counter(r["action"] for r in results)
    print("")
    print("  ADD %d  UPDATE %d  DELETE %d  UNCHANGED %d  BLOCKED %d  ERROR %d%s%s" % (
        tally["ADD"], tally["UPDATE"], tally["DELETE"], tally["UNCHANGED"], tally["BLOCKED"], tally["ERROR"],
        "  HELD %d" % tally["HELD"] if tally["HELD"] else "", "" if commit else "   (nothing written)"))
    return tally


def mig_print_state(st, res, path):
    rows = res.get("rows") or []
    if not rows:
        return
    print("")
    print("  STATE   %s" % path)
    for r in rows:
        s_ = st["segments"].get(r["segment"]) or {}
        h = (s_.get("history") or [None])[-1]
        vms = s_.get("vms") or {}
        print("  %-18s %-26s %-10s VMs known %d, on Green %d   last: %s" % (
            r["subnet"] or "-", r["segment"][:26], s_.get("status", "planned"), len(vms),
            sum(1 for v in vms.values() if v.get("where") == "green"),
            "%s %s %s" % (h["action"], h["result"], h["ts"]) if h else "none"))


MIG_REPORT_SEGMENTS = ("site", "segment", "name", "subnet", "gateway", "blue_tier1", "source", "path", "at_site", "in_scope",
                       "transit_vlan", "status", "vms_on_blue", "vms_on_green", "nsx_vm_ports", "notes")
MIG_REPORT_VMS = ("site", "vm", "where", "vcenter", "listed_to_move", "listed_to_return", "wave", "segment", "segment_name", "subnet",
                  "ip", "power_state", "on_green_since", "came_from")


def mig_reports(cfg, site, rows, st, beside, outdir):
    """Two CSVs to read in Excel, written by the tool and never read back: every Blue segment (in the
    scope or not: path, transit VLAN, status, VM counts) and every VM captured on the scope's segments
    (where it is, its address, whether mig_move_vms or mig_return_vms lists it, where it came from on Blue).
    Rewritten beside the state only when their content changes; a copy goes into each run's evidence."""
    sels = [str(x).strip() for x in _mig_items(_mig_key(cfg, "mig_move_vms", site)) if str(x).strip()]
    rets = [str(x).strip() for x in _mig_items(_mig_key(cfg, "mig_return_vms", site)) if str(x).strip()]
    frm = cfg.get("_list_from") or {}
    segs, vms_ = [], []

    def order(r):
        n = r.get("net")
        return (not r.get("scope"), not r.get("at_site"), n is None, n.version if n is not None else 0,
                int(n.network_address) if n is not None else 0, r["segment"])
    for r in sorted(rows or [], key=order):
        s_ = st["segments"].get(r["segment"]) or {}
        vms = s_.get("vms") or {}
        segs.append({"site": site, "segment": r["segment"], "name": r.get("name") or "", "subnet": r.get("subnet") or "",
                     "gateway": r.get("gateway") or "", "blue_tier1": r.get("blue_tier1") or "",
                     "source": r.get("source") or "", "path": r.get("path") or "",
                     "at_site": "yes" if r.get("at_site") else "", "in_scope": "yes" if r.get("scope") else "",
                     "transit_vlan": r.get("transit_vlan") or "",
                     "status": s_.get("status") or ("skipped" if r.get("path") == "SKIP" else "planned" if r.get("scope") else ""),
                     "vms_on_blue": sum(1 for v in vms.values() if v.get("where") == "blue") if vms else "",
                     "vms_on_green": sum(1 for v in vms.values() if v.get("where") == "green") if vms else "",
                     "nsx_vm_ports": r.get("nsx_vm_ports", ""), "notes": r.get("notes") or ""})
        for n, v in sorted(vms.items()):
            back, fwd = _mig_vm_listed(rets, n, r), _mig_vm_listed(sels, n, r)
            came = v.get("from") or {}
            vms_.append({"site": site, "vm": n, "where": v.get("where") or "", "vcenter": v.get("vc") or "",
                         "listed_to_move": "yes" if fwd and not back else "",
                         "listed_to_return": "yes" if back else "",
                         "wave": (frm.get(("mig_return_vms", back.lower())) if back else
                                  frm.get(("mig_move_vms", fwd.lower())) if fwd else "") or "",
                         "segment": r["segment"], "segment_name": r.get("name") or "", "subnet": r.get("subnet") or "",
                         "ip": v.get("ip") or "", "power_state": v.get("power_state") or "",
                         "on_green_since": v.get("on_green_since") or "",
                         "came_from": " / ".join(str(came[k]) for k in ("vc", "cluster", "host", "datastore", "folder_path")
                                                 if came.get(k))})
    out = []
    for fn, cols, data in (("migpath_segments_%s.csv" % site, MIG_REPORT_SEGMENTS, segs),
                           ("migpath_vms_%s.csv" % site, MIG_REPORT_VMS, vms_)):
        buf = io.StringIO()
        w = csv.DictWriter(buf, fieldnames=list(cols))
        w.writeheader()
        w.writerows(data)
        text, path = buf.getvalue(), os.path.join(beside, fn)
        old = None
        if os.path.exists(path):
            with open(path, newline="") as fh:
                old = fh.read()
        if old != text:
            tmp = path + ".tmp"
            with open(tmp, "w", newline="") as fh:
                fh.write(text)
            os.replace(tmp, path)
        if outdir:
            shutil.copy2(path, os.path.join(outdir, fn))
        out.append(path)
    return out


def mig_legacy_plan(path, site, rows):
    """The plan CSV of 1.14.0 and earlier is no longer read for planning. Checked only so that a SKIP or
    READDRESS decision in it is not lost: one the config does not carry is listed until it does."""
    old = mig_plan_raw(path)
    if not old:
        return []
    skipped = {r["segment"] for r in rows or [] if r.get("path") == "SKIP"}
    lost = sorted(r["segment"] for r in old if (r.get("site") or site) == site and r.get("segment")
                  and (r.get("path") or "").upper() in ("SKIP", "READDRESS") and r["segment"] not in skipped)
    if not lost:
        return []
    return [{"area": "plan", "item": "decisions in %s" % os.path.basename(path), "state": "WARN",
             "detail": "no longer read; it marks %d segment(s) SKIP or READDRESS that mig_skip_%s does not list: %s. "
                       "Add them to mig_skip_%s, or delete the file" % (len(lost), site, ", ".join(lost[:8]), site)}]


def mig_blue_proof(bhost, BH, bsite, blue, scope, outdir, grow=None):
    """After a commit: re-read Blue. Anything changed outside the run's scope fails the run. `grow`
    names objects the run created, found in the re-read by name (their ids are NSX's)."""
    log("-- Blue re-read: did anything change outside this run's scope?")
    after = mig_snapshot(bhost, BH, mig_side(bhost, BH, bsite.get("id")))
    if grow:
        scope = set(scope) | grow(after)
    imp = mig_impact(_mig_norm(blue["snapshot"]), _mig_norm(after), scope)
    write_json(outdir, "blue_impact", imp)
    leak = imp["out_of_scope"]
    touched = imp["changed"] + imp["added"] + imp["removed"]
    print("")
    print("  %s" % ("BLUE CHANGED OUTSIDE THIS RUN'S SCOPE: %s   (blue_impact.json)" % ", ".join(leak) if leak else
                    "Blue: %d object%s changed, all in scope%s" % (len(touched), "" if len(touched) == 1 else "s",
                    (": " + ", ".join(p.rsplit("/", 1)[-1] for p in touched)) if touched else "")))
    return {"area": "impact", "item": "Blue changed only within this run's scope", "state": "FAIL" if leak else "PASS",
            "detail": ("outside the scope: %s" % ", ".join(leak)) if leak else
                      ("%d in scope: %s" % (len(touched), ", ".join(p.rsplit("/", 1)[-1] for p in touched))
                       if touched else "nothing changed on Blue")}, leak


def mig_baseline(st, key, outdir, bsite, bhost, blue, balarms):
    st["baselines"][key] = {"taken": now(), "evidence": os.path.abspath(outdir), "site": bsite.get("id"), "host": bhost,
                            "objects": _mig_norm(blue["snapshot"]), "alarms": _mig_norm(balarms)}
    return {"area": "impact", "item": "baseline for %s" % key, "state": "INFO",
            "detail": "recorded this run: %d Blue objects and the open alarms; --impact compares with it"
                      % len(blue["snapshot"])}


def mig_setup_run(cfg, site, a, ctx, green, blue, bhost, BH, bsite, balarms, st, outdir, users, blm=(None, None, None)):
    """--test --setup: create the Blue test segment and prove nothing else on Blue changed. The next
    --test run finds it on Blue and gives it a transit VLAN. Plans first; writes only what is missing.
    --test --setup --remove: delete it again, once nothing of the test is on it."""
    rm = bool(getattr(a, "remove", False))
    checks, objs = mig_setup_remove(cfg, site, green, blue, blm) if rm else mig_setup(cfg, site, green, blue)
    ctx["scope"] = "test"
    if "test" not in st["baselines"]:
        checks.append(mig_baseline(st, "test", outdir, bsite, bhost, blue, balarms))
    if not _mig_blue_writes(cfg, a):
        for o in objs:
            o["needs"] = o.get("needs") or "Blue writes disabled (mig_blue_writes): %s %s on Blue by hand" % (
                "delete" if rm else "create", o["id"])
    fails = [x for x in checks if x["state"] == "FAIL"]
    mig_print_header(site, green["host"], bhost, "SETUP%s  TEST SCOPE  %s" % ("  REMOVE" if rm else "", "COMMIT" if a.commit
                                                                                else "plan only, nothing is written"))
    mig_print_checks(checks)
    commit = bool(a.commit and not fails)
    scope = mig_blue_scope(a, cfg, site, blue, {}, [])
    planned = mig_apply(objs, False, True, blue_scope=scope)
    pending = [r for r in planned if r["action"] in ("ADD", "UPDATE", "DELETE")]
    items = mig_items(planned)
    digest = mig_digest(planned, (), items)
    stopped = review = None
    perr = [r for r in planned if r["action"] == "ERROR"]
    if commit and perr:          # a plan read only in part is not a plan: nothing is written from it
        commit = False
        stopped = ("%d object(s) could not be read (%s): the plan is not complete, so nothing was written. "
                   "Run again" % (len(perr), ", ".join("%s %s" % (r["side"], r["id"]) for r in perr[:4])))
    if commit and a.expect:
        ok, review = mig_review(ctx["state_path"], a.expect, digest, items)
        if not ok:
            commit, stopped, review = False, review, None
    changing = commit and bool(pending)
    ctx["commit"], ctx["changed"], ctx["digest"], ctx["items"] = commit, changing, digest, items
    probes = mig_probes_start(mig_probe_targets(cfg, site, "setup", [], st), ctx) if changing else []
    results = mig_apply(objs, True, True, blue_scope=scope) if changing else planned
    ctx["wrote"] = mig_wrote(results) if changing else None
    post = mig_probe_checks(mig_probes_finish(probes, cfg), "setup")
    ctx["probes"] = []
    tally = mig_print_results(results, changing)
    blocked = [r for r in results if r["action"] == "BLOCKED"]
    print("")
    if not pending and not blocked:
        print("  No changes: %s." % ("no test segment of --setup is on Blue" if rm else "the test segment is on Blue as configured"))
    elif not commit and not stopped and pending:
        print("  plan %s: %d change(s), nothing written. To apply exactly these: --test --setup%s --commit --expect %s"
              % (digest, len(pending), " --remove" if rm else "", digest))
    if review:
        print("  %s" % review)
    if a.commit and fails:
        print("  COMMIT BLOCKED: %d pre-flight FAIL" % len(fails))
    if stopped:
        print("  STOPPED: %s" % stopped)
    leak = []
    if changing:
        chk, leak = mig_blue_proof(bhost, BH, bsite, blue, scope, outdir,
                                   grow=lambda snap: mig_bridge_infra_paths(cfg, site, snap))
        post.append(chk)
    if changing and results and all(r["action"] in ("ADD", "UNCHANGED") for r in results) and not leak:
        for o in objs:
            mig_state_event(st, o["id"], "setup", "OK", outdir, "created on Blue")
            print("  %s on Blue: the next --test run bridges it (its transit VLAN is given out then)" % o["id"])
    if changing and results and all(r["action"] in ("DELETE", "UNCHANGED") for r in results) and not leak and rm:
        for o in objs:
            mig_state_event(st, o["id"], "setup-remove", "OK", outdir, "deleted on Blue")
    if post:
        print("")
        mig_print_checks(post)
    if changing:
        S = " --site %s" % a.site if getattr(a, "site", None) else ""
        mig_print_undo(ctx, outdir, ["fp%s --test --setup --commit: the Blue test segment again" % S] if rm else
                       ["fp%s --test --setup --remove --commit: deleted again, once nothing of the test is on it" % S])
    write_json(outdir, "migpath_checks", checks + post)
    write_json(outdir, "migpath_apply" if commit else "migpath_plan",
               {"mode": "setup", "commit": commit, "changed": changing, "digest": digest, "site": site,
                "results": results})
    with open(os.path.join(outdir, "manual_steps.txt"), "w") as fh:
        fh.write(mig_manual_steps(site, "test setup", results, users))
    print("  evidence: %s" % outdir)
    rc = 1 if fails or tally["ERROR"] or leak or stopped or any(x["state"] == "FAIL" for x in post) else 0
    return 2 if rc == 0 and a.detailed_exitcode and not a.commit and (pending or blocked) else rc


def cmd_migpath(a):
    """Blue GM segment -> Green GM segment, same id, over two edge bridges. Plans by default; --commit
    writes. One run at a time per site; every run is journaled, whatever its outcome; the state file
    is written only when what it holds changes."""
    ctx = {"probes": [], "t0": now()}
    try:
        rc = _migpath(a, ctx)
    except SystemExit as e:
        rc = e.code
        if rc is not None and not isinstance(rc, int):
            print(rc, file=sys.stderr)
            if ctx.get("tee"):
                ctx["tee"].fh.write("%s\n" % rc)
            rc = 1
    except KeyboardInterrupt:
        print("\n  interrupted", file=sys.stderr)
        rc = 130
    finally:
        for p in ctx.get("probes") or []:
            p.kill()
        if ctx.get("tee"):
            sys.stdout = ctx["tee"].close()
    rc = int(rc or 0)
    st, path = ctx.get("state"), ctx.get("state_path")
    if st is not None and path:
        saved = False
        try:
            saved = mig_state_save(path, st, ctx.get("state_before"))
            mig_journal(path, {"ts": ctx["t0"], "args": " ".join(sys.argv[1:]), "action": ctx.get("action"),
                               "scope": ctx.get("scope"), "commit": bool(ctx.get("commit")),
                               "changed": bool(ctx.get("changed")), "digest": ctx.get("digest"),
                               "expect": getattr(a, "expect", None), "items": ctx.get("items") or None,
                               "wrote": ctx.get("wrote") or None, "undo": ctx.get("undo") or None,
                               "state_written": saved, "rc": rc, "evidence": ctx.get("outdir")})
        except OSError as e:
            print("  state not saved to %s: %s" % (path, e), file=sys.stderr)
            rc = rc or 1
        if ctx.get("outdir"):
            write_json(ctx["outdir"], "migpath_state", dict(
                {k: v for k, v in st.items() if k != "baselines"},
                baselines={k: {x: y for x, y in v.items() if x not in ("objects", "alarms")}
                           for k, v in st["baselines"].items()}))
    if ctx.get("lock"):
        ctx["lock"].close()                  # releases the lock
    sys.exit(rc)


def _migpath(a, ctx):
    global DRY
    DRY = False
    acts = [n for n, v in (("--router-mac", a.router_mac), ("--impact", a.impact), ("--baseline", a.baseline),
                           ("--setup", a.setup), ("--cutover", a.cutover), ("--unbridge", a.unbridge),
                           ("--rollback", a.rollback), ("--retire", a.retire), ("--edges", a.edges)) if v]
    act = acts[0] if len(acts) == 1 else None
    rm = bool(getattr(a, "remove", False))
    ctx["action"] = (act.lstrip("-") + ("-remove" if rm else "")) if act else ("remove" if rm else "build") if not acts \
        else "refused"
    if getattr(a, "by_site", False):
        return mig_config_by_site(a.config or os.environ.get("FLEETPARITY_CONFIG"))
    if getattr(a, "set", None):
        return mig_config_set(a.config or os.environ.get("FLEETPARITY_CONFIG"), a.set)
    cfg = read_config(a.config or os.environ.get("FLEETPARITY_CONFIG"))
    _MIG_SHOWN_SITES[:] = list(cfg.get("_site_blocks") or [])
    site = a.site or (_mig_items(cfg.get("mig_sites")) or [None])[0]
    _MIG_SHOWN.update(v2=bool(cfg.get("_v2")), site=site, signins_per_site=any(
        "%s_%s" % (k, x) in cfg for k in _CFG_SITE_SIGNINS for x in _MIG_SHOWN_SITES))
    cchk = mig_config_checks(cfg)
    cfg_dir = os.path.dirname(os.path.abspath(a.config)) if a.config else os.getcwd()
    if site:                    # the .csv waves the lists name, read now: a file that is not there stops the run here
        cchk += mig_list_files(cfg, site, cfg_dir)
        if getattr(a, "vm", None):          # --vm takes names, and .csv waves (relative to where it runs)
            items, a.vm = [x.strip() for v in a.vm for x in str(v).split(",") if x.strip()], []
            given_ = list(items)
            for it in items:
                if not it.lower().endswith(".csv"):
                    a.vm.append(it)
                    continue
                vals, exp, err = mig_read_list_file(it if os.path.isabs(it) else os.path.join(os.getcwd(), it), "vm")
                if vals is None:
                    cchk.append({"area": "config", "item": "%s, given to --vm" % it, "state": "FAIL",
                                 "detail": "not read (%s): its VMs are not known" % err})
                    continue
                a.vm += vals
                lst_ = "mig_return_vms" if getattr(a, "back", False) else "mig_move_vms"
                for v_ in vals:             # named in the UNDO and the reports as the config's waves are
                    cfg["_list_from"].setdefault((lst_, v_.lower()), it)
                for v_, s_ in exp.items():
                    cfg["_vm_subnet"][v_] = (s_, it)
            if not a.vm and not any(x["state"] == "FAIL" for x in cchk):
                cchk.append({"area": "config", "item": "--vm %s" % ",".join(given_), "state": "FAIL",
                             "detail": "names no VM (a wave file with no rows?): nothing to move or return. An empty "
                                       "list never means every VM"})
    if any(x["state"] == "FAIL" for x in cchk):
        print("")
        mig_print_checks(cchk)
        print("\n  the config is not used until these are fixed: nothing was read or written")
        return 1
    if not site:
        sys.exit("set mig_sites in the config (the Green location this migration lands on), or pass --site")
    # One config drives every site: any key given as <key>_<site> overrides <key> for a run at that site
    # (fed_ns_local_as, mig_blue_writes, leaf_user, leaf_password, ...). Nothing in the tool is tied to a site.
    sfx = "_%s" % site
    for k in [k for k in cfg if isinstance(k, str) and k.endswith(sfx) and len(k) > len(sfx)]:
        cfg[k[:-len(sfx)]] = cfg[k]
    base = a.outdir or cfg.get("outdir") or "/tmp/fleetparity"
    outdir, n = os.path.join(base, "migpath_%s" % time.strftime("%Y%m%d-%H%M%S")), 1
    while os.path.exists(outdir):                       # never overwrite another run's record
        n += 1
        outdir = os.path.join(base, "migpath_%s-%d" % (time.strftime("%Y%m%d-%H%M%S"), n))
    os.makedirs(outdir)
    ctx["outdir"] = os.path.abspath(outdir)
    ctx["tee"] = sys.stdout = _MigTee(sys.stdout, os.path.join(outdir, "console.txt"))
    gone_ = [n for n, v in (("--inventory", a.inventory), ("--assign", a.assign is not None), ("--skip", a.skip),
                            ("--wave", a.wave), ("--plan", a.plan), ("segment names", a.segments)) if v]
    if gone_:
        sys.exit("%s: gone in 1.15.0. The plan is no longer a file: every run reads Blue, and the config says what to "
                 "do: mig_scope_%s (CIDRs or segment names to bridge), mig_skip_%s (never bridge), mig_move_vms_%s "
                 "(VMs to move). Then fp to plan, fp --commit to apply (--expect <digest> for a build outside --test)" % (" and ".join(gone_), site, site, site))
    if len(acts) > 1:
        sys.exit("one action per run, not %s" % " and ".join(acts))
    if a.commit and act in ("--impact", "--baseline"):
        sys.exit("%s writes nothing to a manager: run it without --commit" % act)
    if a.setup and not a.test:
        sys.exit("--setup creates the Blue test segment: run it with --test")
    if rm and not (act == "--edges" or (a.test and act in (None, "--setup"))):
        sys.exit("--remove takes apart what one action built: --edges --remove (the bridge edges), --test --remove (the "
                 "test build), --test --setup --remove (the Blue test segment). A segment of the scope goes back by "
                 "listing it in skip, then fp and fp --commit --expect <the digest it prints>; a VM by fp --return --vm "
                 "<name or wave file> --commit")
    if rm and (getattr(a, "move", False) or getattr(a, "vm", None)):
        sys.exit("--move and --vm go with a build, not with --remove")
    back = bool(getattr(a, "back", False))      # --return --vm: VMs back to Blue in this one run, the config untouched
    if back and getattr(a, "move", False):
        sys.exit("--return and --move go one way each: one of them per run")
    if back and act:
        sys.exit("--return goes with a build run (fp, or fp --test), not with %s" % act)
    if back and not getattr(a, "vm", None):
        sys.exit("--return sends back the VMs --vm names: names, wildcards, segment:<subnet>, or a wave .csv")
    cfg_vms = _mig_items(_mig_key(cfg, "mig_move_vms", site))
    a.move_cfg = [str(x).strip() for x in cfg_vms if str(x).strip()] if not act else []   # --test runs too: a later run reads it
    if cfg_vms and not act and not a.test and not back:     # declared in the config: every build run converges them too
        a.move, a.vm = True, list(a.vm or []) + cfg_vms
    if getattr(a, "move", False) and not a.test and not a.vm and not act:
        sys.exit("--move outside --test moves the VMs it is given: --vm with names, wildcards, segment:<subnet> or a "
                 "wave .csv (or sites.<site>.move_vms). It never takes the whole scope at once")
    # back to Blue, on every build run (and --test runs, for the test segments' VMs); wins over move_vms
    a.ret_cfg = [str(x).strip() for x in _mig_items(_mig_key(cfg, "mig_return_vms", site)) if str(x).strip()] \
        if not act and not rm else []
    a.ret = list(a.ret_cfg) + ([str(x).strip() for x in a.vm if str(x).strip()] if back else [])
    if back:
        a.vm = []
    if getattr(a, "vm", None) and not getattr(a, "move", False):
        sys.exit("--vm names the VMs a --move takes to Green, or a --return sends back: run it with one of them")
    a.auto_verify = False
    if getattr(a, "move", False):
        if act:
            sys.exit("--move goes with a build (fp, or fp --test), not with %s" % act)
        a.auto_verify = not a.verify          # on for the moves, not asked for: a bridge not found holds them, not the build
        a.verify = True                       # moves only onto bridges this run found active
    if a.expect and not a.commit:
        sys.exit("--expect goes with --commit: it names the plan the commit must match")
    if a.test and act == "--router-mac":
        sys.exit("--test does not apply to --router-mac")
    if (a.verify or a.check_leaves) and act in ("--router-mac", "--impact", "--setup", "--edges"):
        sys.exit("--verify and --check-leaves go with a build or a segment action, not %s" % act)
    a.mode = ("cutover" if a.cutover else "unbridge" if a.unbridge else "rollback" if a.rollback else
              "retire" if a.retire else "build")

    # the state sits beside the config, where 1.14.0 kept its plan CSV (now only checked for SKIP decisions)
    legacy = cfg.get("mig_plan_file_%s" % site) or cfg.get("mig_plan_file") or "mig_plan_%s.csv" % site
    if not os.path.isabs(legacy) and a.config:
        legacy = os.path.join(os.path.dirname(os.path.abspath(a.config)), legacy)
    st_path = mig_state_file(cfg, site, legacy)
    mig_lock(st_path, ctx)
    st = mig_state_load(st_path, site)
    ctx["state"], ctx["state_path"], ctx["state_before"] = st, st_path, _mig_canon(st)

    ghost = cfg.get("nsx_gm_host")
    bhost = _mig_key(cfg, "mig_blue_gm_host", site)
    if not ghost or not bhost:
        sys.exit("set nsx_gm_host (Green) and mig_blue_gm_host (Blue) in the config")
    guser = cfg.get("nsx_gm_user") or "admin"
    gpw = secret("FLEETPARITY_NSX_GM_PASSWORD", cfg, ["nsx_gm_password"], "      Green Global Manager %s '%s' password (%s): "
                 % (ghost, guser, _mig_shown("nsx_gm_password")))
    buser = cfg.get("mig_blue_gm_user") or guser
    bpw = secret("FLEETPARITY_MIG_BLUE_GM_PASSWORD", cfg, ["mig_blue_gm_password"],
                 "      Blue Global Manager %s '%s' password (%s): " % (bhost, buser, _mig_shown("mig_blue_gm_password")))
    GH, BH = _mig_H(guser, gpw), _mig_H(buser, bpw)
    # each site's Local Managers, Green and Blue: from the config, else as each Global Manager has them registered
    all_sites = [str(x) for x in _mig_items(cfg.get("mig_sites"))] or [site]
    all_sites += [] if site in all_sites else [site]
    need_g = [x for x in all_sites if not cfg.get("nsx_lm_host_%s" % x)]
    need_b = [x for x in all_sites if not cfg.get("mig_blue_lm_host_%s" % x) and cfg.get("mig_blue_site_%s" % x)]
    gsites_ = _mig_list(ghost, GH, "/sites")[0] if need_g else None
    bsites_ = _mig_list(bhost, BH, "/sites")[0] if need_b else None
    for x in need_g:
        lm_, why_ = mig_lm_of(ghost, GH, x, gsites_)
        if lm_:
            cfg["nsx_lm_host_%s" % x] = lm_
            cfg["nsx_lm_host"] = lm_ if x == site else cfg.get("nsx_lm_host")
            log("-- Green Local Manager at %s: %s (registered on %s)" % (x, lm_, ghost))
        else:
            log("-- Green Local Manager at %s: not found (%s)" % (x, why_))
    for x in need_b:
        lm_, why_ = mig_lm_of(bhost, BH, cfg.get("mig_blue_site_%s" % x), bsites_)
        if lm_:
            cfg["mig_blue_lm_host_%s" % x] = lm_
            cfg["mig_blue_lm_host"] = lm_ if x == site else cfg.get("mig_blue_lm_host")
            log("-- Blue Local Manager at %s: %s (registered on %s)" % (x, lm_, bhost))
        else:
            log("-- Blue Local Manager at %s: not found (%s)" % (x, why_))
    green_lms = mig_green_lm_signins(cfg, site, ask=not DRY)
    own_lm = next(((u_, p_) for f_, u_, p_ in green_lms if f_ == str(cfg.get("nsx_lm_host_%s" % site) or "").strip()), None)
    luser = own_lm[0] if own_lm else (cfg.get("nsx_admin_user") or "admin")
    lpw = own_lm[1] if own_lm else ""
    blm = _mig_key(cfg, "mig_blue_lm_host", site)
    # Blue's Local Managers differ by site: mig_blue_lm_user_<site> / mig_blue_lm_password_<site> first,
    # then the shared mig_blue_lm_*, then the Blue Global Manager's; a listed but blank password is asked for
    blm_user = _mig_key(cfg, "mig_blue_lm_user", site) or buser
    blm_pw = (os.environ.get(env_key("FLEETPARITY_MIG_BLUE_LM_PASSWORD", site))
              or os.environ.get("FLEETPARITY_MIG_BLUE_LM_PASSWORD") or _mig_key(cfg, "mig_blue_lm_password", site))
    if not blm_pw and blm and "mig_blue_lm_password_%s" % site in cfg and not DRY:
        blm_pw = getpass.getpass("      Blue Local Manager %s '%s' password (%s; Enter = the Blue Global Manager's): " % (
            blm, blm_user, _mig_shown("mig_blue_lm_password_%s" % site)))
    if blm:
        _MIG_CRED_KEY[blm] = ("mig_blue_lm_password_%s" % site if _mig_key(cfg, "mig_blue_lm_password", site) else
                              "mig_blue_gm_password")
    blm_pw = blm_pw or bpw
    users = {ghost: guser, bhost: buser}

    if a.router_mac:
        log("-- router MAC: Blue %s, Green %s" % (blm or "not set", ", ".join(h for h, _u, _p in green_lms) or "none"))
        blue_macs = {blm: mig_lm_vdr_mac(blm, blm_user, blm_pw)} if blm else {}
        probes = []

        def start():
            probes.extend(mig_probes_start(mig_probe_targets(cfg, site, "router-mac", [], st), ctx))

        ctx["commit"] = bool(a.commit)
        rc, digest, items, n, written = mig_router_mac(
            cfg, a, green_lms, blue_macs, outdir, before_write=start if a.commit else None,
            review=lambda d, i: mig_review(ctx["state_path"], a.expect, d, i), state=st)
        ctx["digest"], ctx["items"], ctx["changed"] = digest, items, bool(written)
        if written:
            was = sorted({str(v.get("before")) for v in (st.get("router_mac") or {}).values() if v.get("before")})
            mig_print_undo(ctx, outdir, ["set mig_router_mac back to %s, then fp --router-mac --commit. Refused while it "
                                         "is Blue's router MAC: no two NSX on one bridged segment may share one"
                                         % (" or ".join(was) or "the value before")])
        presults = mig_probes_finish(probes, cfg)
        ctx["probes"] = []
        post = mig_probe_checks(presults, "router-mac")
        if post:
            print("")
            mig_print_checks(post)
            write_json(outdir, "probes", presults)
        write_json(outdir, "migpath_checks", post)
        print("  evidence: %s" % outdir)
        rc = 1 if rc or any(x["state"] == "FAIL" for x in post) else 0
        return 2 if rc == 0 and a.detailed_exitcode and not a.commit and n else rc

    sites, st_ = _mig_list(bhost, BH, "/sites")
    want = _mig_key(cfg, "mig_blue_site", site)
    bsite = (_mig_named(sites or [], want) or [None])[0] if want else None
    if not bsite:
        sys.exit("Blue location %r not found on %s (HTTP %s). Locations: %s. Set mig_blue_site_%s."
                 % (want, bhost, st_, ", ".join(str(s.get("id")) for s in sites or []) or "none", site))
    log("-- Green Global Manager %s, location %s" % (ghost, site))
    green = mig_side(ghost, GH, site)
    log("-- Blue Global Manager %s, location %s" % (bhost, bsite.get("id")))
    blue = mig_side(bhost, BH, bsite.get("id"))
    green["_H"], blue["_H"] = GH, BH
    others_ = [x for x in sites or [] if x.get("id") != bsite.get("id")]
    blue["here"] = bsite.get("display_name") or bsite.get("id")
    blue["there"] = (others_[0].get("display_name") or others_[0].get("id")) if len(others_) == 1 else "the other site"
    lm, lmhost = None, cfg.get("nsx_lm_host_%s" % site)
    for fq, u_, pw_ in green_lms:
        if not pw_:                     # no password of its own: not signed in to, so nothing counts against it
            green["router_macs"][fq] = {"status": "not read: no password in %s" % _mig_shown(_MIG_CRED_KEY.get(fq, ""))}
            continue
        log("-- Green Local Manager %s (router MAC)" % fq)
        green["router_macs"][fq] = mig_lm_vdr_mac(fq, u_, pw_)
    if blm:
        log("-- Blue Local Manager %s (router MAC)" % blm)
        blue["router_macs"][blm] = mig_lm_vdr_mac(blm, blm_user, blm_pw)
        log("-- Blue Local Manager %s (segments at %s)" % (blm, bsite.get("id")))
        blue["site_segments"], blue["lm_local"], blue["site_why"] = mig_blue_site_segments(blm, _mig_H(blm_user, blm_pw))
        blue["lm_host"] = blm
    else:
        blue["site_segments"], blue["lm_local"], blue["site_why"] = None, [], "set mig_blue_lm_host_%s" % site
    glm_pw = lpw if lmhost else ""          # the site's own Green Local Manager, as mig_green_lm_signins resolved it
    if lmhost:
        log("-- Green Local Manager %s (edge zones)" % lmhost)
        lm = mig_lm_edges(lmhost, luser, glm_pw)
    for nm, d in (("migpath_green", green), ("migpath_blue", blue)):
        write_json(outdir, nm, {k: v for k, v in d.items() if not k.startswith("_")})

    # Snapshots for the no-impact proof: what exists before this run touches anything.
    log("-- snapshots (Green and Blue objects, Blue open alarms)")
    green["snapshot"] = mig_snapshot(ghost, GH, green)
    blue["snapshot"] = mig_snapshot(bhost, BH, blue)
    balarms = {bhost: mig_alarms(bhost, BH)}
    if blm:
        balarms[blm] = mig_alarms(blm, _mig_H(blm_user, blm_pw))
    write_json(outdir, "blue_snapshot", {"site": bsite.get("id"), "host": bhost, "taken": now(),
                                         "objects": blue["snapshot"], "alarms": balarms})
    if a.edges:
        return mig_edges_run(cfg, site, a, ctx, blue, bhost, BH, bsite, st, outdir,
                             {"Green": (lmhost, luser, glm_pw), "Blue": (blm, blm_user, blm_pw)}, green=green)
    tnames = _mig_items(_mig_key(cfg, "mig_test_segments", site))
    tids = set(mig_test_ids(cfg, site, blue["segments"])[1])
    a.test_ids = sorted(tids)
    if a.setup:
        return mig_setup_run(cfg, site, a, ctx, green, blue, bhost, BH, bsite, balarms, st, outdir, users,
                             blm=(blm, blm_user, blm_pw))
    # the plan: Blue as it is now, the config's scope and skips, the transit VLANs in the state
    rows, plan_checks = mig_rows(cfg, site, blue, green, st, tids)
    a.test_ids = sorted(tids | {r["segment"] for r in rows if r["segment"] in tnames or r.get("name") in tnames
                                or r.get("subnet") in tnames})
    plan_checks += mig_legacy_plan(legacy, site, rows)

    leaves_auto = False
    if a.mode in ("build", "cutover", "rollback") and not a.impact and not a.check_leaves and mig_leaf_ports(cfg, site):
        # a build writes the switch lines from each port's current VLAN list; a cutover or rollback
        # moves traffic onto the bridge, so the transit VLAN must be on every listed port first
        a.check_leaves = True
        leaves_auto = a.mode == "build"
    checks, objs, res = mig_plan(cfg, site, a, green, blue, lm, rows, st)
    checks = plan_checks + checks
    gbp_, bbp_ = mig_edge_bps(res)          # each segment's transit VLANs, as each side's migration bridge carries them
    gix_, bix_ = {x.get("id"): x for x in green["segments"]}, {x.get("id"): x for x in blue["segments"]}

    def _vl(o, bp):
        return sorted({int(v) for e in (o or {}).get("bridge_profiles") or [] if bp and _mig_rel(e.get("bridge_profile_path")) == bp
                       for v in e.get("vlan_ids") or [] if str(v).isdigit()})
    res["bridged_vlans"] = {r["segment"]: (_vl(gix_.get(r["segment"]), gbp_), _vl(bix_.get(r["segment"]), bbp_))
                            for r in res["rows"]}
    if a.ret and not a.verify:      # a VM going back onto a cut-over segment reaches Green's gateway over the bridges
        gon_ = {x.get("id"): x for x in green["segments"]}
        a.verify = a.auto_verify = any(r["segment"] in gon_ and _mig_conn(gon_[r["segment"]]) == "ON" and any(
            v.get("where") == "green" for v in ((st["segments"].get(r["segment"]) or {}).get("vms") or {}).values())
            for r in res["rows"])
    unread = (mig_unread("Green", green, ("segments", "bridge_profiles"))
              + mig_unread("Blue", blue, ("segments", "bridge_profiles")))
    if unread:              # a segment missing from a list NSX did not return is not a retired segment
        checks.append({"area": "migpath", "item": "segment status from NSX", "state": "WARN",
                       "detail": "not read: %s. Each segment keeps the status last read" % ", ".join(unread)})
    else:
        gall = {x.get("id"): x for x in green["segments"]}
        ball = {x.get("id"): x for x in blue["segments"]}
        ball.update({r["segment"]: None for r in rows if r["segment"] and r["segment"] not in ball})
        mig_refresh_status(st, rows, gall, ball, *mig_edge_bps(res))
        checks += mig_gateway_checks(rows, gall, ball, st=st)
    scope_key = mig_scope_key(a)
    ctx["scope"] = scope_key
    leaf_only = bool(a.baseline and a.check_leaves and not leaves_auto)   # --baseline --check-leaves
    if leaf_only and not res["rows"]:
        sys.exit("no segment in this scope, so no transit VLAN to read on the leaves: set mig_scope_%s, or use --test"
                 % site)
    if scope_key and not a.impact and ((a.baseline and not leaf_only) or scope_key not in st["baselines"]):
        checks.append(mig_baseline(st, scope_key, outdir, bsite, bhost, blue, balarms))
    live = not a.impact and not a.baseline
    if live and res["rows"]:
        checks += mig_vm_checks(cfg, site, a, res, st, blue, (blm, blm_user, blm_pw), outdir)
        if a.mode == "cutover":
            checks += mig_dhcp_checks(res, green, blue)
    if live and res.get("drop"):
        checks += mig_drop_checks(cfg, site, res, objs)
    glm_H = _mig_H(luser, glm_pw) if lmhost else None
    res["tunnels"] = {}
    if live and res["rows"] and lmhost and lm is not None and a.mode in ("build", "cutover", "rollback", "unbridge"):
        tc_, res["tunnels"] = mig_tunnel_checks(cfg, site, lmhost, glm_H, lm, res, a.mode)
        checks += tc_
    tep_rows = []           # every build, every site: tunnel pools that need a gateway get the leaves' one
    if live and res["rows"] and lmhost and lm is not None and a.mode == "build":
        tep_rows, tc_ = mig_tep_plan(cfg, site, lmhost, glm_H, lm, res)
        checks += tc_
    captured = mig_tag_capture(res, st) if live and a.mode != "retire" else {}
    tag_rows, gidx = [], None
    if captured and not lmhost:
        checks.append({"area": "tags", "item": "NSX tags from Blue on Green", "state": "WARN",
                       "detail": "set nsx_lm_host_%s: %d VM(s) have tags captured on Blue" % (site, len(captured))})
    elif captured:
        gidx = mig_nsx_vm_index(lmhost, glm_H)      # Green's VM inventory, read once for the whole scope
        tag_rows = mig_tags_apply(lmhost, glm_H, captured, False, gidx)
        checks += mig_tag_checks(tag_rows, a.mode)
    # VMs returned to Blue whose NSX tags are not all back on Blue's Local Manager yet: every build run finishes it
    owed = mig_tags_owed(res, st) if live and a.mode == "build" else {}
    btag_rows, BLH_ = [], (_mig_H(blm_user, blm_pw) if blm else None)
    if owed and not blm:
        checks.append({"area": "tags", "item": "NSX tags back on Blue", "state": "WARN",
                       "detail": "set mig_blue_lm_host_%s: %d VM(s) returned to Blue wait for their tags" % (site, len(owed))})
    elif owed:
        btag_rows = mig_tags_apply(blm, BLH_, owed, False, where="Blue")
        if not _mig_blue_writes(cfg, a):
            for t in btag_rows:
                if t["action"] == "ADD":
                    t["action"], t["detail"] = "BLOCKED", "Blue writes disabled: put back by hand: %s" % ", ".join(
                        "%s=%s" % (x["scope"], x["tag"]) for x in t["add"])
        checks += mig_tag_checks(btag_rows, a.mode, where="Blue")
    leafcmds = {}
    if a.check_leaves and res["rows"]:
        lc, leafcmds = mig_leaves(cfg, site, res, outdir, st, reset=leaf_only, soft=leaves_auto)
        checks += lc
    if a.verify and res["rows"]:
        vc_ = mig_verify(cfg, site, res, lm, outdir)
        if getattr(a, "auto_verify", False):    # read for the VM moves: a bridge not active holds the moves onto it
            for x in vc_:
                if x["state"] == "FAIL":
                    x["state"], x["detail"] = "WARN", x["detail"].rstrip(". ") + ". VMs move onto it only once both are found active"
        checks += vc_
    if a.impact:
        checks += mig_impact_checks(a, cfg, site, blue, balarms, rows, res, outdir, st, scope_key)
    fails = [x for x in checks if x["state"] == "FAIL"]

    label = "IMPACT" if a.impact else "BASELINE" if a.baseline else a.mode.upper()
    sc_ = _mig_items(_mig_key(cfg, "mig_scope", site))
    sc_lbl = ("  TEST SCOPE" if getattr(a, "test", False) else
              "  SCOPE %s" % ",".join(sc_) if sc_ and a.mode == "build" else "")
    mig_print_header(site, ghost, bhost, "%s%s%s" % (
        label, sc_lbl,
        "  read-only, compared with %s" % ("the recorded baseline" if a.impact == "@state" else a.impact) if a.impact
        else "  read-only" if a.baseline else "  COMMIT" if a.commit else "  plan only, nothing is written"))
    mig_print_checks(checks)
    mig_print_state(st, res, st_path)
    if a.impact or a.baseline:
        write_json(outdir, "migpath_checks", checks)
        bad = [x for x in checks if x.get("area") == "impact" and x["state"] == "FAIL"]
        print("")
        if a.impact:
            print("  %s" % ("BLUE CHANGED OUTSIDE THE SCOPE" if bad else "Blue: no change outside the scope"))
        else:
            print("  recorded: %s" % ("the VLANs on each listed leaf port" if leaf_only else
                                      "the Blue baseline for %s; --impact compares with it" % scope_key))
        if rows:
            mig_reports(cfg, site, rows, st, os.path.dirname(st_path), outdir)
        print("  evidence: %s" % outdir)
        return 1 if bad else 0

    commit = bool(a.commit and not fails)
    scope = mig_blue_scope(a, cfg, site, blue, res, rows)
    # The plan: every object read live, nothing written. Its digest names exactly these changes;
    # --commit --expect <digest> writes only if the plan is still the one that was reviewed.
    planned = mig_apply(objs, False, stop_on_error=a.mode != "build", blue_scope=scope)
    pending = [r for r in planned if r["action"] in ("ADD", "UPDATE", "DELETE")]
    # VMs back to Blue first (return_vms wins over move_vms, and takes its place in move_batch), then forward
    ret_rows, rctx = mig_return_plan(cfg, site, res, st, checks, green, blue, a.ret, _mig_blue_writes(cfg, a), blm) \
        if a.ret else ([], {})
    move_rows, mctx = mig_move_plan(        # moves wait for the build, tunnel pool gateways included
        cfg, site, res, st, checks, len(pending) + sum(1 for r_ in tep_rows if r_["action"] == "UPDATE"),
        getattr(a, "vm", None), hold=rctx.get("hold") or (),
        taken=sum(1 for r in ret_rows if r["kind"] == "vm-return" and r["action"] == "UPDATE"),
        skip_settings=rctx.get("settings") or ()) if getattr(a, "move", False) else ([], {})
    if getattr(a, "back", False) and getattr(a, "move_cfg", None):
        segrow_ = {r_["segment"]: r_ for r_ in res.get("rows") or []}
        for r_ in ret_rows:
            if r_.get("kind") == "vm-return" and r_["action"] == "UPDATE" and _mig_vm_listed(
                    a.move_cfg, r_["id"], segrow_.get(r_.get("segment")) or {"segment": r_.get("segment")}):
                r_["move_listed"] = True
    vm_rows = ret_rows + move_rows
    move_pending = [r for r in vm_rows if r["action"] in ("UPDATE", "ADD")]     # ADD: a VM folder made on Green
    tep_pending = [r for r in tep_rows if r["action"] == "UPDATE"]
    tag_pending = [t for t in tag_rows if t["action"] == "ADD"]
    btag_pending = [t for t in btag_rows if t["action"] == "ADD"]
    items = mig_items(planned + tep_rows + vm_rows, tag_rows + btag_rows)
    digest = mig_digest(planned + tep_rows + vm_rows, tag_rows + btag_rows, items)
    ctx["digest"], ctx["items"] = digest, items
    stopped = review = None
    perr = [r for r in planned + tep_rows + vm_rows if r["action"] == "ERROR"]
    if commit and perr:          # a plan read only in part is not a plan: nothing is written from it
        commit = False
        stopped = ("%d object(s) could not be read (%s): the plan is not complete, so nothing was written. "
                   "Run again" % (len(perr), ", ".join("%s %s" % (r["side"], r["id"]) for r in perr[:4])))
    if commit and a.expect:
        ok, review = mig_review(ctx["state_path"], a.expect, digest, items)
        if not ok:
            commit, stopped, review = False, review, None
    # Outside --test, a build run changes NSX itself (segments, bridges, what the scope takes apart, tunnel pool
    # gateways) only with --expect, the digest of the plan that was read. Without it those changes are HELD and
    # the rest of the run goes ahead: a wave or a return commits its VMs and nothing else, and nothing in the
    # scope is built or taken apart by a command typed for something else.
    guard = a.mode == "build" and not getattr(a, "test", False)
    held = []
    if commit and guard and not a.expect and (pending or tep_pending):
        held = pending + tep_pending
        for r in held:
            r["action"], r["detail"] = "HELD", "planned window, --expect: %s" % (r.get("detail") or r.get("kind"))
        pending, tep_pending = [], []
    changing = commit and bool(pending or tag_pending or move_pending or tep_pending or btag_pending)
    ctx["commit"], ctx["changed"] = commit, False
    probes = mig_probes_start(mig_probe_targets(cfg, site, a.mode, res["rows"], st), ctx) if changing else []
    if changing and btag_pending:
        log("-- NSX tags back on Blue (%s)" % blm)
        btag_rows = mig_tags_apply(blm, BLH_, owed, True, where="Blue")
        mig_tags_back(st, btag_rows)
        ctx["changed"] = True
    if changing and tag_pending:
        log("-- NSX tags on Green (%s)" % lmhost)
        tag_rows = mig_tags_apply(lmhost, glm_H, captured, True, gidx)
        ctx["changed"] = True
        bad = [t for t in tag_rows if t["action"] in ("ERROR", "BLOCKED")]
        if bad and a.mode == "cutover":
            commit = changing = ctx["commit"] = False
            stopped = "NSX tags not all on Green (%s): the gateway was not moved" % ", ".join(t["vm"] for t in bad[:4])
    if commit:
        mig_tags_placed(st, tag_rows)
    if changing and tep_pending:
        log("-- tunnel pool gateways on %s" % lmhost)
        tep_rows = mig_tep_apply(lmhost, glm_H, tep_rows)
        ctx["changed"] = True
    results = planned
    if changing and pending:
        results = mig_apply(objs, True, stop_on_error=a.mode != "build", blue_scope=scope)
        ctx["changed"], ctx["wrote"] = True, mig_wrote(results)
    post = []
    wait_t = int(cfg["mig_move_tag_wait"]) if cfg.get("mig_move_tag_wait") not in (None, "") else 180
    if changing and any(r["action"] == "UPDATE" for r in ret_rows):
        ret_rows = mig_return_apply(cfg, site, ret_rows, rctx, st)
        ctx["changed"] = True
        if any(r["kind"] == "vcenter-setting" and r["action"] == "ERROR" for r in ret_rows):
            for r in move_rows:
                if r["action"] in ("UPDATE", "ADD"):     # ADD: a folder for them, not made either
                    r["action"], r["detail"] = "BLOCKED", "not attempted: the vCenter setting failed"
        back = {r["id"] for r in ret_rows if r["kind"] == "vm-return" and r["action"] == "UPDATE"}
        cap = {n: c_ for n, c_ in (rctx.get("tags") or {}).items() if n in back}
        if cap and blm:               # their NSX tags back on Blue, once Blue's NSX inventory has them
            t0 = time.time()
            while True:
                trows = mig_tags_apply(blm, BLH_, cap, True, where="Blue")
                if not any(t["action"] == "PENDING" for t in trows) or time.time() - t0 >= wait_t:
                    break
                time.sleep(10)
            mig_tags_back(st, trows)
            btag_rows += trows
            post += mig_tag_checks(trows, a.mode, where="Blue")
            if any(t["action"] in ("PENDING", "ERROR") for t in trows):
                post.append({"area": "tags", "item": "NSX tags of the returned VMs", "state": "WARN",
                             "detail": "not all back on Blue after %ds: the next fp --commit puts the rest back" % wait_t})
    if changing and any(r["action"] == "UPDATE" for r in move_rows):
        move_rows = mig_move_apply(cfg, site, move_rows, mctx, st)
        ctx["changed"] = True
        moved = {r["id"] for r in move_rows if r["kind"] == "vm-move" and r["action"] == "UPDATE"}
        cap = {n: c_ for n, c_ in mig_tag_capture(res, st).items() if n in moved}
        if cap and lmhost:            # their Blue tags on Green, once Green's NSX inventory has them
            t0 = time.time()
            while True:
                trows = mig_tags_apply(lmhost, glm_H, cap, True)
                if not any(t["action"] == "PENDING" for t in trows) or time.time() - t0 >= wait_t:
                    break
                time.sleep(10)
            mig_tags_placed(st, trows)
            post += mig_tag_checks(trows, a.mode)
            if any(t["action"] == "PENDING" for t in trows):
                post.append({"area": "tags", "item": "NSX tags of the moved VMs", "state": "WARN",
                             "detail": "not all in Green's NSX inventory after %ds: run the same build with --commit to "
                                       "place the rest" % wait_t})
    if commit and a.mode in ("cutover", "rollback") and res["rows"]:
        flip = [r for r in results if r["kind"] == "connectivity"]
        if flip and all(r["action"] in ("UPDATE", "UNCHANGED") for r in flip):
            for r in res["rows"]:
                log("-- route %s on the leaves: waiting for %s (up to %ds, each leaf's reading every 15s)" % (
                    r["net"], "Green" if a.mode == "cutover" else "Blue", int(cfg.get("mig_route_wait") or 90)))
                post.append(mig_route_wait(cfg, site, str(r["net"]), "green" if a.mode == "cutover" else "blue",
                                           res.get("green_nets")))
        else:
            post.append({"area": "route", "item": "route on the leaves", "state": "SKIP",
                         "detail": "the gateway did not move this run"})
    presults = mig_probes_finish(probes, cfg)
    ctx["probes"] = []
    post += mig_probe_checks(presults, a.mode)
    if presults:
        write_json(outdir, "probes", presults)
    # The leaves not showing the route moved, while the segment's gateway answers again after the change: the
    # gateway is on one side only, so traffic reaches it there. The leaves' reading is in doubt, not the move:
    # a WARN to check by hand, never a call to roll back.
    for p_ in post:
        if p_["area"] != "route" or p_["state"] != "FAIL":
            continue
        gws_ = {str(r["gw"]) for r in res["rows"] if r.get("gw") is not None and "route %s " % r["net"] in p_["item"] + " "}
        for r_ in presults or []:
            if str(r_.get("ip")) in gws_ and not r_.get("error") and r_.get("answered_before") \
                    and r_.get("judged", 0) - r_.get("lost", 0) >= 5:
                p_["state"] = "WARN"
                p_["detail"] = ("the gateway %s answers again after the change (lost %d of %d, longest gap %.1fs), so traffic "
                                "reaches it on the %s side; the leaves were not read as moved: %s. Check them by hand"
                                % (r_["ip"], r_["lost"], r_["judged"], r_["longest_gap_s"],
                                   "Green" if a.mode == "cutover" else "Blue", p_["detail"]))
                break
    vm_rows = ret_rows + move_rows
    tally = mig_print_results(results + tep_rows + vm_rows, commit and bool(pending or move_pending or tep_pending))
    blocked = [r for r in results + tep_rows + vm_rows if r["action"] == "BLOCKED"]
    hard = [r for r in blocked if "by hand" not in r["detail"]]
    print("")
    S_ = " --site %s" % a.site if getattr(a, "site", None) else ""
    if not pending and not tag_pending and not move_pending and not tep_pending and not btag_pending and not blocked \
            and not held:
        back_ = {str(y).lower() for y in a.ret or []}       # a VM in both lists is returned: not said to be on Green
        fwd_ = [x for x in getattr(a, "vm", None) or [] if str(x).lower() not in back_]
        print("  No changes: NSX already matches the plan for this scope%s%s." % (
            ", and the VMs listed are on Green" if fwd_ else "" if getattr(a, "vm", None) else
            ", and no VM of it is left on Blue" if getattr(a, "move", False) else "",
            ", and the VMs listed to return are on Blue" if a.ret else ""))
    elif not commit and not stopped and (pending or tag_pending or move_pending or tep_pending or btag_pending):
        print("  plan %s: %d change(s)%s, nothing written. To apply: the same command with --commit %s" % (
            digest, len(pending) + len(tag_pending) + len(move_pending) + len(tep_pending) + len(btag_pending),
            " and %d BLOCKED" % len(blocked) if blocked else "",
            ("--expect %s (%d of them change NSX itself, which outside --test goes in only with --expect)"
             % (digest, len(pending) + len(tep_pending))) if guard and (pending or tep_pending) else
            "(--expect %s holds it to exactly these)" % digest))
    if held:
        print("  HELD: %d change(s) to NSX itself (segments, bridges, tunnel pools) not made: outside --test they go in "
              "only with --expect, in a planned window: %s" % (len(held), (
                  "fp%s --commit --expect %s" % (S_, digest)) if not (move_pending or tag_pending or btag_pending) else
                  "fp%s (the plan), then fp%s --commit --expect <the digest it prints>" % (S_, S_)))
    again_ = sorted(r_["id"] for r_ in ret_rows if r_.get("move_listed"))
    if again_:
        them_ = "it" if len(again_) == 1 else "them"
        print("  WARN: %s: in %s too, so the next run without --return moves %s to Green again. Take %s out of that "
              "list" % (", ".join(again_), _mig_shown("mig_move_vms_%s" % site), them_, them_))
    if review:
        print("  %s" % review)
    if a.commit and fails:
        print("  COMMIT BLOCKED: %d pre-flight FAIL" % len(fails))
    if stopped:
        print("  STOPPED: %s" % stopped)
    leak = []
    if changing and pending:           # every run that wrote proves what it changed on Blue
        chk, leak = mig_blue_proof(bhost, BH, bsite, blue, scope, outdir,
                                   grow=lambda snap: mig_bridge_infra_paths(cfg, site, snap))
        post.append(chk)
        after = mig_digest(results, tag_rows)
        if not tally["ERROR"] and after != digest:
            post.append({"area": "impact", "item": "changes written are the planned ones", "state": "WARN",
                         "detail": "planned %s, written %s: an object changed during the run; re-run to see where it "
                                   "stands" % (digest, after)})
        # the segments as NSX now has them: observed status, and a flip left half done
        gnow, bnow = {}, {}
        for r in res["rows"]:
            for host_, H_, into in ((ghost, GH, gnow), (bhost, BH, bnow)):
                st_x, x_ = gm_get(host_, H_, "/segments/%s" % r["segment"])
                if st_x == 200 and isinstance(x_, dict):
                    into[r["segment"]] = x_
                elif st_x == 404:
                    into[r["segment"]] = None
        mig_refresh_status(st, [r for r in res["rows"] if r["segment"] in gnow and r["segment"] in bnow],
                           gnow, bnow, *mig_edge_bps(res))
        post += mig_gateway_checks(res["rows"], gnow, bnow, after_write=True, st=st)
        gone_ = [x for x in results if x.get("kind") == "segment" and x["action"] == "DELETE" and x.get("side") == "Green"]
        if gone_:
            post.append(mig_delete_wait(cfg, ghost, GH, gone_, res, green_lms))
        for x in results:              # prefix-list entries this tool placed are the only ones it removes
            if x["kind"] == "prefix-list" and x["action"] == "UPDATE" and x.get("segment"):
                seg_ = mig_state_seg(st, x["segment"])
                owned = set(seg_.get("prefix_lists") or [])
                if a.mode == "cutover":
                    owned.add(x["path"])
                else:
                    owned.discard(x["path"])
                seg_["prefix_lists"] = sorted(owned)
    if post:
        print("")
        print("  AFTER THE CHANGE")
        mig_print_checks(post)
    if ctx["changed"]:
        for r in res["rows"]:
            mine = [x for x in results if x.get("segment") == r["segment"]]
            wrote = [x for x in mine if x["action"] in ("ADD", "UPDATE", "DELETE")]
            errs = [x for x in mine if x["action"] == "ERROR"]
            tagged = [t for t in tag_rows if t.get("segment") == r["segment"] and t["action"] == "ADD"]
            if wrote or errs or tagged:
                rt = "; ".join("route %s: %s" % (p["state"], p["detail"]) for p in post
                               if p["area"] == "route" and str(r["net"]) in p["item"])
                mig_state_event(st, r["segment"], a.mode, "ERROR" if errs else "OK", outdir, "; ".join(
                    x for x in ("%d object(s) written" % len(wrote) if wrote else "",
                                "NSX tags on %d VM(s)" % len(tagged) if tagged else "", rt) if x))
    if commit and a.mode == "build":
        for r in res.get("drop") or []:     # taken apart: Blue's bridge off, Green's segment gone, its VLAN back to the pool
            mine = [x for x in results if x.get("segment") == r["segment"]]
            wrote = [x for x in mine if x["action"] in ("UPDATE", "DELETE")]
            errs = [x for x in mine if x["action"] == "ERROR"]
            if not wrote and not errs:
                continue
            seg_ = mig_state_seg(st, r["segment"])
            if any(x["side"] == "Green" and x["action"] == "DELETE" for x in mine):
                seg_.pop("transit_vlan", None)
                seg_["status"] = "planned"
            mig_state_event(st, r["segment"], "drop", "ERROR" if errs else "OK", outdir, "; ".join(
                ["Blue's bridge taken off" if x["side"] == "Blue" else "Green's segment deleted" for x in wrote]
                + ["%s %s: %s" % (x["side"], x["id"], x["detail"]) for x in errs]))
    checks += post
    write_json(outdir, "migpath_checks", checks)
    write_json(outdir, "migpath_apply" if commit else "migpath_plan",
               {"mode": a.mode, "commit": commit, "changed": ctx["changed"], "digest": digest, "site": site,
                "results": [{k: v for k, v in r.items() if k != "body"} for r in tep_rows] + results + vm_rows})
    if tag_rows or btag_rows:
        write_json(outdir, "tags", tag_rows + btag_rows)
    if a.mode == "build":
        with open(os.path.join(outdir, "switch_requirements.txt"), "w") as fh:
            fh.write(mig_switch_spec(cfg, site, res, leafcmds))
        with open(os.path.join(outdir, "migration_strategy.txt"), "w") as fh:
            fh.write(mig_steps(cfg, site, res, a))
    with open(os.path.join(outdir, "manual_steps.txt"), "w") as fh:
        fh.write(mig_manual_steps(site, "%s%s" % (a.mode, (" " + mig_target(a)) if mig_target(a) else ""),
                                  results, users, tag_rows, lmhost, luser))
    if a.commit and hard and not fails and not stopped:
        print("")
        print("  NOT DONE: %d object(s) BLOCKED; the reason is on each line above" % len(hard))
    rfail = [p for p in post if p["area"] == "route" and p["state"] == "FAIL"]
    if rfail and a.mode == "cutover":
        print("")
        print("  THE ROUTE DID NOT MOVE TO GREEN. Roll back:")
        print("    fp%s%s --rollback %s --commit" % (S_, " --test" if a.test else "", a.cutover))
    if ctx["changed"]:
        u_ = mig_undo(a, site, results, vm_rows, tep_rows, res)
        if held and any(" --move " in x for x in u_):
            u_.append("a move waits while the HELD change(s) above are pending: they go in first, in a planned window")
        mig_print_undo(ctx, outdir, u_)
    # the one command forward for each subnet this run acted on, once it ended clean; never after a way back
    clean_ = not (fails or tally["ERROR"] or leak or stopped or held or any(p["state"] == "FAIL" for p in post))
    planned_ = not a.commit and bool(pending or tag_pending or move_pending or tep_pending or btag_pending)
    back_run = a.mode == "rollback" or getattr(a, "back", False) or bool(getattr(a, "ret_cfg", None)) or any(
        r.get("kind") == "vm-return" and r["action"] == "UPDATE" for r in ret_rows) or (
        a.mode == "cutover" and any(r.get("kind") == "segment-bridge" and r["action"] in ("ADD", "UPDATE") for r in results)
        and not any(r.get("kind") == "connectivity" and r["action"] == "UPDATE" for r in results))   # an unbridge's way back
    if clean_ and not planned_ and not back_run:
        nx = mig_next(a, st, res, vm_rows)
        if nx:
            print("")
            print("  NEXT")
            for net_, txt_ in nx:
                print("    %-18s %s" % (net_, txt_))
    if rows:
        rp = mig_reports(cfg, site, rows, st, os.path.dirname(st_path), outdir)
        print("  reports: %s" % ", ".join(os.path.basename(x) for x in rp))
    print("  evidence: %s" % outdir)
    rc = 1 if (fails or tally["ERROR"] or leak or stopped or held or (a.commit and hard)
               or any(p["state"] == "FAIL" for p in post)) else 0
    if rc == 0 and a.detailed_exitcode and not a.commit and (pending or tag_pending or tep_pending or move_pending
                                                              or btag_pending or blocked):
        rc = 2                         # plan with changes pending, as terraform plan -detailed-exitcode
    return rc


# ---------------------------------------------------------------- migpath: the way back from each commit
def _mig_some(xs, k=6):
    xs = sorted(set(str(x) for x in xs if x), key=lambda x: (len(x), x))
    return ", ".join(xs[:k]) + (" (+%d more)" % (len(xs) - k) if len(xs) > k else "")


def mig_undo(a, site, results=(), vm_rows=(), tep_rows=(), res=None, extra=None):
    """After a commit that wrote: the one command, or the one change to the config, that takes it back.
    Retire is the one step without a way back: said so."""
    S = " --site %s" % a.site if getattr(a, "site", None) else ""
    T = " --test" if getattr(a, "test", False) else ""
    rm = bool(getattr(a, "remove", False))
    target = mig_target(a)
    out = []
    if extra:
        return list(extra)
    drops = {r["segment"] for r in (res or {}).get("drop") or []}
    sub = {r["segment"]: r.get("subnet") or r["segment"] for r in list((res or {}).get("rows") or []) + list(
        (res or {}).get("drop") or [])}
    wrote = [x for x in results or [] if x["action"] in ("ADD", "UPDATE", "DELETE") and x.get("http") in (200, 201, 202, 204)]
    if a.mode == "build":
        built = {sub.get(x.get("segment"), x.get("segment")) for x in wrote if x.get("segment") and x["segment"] not in drops
                 and x["kind"] in ("segment", "segment-bridge")}
        apart = {sub.get(x.get("segment"), x.get("segment")) for x in wrote if x.get("segment") in drops}
        if built and getattr(a, "test", False):
            out.append("fp%s --test --remove --commit: the test build apart, Blue's bridge first, then Green's segment" % S)
        elif built:
            out.append("list %s in mig_skip_%s (or the scope item, for all of it), then fp%s and fp%s --commit --expect "
                       "<the digest it prints>: Blue's bridge comes off first, then Green's segment" % (_mig_some(built), site, S, S))
        if apart and rm:
            out.append("fp%s --test --commit: the test build again" % S)
        elif apart:
            out.append("take %s out of mig_skip_%s (back in mig_scope_%s), then fp%s and fp%s --commit --expect <the digest "
                       "it prints>: built again" % (_mig_some(apart), site, site, S, S))
        if any(x["kind"] == "bridge-profile" and x["action"] == "ADD" for x in wrote):
            out.append("the bridge profiles go with the bridge edges: fp%s --edges --remove --commit, once no segment "
                       "uses them" % S)
        mv = [r for r in vm_rows or [] if r["kind"] == "vm-move" and r["action"] == "UPDATE"]
        bk = [r for r in vm_rows or [] if r["kind"] == "vm-return" and r["action"] == "UPDATE"]

        def named(rows_):               # the wave files they came from, when every one came from a file
            w_ = {r_.get("wave") for r_ in rows_}
            return ", ".join(sorted(w_)) if None not in w_ else _mig_some([r_["id"] for r_ in rows_])

        def arg(rows_):                 # the --vm that names them all: their wave files, else every name
            w_ = {r_.get("wave") for r_ in rows_}
            return ",".join(sorted(w_)) if None not in w_ else ",".join(sorted({r_["id"] for r_ in rows_}))
        segrow_ = {r_["segment"]: r_ for r_ in (res or {}).get("rows") or []}

        def listed(sel_, r_):
            return _mig_vm_listed(sel_ or [], r_["id"], segrow_.get(r_.get("segment")) or {"segment": r_.get("segment")})
        mvd = [r_ for r_ in mv if listed(getattr(a, "move_cfg", None), r_)]     # move_vms would take them again
        mvc = [r_ for r_ in mv if r_ not in mvd]
        if mvc:
            out.append("fp%s%s --return --vm %s --commit: back to Blue, each where it was" % (S, T, arg(mvc)))
        if mvd:                         # move_vms would take them again: return_vms wins over it
            out.append("list %s in mig_return_vms_%s, then fp%s%s --commit: back to Blue, where they were"
                       % (named(mvd), site, S, T))
        # a VM the config's return_vms lists stays on Blue until it is taken out of the list (return_vms wins)
        cfgd = [r_ for r_ in bk if listed(getattr(a, "ret_cfg", None), r_)]
        cli = [r_ for r_ in bk if r_ not in cfgd]
        if cli:
            out.append("fp%s%s --move --vm %s --commit: to Green again" % (S, T, arg(cli)))
        if cfgd and T:                  # a --test run does not read move_vms: --move --vm names them
            out.append("take %s out of mig_return_vms_%s, then fp%s --test --move --vm %s --commit: to Green again"
                       % (named(cfgd), site, S, arg(cfgd)))
        elif cfgd:
            out.append("take %s out of mig_return_vms_%s, then fp%s --move --vm %s --commit: to Green again"
                       % (named(cfgd), site, S, arg(cfgd)))
        if any(r["action"] == "UPDATE" for r in tep_rows or []):
            out.append("tunnel pool gateways: a repair, kept. Each pool had none; the tool never removes one")
    elif a.mode == "cutover":
        out.append("fp%s%s --rollback %s --commit: bridges kept, Green OFF, Blue ON" % (S, T, target))
    elif a.mode == "rollback":
        out.append("fp%s%s --cutover %s --commit: Blue OFF, Green ON again" % (S, T, target))
    elif a.mode == "unbridge":
        out.append("fp%s%s --cutover %s --commit: both bridges back, Green stays the gateway (or --rollback %s: "
                   "bridges back and Blue the gateway)" % (S, T, target, target))
    elif a.mode == "retire":
        out.append("none: Blue's segment is deleted. Retire is the one step with no way back")
    return out


def mig_next(a, st, res, vm_rows=()):
    """[(subnet, the one command forward)] for each subnet a run acted on: a step's own subnet; for a build run,
    the subnets of the VMs it moved or named. Read from the state as the run left it: VMs still on Blue first,
    then the cutover, then the unbridge once the subnet has run clean on Green, then done."""
    S = " --site %s" % a.site if getattr(a, "site", None) else ""
    T = " --test" if getattr(a, "test", False) else ""
    rows = list(res.get("rows") or [])
    if a.mode == "build":
        segs = {r.get("segment") for r in vm_rows or [] if r.get("segment") and r.get("kind") in ("vm-move", "vm-return")}
        rows = [r for r in rows if r["segment"] in segs]
    out = []
    for r in rows:
        s_ = (st.get("segments") or {}).get(r["segment"]) or {}
        status = s_.get("status") or "planned"
        on_blue = sorted(n for n, v in (s_.get("vms") or {}).items() if v.get("where") == "blue")
        net = r.get("subnet") or r["segment"]
        if status == "built" and on_blue:
            txt = "%d VM(s) still on Blue (%s): move them first; then fp%s%s --cutover %s" % (
                len(on_blue), _mig_some(on_blue, 4), S, T, net)
        elif status == "built":
            txt = "fp%s%s --cutover %s" % (S, T, net)
        elif status == "cutover" and on_blue:
            txt = "%d VM(s) still on Blue (%s): move them first; then fp%s%s --unbridge %s" % (
                len(on_blue), _mig_some(on_blue, 4), S, T, net)
        elif status == "cutover":
            txt = "fp%s%s --unbridge %s   once it has run clean on Green" % (S, T, net)
        elif status == "unbridged":
            txt = "done: Green is its gateway, no bridge left"
        elif status == "retired":
            txt = "done: Blue's segment is retired"
        elif status == "NO GATEWAY":
            txt = "no gateway: fp%s%s --cutover %s --commit finishes it, or fp%s%s --rollback %s --commit" % (
                S, T, net, S, T, net)
        else:
            txt = "not bridged yet (%s): its build comes first%s" % (
                status, ": fp%s --test --commit" % S if T else ", in a planned window")
        out.append((net, txt))
    return out


def mig_print_undo(ctx, outdir, lines):
    """The way back, printed after the commit, kept in the evidence (undo.txt) and in the run's journal line."""
    lines = [_mig_shown(x) for x in lines or []]
    ctx["undo"] = lines
    if not lines:
        return
    print("")
    print("  UNDO")
    for x in lines:
        print("    %s" % x)
    if outdir:
        with open(os.path.join(outdir, "undo.txt"), "w") as fh:
            fh.write("\n".join(lines) + "\n")


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(prog=TOOL, formatter_class=argparse.RawDescriptionHelpFormatter,
                                 description=__doc__.split("Usage")[0])
    ap.add_argument("--version", action="version", version="%s %s" % (TOOL, __version__))
    ap.add_argument("--write-example-config", metavar="PATH", help="write an example config and exit")
    sub = ap.add_subparsers(dest="cmd")

    c = sub.add_parser("collect", help="collect from this node (or a remote Ops host)")
    c.add_argument("--role", choices=["ops", "sddc", "fleet", "remote"], help="override auto-detect")
    c.add_argument("--tag", help="bundle label, e.g. the VCF instance name")
    c.add_argument("--host", help="API host (default localhost)")
    c.add_argument("--config", help="config file (YAML/JSON)")
    c.add_argument("--outdir")
    c.add_argument("--plan", action="store_true", help="dry run: print every call/query, execute nothing")
    c.set_defaults(func=cmd_collect)

    r = sub.add_parser("run", help="ONE command from the Operations node: collect everything, "
                                   "compare, produce one tarball")
    r.add_argument("--host", help="Operations API host (default localhost)")
    r.add_argument("--config", help="config file (YAML/JSON)")
    r.add_argument("--outdir")
    r.add_argument("--plan", action="store_true", help="dry run: print every call, execute nothing")
    r.add_argument("--skip-ssh", action="store_true",
                   help="skip every SSH layer (other Ops nodes, SDDC DB, ESXi) regardless of config")
    r.set_defaults(func=cmd_run)

    fa = sub.add_parser("fedapply", help="converge the stretched Tier-0 north-south config on the "
                                         "Global Manager (idempotent; plans unless --commit)")
    fa.add_argument("bundle", nargs="?", help="optional: reuse the plan from a previous `run` "
                                              "directory instead of collecting again")
    fa.add_argument("--host", help="Global Manager FQDN/VIP (default: nsx_gm_host from config)")
    fa.add_argument("--config", help="config file (YAML/JSON)")
    fa.add_argument("--outdir")
    fa.add_argument("--commit", action="store_true",
                    help="actually write. Without this nothing is changed.")
    fa.add_argument("--verify", action="store_true",
                    help="read-only verdict on the federation as built: Tier-0 placement, "
                         "route redistribution, uplinks, MTU, uRPF, teaming, RTEP, BGP and "
                         "realization. Proposes nothing and writes nothing. Pair with "
                         "--verify-edges to judge Tier-0 placement from the datapath.")
    fa.add_argument("--replay", metavar="DIR",
                    help="run --verify against a saved bundle with no network calls at all. "
                         "Takes a federation_<ts> directory or a parent holding several. "
                         "Use it to judge an archive someone sent, and to prove a change "
                         "against real data before running it anywhere.")
    fa.add_argument("--no-edge-bgp", action="store_true",
                    help="skip the per-node BGP summary during --verify-edges. The RTEP and "
                         "gateway reads are plain one-shot commands; the BGP read needs an "
                         "interactive session and is the slow one.")
    fa.add_argument("--verify-edges", action="store_true",
                    help="SSH each edge node (read-only: get rteps, get gateways) and compare "
                         "the datapath with what the managers report")
    fa.add_argument("--fix-rtep", action="store_true",
                    help="configure RTEP on any edge node missing it (writes to the LOCAL "
                         "MANAGER; requires --commit to actually write)")
    fa.add_argument("--diagnose", action="store_true",
                    help="read-only: report realization status and the real alarm text for "
                         "every object already on the stretched Tier-0")
    fa.set_defaults(func=cmd_fedapply)

    mp = sub.add_parser("migpath", help="Blue GM segment -> Green GM segment over two edge bridges "
                                         "(idempotent; plans unless --commit)",
                        description="The config says what to do: mig_scope_<site> (all: every segment Blue has at the site; or CIDRs, segment names, t1:<Blue Tier-1>), "
                                    "mig_skip_<site> (never bridge; a built segment listed there is taken apart), "
                                    "mig_move_vms_<site> (VMs to move to Green), mig_return_vms_<site> (VMs back to Blue; once: --return --vm); "
                                    "any of these lists can name a .csv, a wave, read in place. "
                                    "Every run reads Blue and Green, plans, and with --commit converges. Run it again "
                                    "until it says No changes. Every commit prints its UNDO.")
    mp.add_argument("--config", help="config file (YAML/JSON)")
    mp.add_argument("--outdir")
    mp.add_argument("--site", help="Green location (default: first of mig_sites)")
    mp.add_argument("--by-site", action="store_true",
                    help="rewrite the config with every site's values, sign-ins included, in that site's block (only "
                         "the Global Managers stay above the sites); every value checked to read back the same, the "
                         "old file kept beside it; then stop")
    mp.add_argument("--set", metavar="NAME[=VALUE]",
                    help="put one value in the config by its full name, e.g. sites.<site>.blue.bridge.admin_password "
                         "(a password is asked for twice, never shown); nothing else in the file changes; then stop")
    # gone in 1.15.0 (the plan is derived each run, the decisions are in the config): kept only to say so
    mp.add_argument("segments", nargs="*", help=argparse.SUPPRESS)
    mp.add_argument("--plan", help=argparse.SUPPRESS)
    mp.add_argument("--inventory", action="store_true", help=argparse.SUPPRESS)
    mp.add_argument("--assign", help=argparse.SUPPRESS)
    mp.add_argument("--skip", action="store_true", help=argparse.SUPPRESS)
    mp.add_argument("--wave", help=argparse.SUPPRESS)
    mp.add_argument("--router-mac", action="store_true",
                    help="set mig_router_mac on every Green Local Manager and read it back (plans unless --commit)")
    mp.add_argument("--edges", action="store_true",
                    help="build the bridge edges on each side from mig_bridge_edge_template: bridge zone, trunk port "
                         "group, two edges, edge cluster (plans unless --commit; Blue only when Blue writes are on)")
    mp.add_argument("--remove", action="store_true",
                    help="take apart what one action built, in reverse order and only what this tool made: "
                         "--edges --remove (bridge profiles, edge cluster, DRS rule, edges, trunk port group, zone), "
                         "--test --remove (the test build), --test --setup --remove (the Blue test segment). A segment "
                         "of the scope goes back by listing it in mig_skip_<site>, a VM by --return --vm")
    mp.add_argument("--vm", action="append", default=[], metavar="NAME[,NAME]",
                    help="with --move: only these VMs (comma-separated, repeat --vm, or a wave .csv), on top of "
                         "mig_move_vms_<site>; the rest stay on Blue. With --return: the VMs to send back")
    mp.add_argument("--return", dest="back", action="store_true",
                    help="with --vm: send those VMs back to Blue, each where it left (vCenter, cluster, host, "
                         "datastore), its Blue NSX tags put back; one run, nothing to change in the config. The "
                         "way back of --move --vm (plans unless --commit)")
    mp.add_argument("--move", action="store_true",
                    help="with a build (on by itself when mig_move_vms_<site> lists a VM): move VMs still on Blue "
                         "to Green by cross vCenter vMotion, after "
                         "setting %s on both vCenters. Lands them on the Green vCenter's only cluster and the datastore "
                         "all its hosts share (vSAN first), unless mig_green_cluster_<site> / mig_green_datastore_<site> "
                         "name others, in the folder of the same path as on Blue (made where Green has none) "
                         "(plans unless --commit)" % "config.vpxd.network.allowVmotionBetweenLogicalSwitches")
    mp.add_argument("--commit", action="store_true", help="actually write. Without this nothing is changed.")
    mp.add_argument("--expect", metavar="DIGEST",
                    help="with --commit: write only the changes of the plan a plan run printed as DIGEST, on "
                         "objects unchanged since that run read them, or what is left of it after a stop part "
                         "way (none: a plan with no changes). Anything else, nothing is written")
    mp.add_argument("--detailed-exitcode", action="store_true",
                    help="plan runs exit 0 with no changes, 2 with changes pending, 1 on a failure "
                         "(as terraform plan -detailed-exitcode)")
    mp.add_argument("--verify", action="store_true",
                    help="read-only: SSH both bridge pairs, `get bridge`, one active and one standby per VLAN")
    mp.add_argument("--check-leaves", action="store_true",
                    help="read-only: SSH the leaves, transit VLANs on the listed ports, no SVI, no VLAN lost; "
                         "writes the exact NVUE lines per leaf")
    mp.add_argument("--cutover", metavar="SUBNET", help="Blue Connectivity OFF, then Green ON, for one segment "
                                                         "(its subnet, name or id)")
    mp.add_argument("--unbridge", metavar="SUBNET", help="remove both bridges from a cut-over segment")
    mp.add_argument("--rollback", metavar="SUBNET", help="bridges back, Green OFF, Blue ON")
    mp.add_argument("--retire", metavar="SUBNET",
                    help="delete Blue's segment once it is cut over, unbridged and empty on Blue")
    mp.add_argument("--legacy-gw-off", action="store_true",
                    help="for a source outside NSX: its gateway has been switched off by hand")
    mp.add_argument("--test", action="store_true",
                    help="act only on mig_test_segments. Blue writes are limited to the test segment and "
                         "the Blue bridge profile; every commit run proves nothing else on Blue changed")
    mp.add_argument("--setup", action="store_true",
                    help="with --test: create the Blue test segment from mig_test_subnet and "
                         "mig_test_blue_tier1")
    mp.add_argument("--baseline", action="store_true",
                    help="record Blue now as the baseline of this scope (the config's, or --test). The first "
                         "run of a scope records one by itself")
    mp.add_argument("--impact", metavar="DIR", nargs="?", const="@state",
                    help="read-only: compare Blue now with the recorded baseline of this scope, or with the "
                         "snapshot in an earlier run's evidence directory. Any change outside the scope fails; "
                         "new open Blue alarms are listed")
    mp.set_defaults(func=cmd_migpath)

    m = sub.add_parser("compare", help="compare bundles and flag deltas")
    m.add_argument("bundles", nargs="+", help="bundle .tgz files or directories")
    m.add_argument("--config", help="config file (for expected_hosts / rotation_warn_days)")
    m.add_argument("--outdir")
    m.set_defaults(func=cmd_compare)

    # single-file agent mode: `python3 - _bridge_json < fleetparity.py` on a remote node
    if len(sys.argv) > 1 and sys.argv[1] == "_bridge_json":
        print(json.dumps(analyse_bridge_logs(None), default=str))
        return
    if len(sys.argv) > 1 and sys.argv[1] == "_sddc_json":
        print(json.dumps(sddc_agent_json(), default=str))
        return
    a = ap.parse_args()
    if a.write_example_config:
        with open(a.write_example_config, "w") as fh:
            fh.write(EXAMPLE_CONFIG)
        os.chmod(a.write_example_config, 0o600)
        print("wrote %s (mode 600)" % a.write_example_config)
        return
    if not a.cmd:
        ap.print_help()
        sys.exit(2)
    a.func(a)


if __name__ == "__main__":
    main()
