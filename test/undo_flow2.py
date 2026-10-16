#!/usr/bin/env python3
"""1.20.0: a scope build with a VM moved, then every way back: the VM returned (its Blue tags put back), a segment
taken apart by skip and built again, the bridge edges held while anything is bridged. Mocks already running."""
import copy, glob, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from undo_flow import mock, run, build, cfgv, PORT, HERE, WORLD  # noqa: E402  (undo_flow's own flow runs on import)

print("\n" + "#" * 100 + "\n# scope flow\n" + "#" * 100)
for w_ in PORT:
    mock(w_, "/mock/reset")
for f in glob.glob(os.path.join(HERE, "migpath_state_*")):
    os.remove(f)
LEAF = {"bridge_vids": list(range(3101, 3200)) + [221, 222, 225], "ports": {"swp10": None, "swp11": None, "peerlink": None},
        "svis": ["vlan221-v0"]}
json.dump({"leaves": {"leaf-a1.example.com": copy.deepcopy(LEAF), "leaf-a2.example.com": copy.deepcopy(LEAF)}}, open(WORLD, "w"))
for n in ("green-a-bdg01", "green-a-bdg02"):
    mock("lm", "/mock/attach", {"node": n, "tz": "uuid-tz-br"})
for w_ in ("lm", "lm2"):
    mock(w_, "/mock/gc", {"vdr_mac": "02:50:56:56:44:62"})
mock("vc-blue", "/mock/vm", {"name": "app-vm-01", "network": "app-210", "ip": "10.30.10.11"})
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-2", "tags": [{"scope": "app", "tag": "billing"}]})

C1 = cfgv("env.u1.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_vms_site-a": "[app-vm-01]",
                           "mig_move_tag_wait": "0"})
build("build (moves wait for it)", C1)
mock("lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-g-2"})         # Green's NSX sees it once moved
mock("vc-green", "/mock/net", {"name": "app-210"})                          # Green's port group for app-210
run("move app-vm-01", C1, "--commit")
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "remove": True})               # Blue's NSX lost it, and its tags
st = json.load(open(os.path.join(HERE, "migpath_state_site-a.json")))
print("state after the move:", json.dumps(st["segments"]["app-210"]["vms"]["app-vm-01"], sort_keys=True))
run("again: nothing to do", C1, "--commit")

C2 = cfgv("env.u2.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_vms_site-a": "[app-vm-01]",
                           "mig_return_vms_site-a": "[app-vm-01]", "mig_move_tag_wait": "0"})
run("return: plan", C2)
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-3", "tags": []})   # back in Blue's NSX, no tags
run("return: commit", C2, "--commit")
mock("lm", "/mock/fvm", {"name": "app-vm-01", "remove": True})
st = json.load(open(os.path.join(HERE, "migpath_state_site-a.json")))
print("state after the return:", json.dumps(st["segments"]["app-210"]["vms"]["app-vm-01"], sort_keys=True))
print("Blue NSX tags now:", [v.get("tags") for v in mock("blue-lm", "/mock/state")["FVM"].values()])
print("vMotions: Blue vc", [(m["vm"], m["uuid"]) for m in mock("vc-blue", "/mock/opts")["moves"]],
      "Green vc", [(m["vm"], m["uuid"], m["host"]) for m in mock("vc-green", "/mock/opts")["moves"]])
run("return again: nothing to do", C2, "--commit")

C3 = cfgv("env.u3.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_skip_site-a": "[db-211]",
                           "mig_return_vms_site-a": "[app-vm-01]", "mig_move_tag_wait": "0"})
build("skip db-211", C3)
print("db-211 now: Green", "/segments/db-211" in mock("green", "/mock/state")["S"],
      "Blue bridges", (mock("blue", "/mock/state")["S"].get("/segments/db-211") or {}).get("bridge_profiles"))
run("skip again: nothing to do", C3, "--commit")
run("edges --remove while app-210 is bridged: plan", C3, "--edges", "--remove")
C4 = cfgv("env.u4.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_tag_wait": "0"})
build("skip taken out: db-211 built again", C4)
for f in ("env.u1.yaml", "env.u2.yaml", "env.u3.yaml", "env.u4.yaml"):
    os.remove(os.path.join(HERE, f))
