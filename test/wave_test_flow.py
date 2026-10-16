#!/usr/bin/env python3
"""1.21.0, the customer's three steps with --test on an existing segment (as the second site's net-10.2.125.0-24), while the
config's scope is wider: #1 --move --vm wave.csv, #2 --cutover (refused until every VM is on Green), #3 --unbridge,
then each way back. Only the test segment is written. Mocks already running."""
import copy, glob, json, os, re, ssl, subprocess, sys, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
FP = os.path.join(HERE, "..", "fleetparity.py")
CTX = ssl._create_unverified_context()
PORT = {"green": 9443, "blue": 9444, "lm": 9445, "blue-lm": 9446, "lm2": 9447, "vc-blue": 9448, "vc-blue2": 9449,
        "vc-green": 9450}
WORLD = os.path.join(HERE, "world.json")


def mock(who, path, body=None):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request("https://127.0.0.1:%d%s" % (PORT[who], path), data=data, method="POST",
                                 headers={"Content-Type": "application/json"})
    return json.load(urllib.request.urlopen(req, context=CTX))


def run(label, cfg, *args, show=r"\[(ADD|UPDATE|DELETE|BLOCKED|ERROR|NEXT)|\[(FAIL|WARN)\]|empty on Blue|UNDO|^    |No changes|"
                                r"STOPPED|NOT DONE|Traceback|refus|all in scope|objects? changed"):
    p = subprocess.run([sys.executable, FP, "migpath", "--config", os.path.join(HERE, cfg)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=HERE, stdin=subprocess.DEVNULL)
    out = p.stdout.decode()
    print("=" * 100)
    print("%s   rc=%s   (%s)" % (label, p.returncode, " ".join(args)))
    for l in out.splitlines():
        if re.search(show, l) and not re.search(r"T0-STRETCHED.* uplinks|Blue vCenters at|Local Manager VM ports|overlay tunnels|"
                                                 r"port groups +none for", l):
            print(l[:210])
    if "Traceback" in out:
        print(out[-2500:])
    return p.returncode, out


A = open(os.path.join(HERE, "env.auto.yaml")).read()


def cfgv(name, **kv):
    s_ = A
    for k, v in kv.items():
        s_ = re.sub(r"(?m)^%s:.*$" % re.escape(k), "%s: %s" % (k, v), s_) if re.search(r"(?m)^%s:" % re.escape(k), s_) \
            else s_.rstrip("\n") + "\n%s: %s\n" % (k, v)
    open(os.path.join(HERE, name), "w").write(s_)
    os.chmod(os.path.join(HERE, name), 0o600)
    return name


def green_has(seg):
    return "/segments/%s" % seg in mock("green", "/mock/state")["S"]


def blue_bridges(seg):
    return (mock("blue", "/mock/state")["S"].get("/segments/%s" % seg) or {}).get("bridge_profiles")


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
for i, n in enumerate(("app-vm-01", "app-vm-02")):
    mock("vc-blue", "/mock/vm", {"name": n, "network": "app-210", "ip": "10.30.10.%d" % (11 + i)})
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-1", "tags": [{"scope": "app", "tag": "billing"}]})
open(os.path.join(HERE, "wave1.csv"), "w").write("vm,subnet,owner\napp-vm-01,10.30.10.0/24,billing\napp-vm-02,10.30.10.0/24,billing\n")

# the scope is wider than the test segment (as the second site's 10.2.0.0/16): --test runs must write the test segment only
C1 = cfgv("env.t1.yaml", **{"mig_test_segments_site-a": "[app-210]", "mig_scope_site-a": "[app-210, db-211]",
                           "mig_move_tag_wait": "0"})
run("test build", C1, "--test", "--commit")
print("   Green has app-210:", green_has("app-210"), "| Green has db-211 (must be False):", green_has("db-211"))
run("#2 before #1: refused while its VMs are on Blue", C1, "--test", "--cutover", "app-210")
run("#2 before #1, --commit: writes nothing", C1, "--test", "--cutover", "app-210", "--commit")
print("   Blue connectivity on app-210 (must stay ON):",
      ((mock("blue", "/mock/state")["S"].get("/segments/app-210") or {}).get("advanced_config") or {}).get("connectivity", "ON"))
mock("vc-green", "/mock/net", {"name": "app-210"})
mock("lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-g-1"})
mock("lm", "/mock/fvm", {"name": "app-vm-02", "external_id": "ext-g-2"})
run("#1 plan: --move --vm wave1.csv", C1, "--test", "--move", "--vm", "wave1.csv")
run("#1 commit", C1, "--test", "--move", "--vm", "wave1.csv", "--commit")
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "remove": True})
run("#1 again: nothing to do", C1, "--test", "--move", "--vm", "wave1.csv", "--commit")
run("#2 commit", C1, "--test", "--cutover", "app-210", "--commit")
run("#3 commit", C1, "--test", "--unbridge", "app-210", "--commit")
print("   Blue bridges on app-210 after #3:", blue_bridges("app-210"))
run("#3 back: --cutover puts both bridges back", C1, "--test", "--cutover", "app-210", "--commit")
print("   Blue bridges on app-210:", blue_bridges("app-210"))
run("#2 back: --rollback", C1, "--test", "--rollback", "app-210", "--commit")
C2 = cfgv("env.t2.yaml", **{"mig_test_segments_site-a": "[app-210]", "mig_scope_site-a": "[app-210, db-211]",
                           "mig_return_vms_site-a": "[wave1.csv]", "mig_move_tag_wait": "0"})
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-3", "tags": []})
run("#1 back: return_vms [wave1.csv], fp --test --commit", C2, "--test", "--commit")
run("again: nothing to do", C2, "--test", "--commit")
print("   Green has db-211 at the end (must be False):", green_has("db-211"))
for f in ("env.t1.yaml", "env.t2.yaml", "wave1.csv"):
    os.remove(os.path.join(HERE, f))
