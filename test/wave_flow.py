#!/usr/bin/env python3
"""1.21.0, the customer's three steps on the mocks: #1 a wave .csv moves the VMs, #2 the routing moves only once
every VM is on Green, then the way back: rollback, and the wave returned. Mocks already running."""
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


def run(label, cfg, *args, show=r"\[(ADD|UPDATE|DELETE|BLOCKED|ERROR|NEXT|HELD)|\[(FAIL|WARN)\]|empty on Blue|UNDO|^  NEXT|^  HELD|^    |No changes|STOPPED|NOT DONE|Traceback"):
    p = subprocess.run([sys.executable, FP, "migpath", "--config", os.path.join(HERE, cfg)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=HERE, stdin=subprocess.DEVNULL)
    out = p.stdout.decode()
    print("=" * 100)
    print("%s   rc=%s" % (label, p.returncode))
    for l in out.splitlines():
        if re.search(show, l) and not re.search(r"T0-STRETCHED.* uplinks|Blue vCenters at|Local Manager VM ports|overlay tunnels|"
                                                 r"port groups +none for", l):
            print(l[:210])
    if "Traceback" in out:
        print(out[-2500:])
    return p.returncode, out


def build(label, cfg, *args):
    """A change to NSX itself outside --test (1.23.0): its plan, then --commit --expect <that plan's digest>."""
    rc, out = run(label + ": plan", cfg, *args)
    m = re.search(r"plan (\S+): \d+ change", out)
    if not m:
        return rc, out
    return run(label + ": --commit --expect", cfg, *(list(args) + ["--commit", "--expect", m.group(1)]))


A = open(os.path.join(HERE, "env.auto.yaml")).read()


def cfgv(name, **kv):
    s_ = A
    for k, v in kv.items():
        s_ = re.sub(r"(?m)^%s:.*$" % re.escape(k), "%s: %s" % (k, v), s_) if re.search(r"(?m)^%s:" % re.escape(k), s_) \
            else s_.rstrip("\n") + "\n%s: %s\n" % (k, v)
    open(os.path.join(HERE, name), "w").write(s_)
    os.chmod(os.path.join(HERE, name), 0o600)
    return name


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

C1 = cfgv("env.w1.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_vms_site-a": "[wave1.csv]",
                           "mig_move_tag_wait": "0"})
build("build; the wave waits for it", C1)
run("#2 before the wave moved: the routing must not move", C1, "--cutover", "app-210")
mock("vc-green", "/mock/net", {"name": "app-210"})
mock("lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-g-1"})
mock("lm", "/mock/fvm", {"name": "app-vm-02", "external_id": "ext-g-2"})
run("#1 the wave", C1, "--commit")
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "remove": True})
run("#2 the wave is on Green: plan", C1, "--cutover", "app-210")
run("#2 commit", C1, "--cutover", "app-210", "--commit")
run("#2 back: rollback", C1, "--rollback", "app-210", "--commit")
C2 = cfgv("env.w2.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_vms_site-a": "[wave1.csv]",
                           "mig_return_vms_site-a": "[wave1.csv]", "mig_move_tag_wait": "0"})
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-3", "tags": []})
run("#1 back: the wave returned", C2, "--commit")
run("again: nothing to do", C2, "--commit")
rp = open(os.path.join(HERE, "migpath_vms_site-a.csv")).read()
print("vms report:\n" + "\n".join(l for l in rp.splitlines() if "app-vm" in l or l.startswith("site")))
for f in ("env.w1.yaml", "env.w2.yaml", "wave1.csv"):
    os.remove(os.path.join(HERE, f))
