#!/usr/bin/env python3
"""1.20.0: forward, then every way back, against the mocks (already running). Prints what each run did."""
import copy, json, os, re, ssl, subprocess, sys, urllib.request, glob

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


def run(label, cfg, *args):
    p = subprocess.run([sys.executable, FP, "migpath", "--config", os.path.join(HERE, cfg)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=HERE, stdin=subprocess.DEVNULL)
    out = p.stdout.decode()
    keep = [l for l in out.splitlines() if re.match(r"\s+\[(ADD|UPDATE|DELETE|BLOCKED|ERROR|NEXT|UNCHANGED|HELD)", l)
            or re.match(r"\s+\[(FAIL|WARN)\]", l) or l.startswith("  UNDO") or l.startswith("  NEXT") or l.startswith("  HELD") or l.startswith("    ")
            or "No changes" in l or "plan " in l[:8] or "Traceback" in l or "Error" in l[:40] or "STOPPED" in l
            or "NOT DONE" in l or "BLUE CHANGED" in l or l.startswith("  Blue: ")]
    print("=" * 100)
    print("%s   rc=%s" % (label, p.returncode))
    for l in keep:
        if "line" in l and "File" in l:
            print(l)
        else:
            print(l[:200])
    if "Traceback" in out:
        print(out[-3000:])
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
        if re.search(r"(?m)^%s:" % re.escape(k), s_):
            s_ = re.sub(r"(?m)^%s:.*$" % re.escape(k), "%s: %s" % (k, v), s_)
        else:
            s_ = s_.rstrip("\n") + "\n%s: %s\n" % (k, v)
    open(os.path.join(HERE, name), "w").write(s_)
    os.chmod(os.path.join(HERE, name), 0o600)
    return name


for w_ in PORT:
    mock(w_, "/mock/reset")
for f in glob.glob(os.path.join(HERE, "migpath_state_*")) + glob.glob(os.path.join(HERE, "mig_plan_site-a*.csv")):
    os.remove(f)
LEAF = {"bridge_vids": list(range(3101, 3200)) + [221, 222, 225], "ports": {"swp10": None, "swp11": None, "peerlink": None},
        "svis": ["vlan221-v0"]}
json.dump({"leaves": {"leaf-a1.example.com": copy.deepcopy(LEAF), "leaf-a2.example.com": copy.deepcopy(LEAF)}}, open(WORLD, "w"))
for n in ("green-a-bdg01", "green-a-bdg02"):
    mock("lm", "/mock/attach", {"node": n, "tz": "uuid-tz-br"})
for w_ in ("lm", "lm2"):
    mock(w_, "/mock/gc", {"vdr_mac": "02:50:56:56:44:62"})

# forward: the Blue test segment, then the test build
run("test setup", "env.auto.yaml", "--test", "--setup", "--commit")
run("test build", "env.auto.yaml", "--test", "--commit")
run("test build again (idempotent)", "env.auto.yaml", "--test", "--commit")
# back: the test build apart, then the Blue test segment
run("test remove: plan", "env.auto.yaml", "--test", "--remove")
run("test remove: commit", "env.auto.yaml", "--test", "--remove", "--commit")
run("test remove again (idempotent)", "env.auto.yaml", "--test", "--remove", "--commit")
run("setup remove: commit", "env.auto.yaml", "--test", "--setup", "--remove", "--commit")
run("setup remove again (idempotent)", "env.auto.yaml", "--test", "--setup", "--remove", "--commit")
# a scope build, then skip undoes one segment
segs = sorted(s["id"] for s in mock("blue", "/mock/state")["S"].values() if isinstance(s, dict) and s.get("id")
              and "/segments/" in str(s.get("path")))
print("Blue segments in the mock:", segs[:12])
