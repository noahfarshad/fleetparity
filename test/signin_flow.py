#!/usr/bin/env python3
"""1.22.0: the config rewritten with every sign-in in its site (fp --by-site), then a --test build and a wave
move against the mocks: a Blue bridge edge that refuses the password holds the move, and the held row names
the exact setting to fix. Mocks already running."""
import copy, glob, json, os, re, shutil, ssl, subprocess, sys, urllib.request

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


def run(label, cfg, *args, show=r"\[(ADD|UPDATE|DELETE|BLOCKED|ERROR)|\[(FAIL)\]|refused|rewritten|into each|nothing to do|"
                                r"No changes|Traceback|bridge VLAN|get bridge"):
    p = subprocess.run([sys.executable, FP, "migpath", "--config", os.path.join(HERE, cfg)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=HERE, stdin=subprocess.DEVNULL)
    out = p.stdout.decode()
    print("=" * 100)
    print("%s   rc=%s   (%s)" % (label, p.returncode, " ".join(args)))
    for l in out.splitlines():
        if re.search(show, l) and "empty on Blue at SITE-B" not in l:
            print(l[:230])
    if "Traceback" in out:
        print(out[-2500:])
    return p.returncode, out


for w_ in PORT:
    mock(w_, "/mock/reset")
for f in glob.glob(os.path.join(HERE, "migpath_state_*")):
    os.remove(f)
LEAF = {"bridge_vids": list(range(3101, 3200)) + [221, 222, 225], "ports": {"swp10": None, "swp11": None, "peerlink": None},
        "svis": ["vlan221-v0"]}
world = {"leaves": {"leaf-a1.example.com": copy.deepcopy(LEAF), "leaf-a2.example.com": copy.deepcopy(LEAF)}}
json.dump(world, open(WORLD, "w"))
for n in ("green-a-bdg01", "green-a-bdg02"):
    mock("lm", "/mock/attach", {"node": n, "tz": "uuid-tz-br"})
for w_ in ("lm", "lm2"):
    mock(w_, "/mock/gc", {"vdr_mac": "02:50:56:56:44:62"})
for i, n in enumerate(("app-vm-01", "app-vm-02")):
    mock("vc-blue", "/mock/vm", {"name": n, "network": "app-210", "ip": "10.30.10.%d" % (11 + i)})
open(os.path.join(HERE, "wave1.csv"), "w").write("vm,subnet\napp-vm-01,10.30.10.0/24\napp-vm-02,10.30.10.0/24\n")

# the flat test config, rewritten with every sign-in in its site
V3 = os.path.join(HERE, "env.v3.yaml")
shutil.copy(os.path.join(HERE, "env.auto.yaml"), V3)
os.chmod(V3, 0o600)
run("rewrite: every sign-in into its site", "env.v3.yaml", "--by-site")
run("rewrite again: nothing to do", "env.v3.yaml", "--by-site")
t = open(V3).read()
print("in the file:", [l.strip() for l in t.splitlines() if re.search(r"admin_password|lm_password|vc_password", l)][:6])
t = t.replace("test_segments: [mig-test]", "test_segments: [app-210]")
t = re.sub(r"(?m)^(  site-a:.*\n)", r"\1    scope: [app-210, db-211]\n    move_tag_wait_unused: x\n", t, count=1)
t = t.replace("    move_tag_wait_unused: x\n", "")
t += "\nextra:\n  mig_move_tag_wait: 0\n" if "\nextra:" not in t else ""
open(V3, "w").write(t)
run("test build", "env.v3.yaml", "--test", "--commit")
mock("vc-green", "/mock/net", {"name": "app-210"})
mock("lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-g-1"})
mock("lm", "/mock/fvm", {"name": "app-vm-02", "external_id": "ext-g-2"})
world["refuse"] = ["blue-a-bdg01", "blue-a-bdg02"]
json.dump(world, open(WORLD, "w"))
run("move while Blue's edges refuse the password: held, the setting named", "env.v3.yaml", "--test", "--move", "--vm", "wave1.csv")
world["refuse"] = []
json.dump(world, open(WORLD, "w"))
run("the right password: planned", "env.v3.yaml", "--test", "--move", "--vm", "wave1.csv")
t = open(V3).read()
t = re.sub(r"(?m)^(blue:\n(?:.*\n)*?)", r"\1", t)
open(V3, "w").write(t.replace("\nsites:", "\n  # a value at the top again\nsites:", 1))
bad = re.sub(r"(?m)^(blue:.*\n)", r"\1  edge_password: 'again'\n", t, count=1)
open(os.path.join(HERE, "env.v3bad.yaml"), "w").write(bad)
os.chmod(os.path.join(HERE, "env.v3bad.yaml"), 0o600)
run("a sign-in in two places: refused before anything is read", "env.v3bad.yaml", "--test")
for f in ("env.v3.yaml", "env.v3bad.yaml", "wave1.csv") + tuple(os.path.basename(x) for x in glob.glob(os.path.join(HERE, "env.v3.yaml.*"))):
    if os.path.exists(os.path.join(HERE, f)):
        os.remove(os.path.join(HERE, f))
