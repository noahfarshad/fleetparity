#!/usr/bin/env python3
"""1.23.0, the after-hours simplifications, asserted on the mocks (already running):
  a build outside --test changes NSX itself only with --expect (a plain --commit holds it, nothing written);
  a wave moves with --move --vm and comes back with --return --vm, the config untouched;
  NEXT names the one command forward after a clean forward run, and never after a way back;
  a wave commit while the scope has NSX changes pending holds them and moves nothing;
  the route wait says how long it may take.
1.24.0: each VM lands in the folder of the same path on Green as on Blue, the missing ones made first (vc-folder
  rows, parents first); a return puts it back in the Blue folder it left, and says so when that folder is gone.
Every check prints PASS or FAIL; the flow exits 1 on any FAIL."""
import copy, glob, hashlib, json, os, re, ssl, subprocess, sys, urllib.request

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


def run(label, cfg, *args, show=r"\[(ADD|UPDATE|DELETE|BLOCKED|ERROR|NEXT|HELD)|\[(FAIL)\]|^  UNDO|^  NEXT|^  HELD|^    |"
                                r"No changes|STOPPED|NOT DONE|waiting for|Traceback"):
    p = subprocess.run([sys.executable, FP, "migpath", "--config", os.path.join(HERE, cfg)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=HERE, stdin=subprocess.DEVNULL)
    out = p.stdout.decode()
    print("=" * 100)
    print("%s   rc=%s   (%s)" % (label, p.returncode, " ".join(args)))
    for l in out.splitlines():
        if re.search(show, l) and not re.search(r"empty on Blue at SITE-B|bridge VLAN|uplinks at", l):
            print(l[:210])
    if "Traceback" in out:
        print(out[-2500:])
    return p.returncode, out


def build(label, cfg, *args):
    """A change to NSX itself outside --test: its plan, then --commit --expect <that plan's digest>."""
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


print("\n" + "#" * 100 + "\n# simple flow (1.23.0, 1.24.0)\n" + "#" * 100)
BAD = []


def check(what, ok, detail=""):
    print("  %s  %s%s" % ("PASS" if ok else "FAIL", what, ("   (%s)" % detail) if detail and not ok else ""))
    if not ok:
        BAD.append(what)


def section(out, head):
    """The lines under a heading such as '  NEXT' or '  UNDO', up to the next blank line."""
    lines, on = [], False
    for l in out.splitlines():
        if l.rstrip() == head:
            on = True
            continue
        if on and not l.strip():
            break
        if on:
            lines.append(l.strip())
    return lines


def where(vm):
    st = json.load(open(os.path.join(HERE, "migpath_state_site-a.json")))
    return ((st["segments"].get("app-210") or {}).get("vms") or {}).get(vm, {}).get("where")


def digest_of(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


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
FOLD = {"app-vm-01": mock("vc-blue", "/mock/folder", {"path": "Apps/Billing"})["moref"],
        "app-vm-02": mock("vc-blue", "/mock/folder", {"path": "Apps"})["moref"]}
for i, n in enumerate(("app-vm-01", "app-vm-02")):
    mock("vc-blue", "/mock/vm", {"name": n, "network": "app-210", "ip": "10.30.10.%d" % (11 + i), "folder": FOLD[n]})
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-1", "tags": [{"scope": "app", "tag": "billing"}]})
open(os.path.join(HERE, "wave1.csv"), "w").write("vm,subnet,owner\napp-vm-01,10.30.10.0/24,billing\napp-vm-02,10.30.10.0/24,billing\n")
C1 = cfgv("env.s1.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_tag_wait": "0"})
C1P = os.path.join(HERE, C1)

# 1. a plain --commit outside --test: the build is HELD, nothing written
rc, out = run("plain --commit, no --expect: held", C1, "--commit")
out_held = out
check("plain commit holds the build", rc == 1 and "  HELD: " in out and re.search(r"\[HELD +\] Green +segment", out), "rc=%s" % rc)
check("nothing written on Green", "/segments/app-210" not in mock("green", "/mock/state")["S"])
check("the HELD line gives the exact command", re.search(r"HELD: .* fp --commit --expect \S+", out) is not None)
rc, out = run("the plan says --expect is needed", C1)
check("plan line asks for --expect", re.search(r"To apply: the same command with --commit --expect \S+ \(\d+ of them change NSX", out)
      is not None)

# 2. the build with the command the HELD line gave: written
m = re.search(r"HELD: .* fp --commit --expect (\S+)", out_held)
rc, out = run("the HELD line's command", C1, "--commit", "--expect", m.group(1) if m else "none")
check("the HELD line's command writes the build", "/segments/app-210" in mock("green", "/mock/state")["S"], "rc=%s" % rc)
mock("vc-green", "/mock/net", {"name": "app-210"})
mock("lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-g-1"})
mock("lm", "/mock/fvm", {"name": "app-vm-02", "external_id": "ext-g-2"})

# 3. the wave forward: UNDO is one --return, NEXT is the cutover
before = digest_of(C1P)
rc, out = run("wave: plan", C1, "--move", "--vm", "wave1.csv")
check("plan: the folders Green lacks are vc-folder rows, parents first",
      re.search(r"\[ADD +\] Green vc-folder +Apps .*\n.*\[ADD +\] Green vc-folder +Apps/Billing", out) is not None)
check("plan: each VM names its folder", re.search(r"app-vm-01 .*folder Apps/Billing", out.replace("\n   ", " ")) is not None
      or "folder Apps/Billing" in re.sub(r"\s+", " ", out))
rc, out = run("wave: commit", C1, "--move", "--vm", "wave1.csv", "--commit")
gf = mock("vc-green", "/mock/folders")
check("Green has the folders, the VMs in them", "Apps/Billing" in gf["folders"] and gf["vms"].get("app-vm-01") == "Apps/Billing"
      and gf["vms"].get("app-vm-02") == "Apps", gf)
check("the wave moved", where("app-vm-01") == "green" and where("app-vm-02") == "green",
      "%s %s" % (where("app-vm-01"), where("app-vm-02")))
undo = section(out, "  UNDO")
check("UNDO is one --return", any("fp --return --vm wave1.csv --commit" in l for l in undo), undo)
nxt = section(out, "  NEXT")
check("NEXT is the cutover", any("fp --cutover 10.30.10.0/24" in l for l in nxt), nxt)
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "remove": True})

# 4. the cutover: NEXT is the unbridge; the route wait says how long
rc, out = run("cutover: commit", C1, "--cutover", "app-210", "--commit")
check("route wait says up to how long", re.search(r"waiting for Green \(up to \d+s, each leaf", out) is not None)
nxt = section(out, "  NEXT")
check("NEXT after the cutover is the unbridge", any("fp --unbridge 10.30.10.0/24" in l for l in nxt), nxt)

# 4b. the unbridge: NEXT says done; the cutover that undoes it is a way back: no NEXT
rc, out = run("unbridge: commit", C1, "--unbridge", "app-210", "--commit")
check("NEXT after the unbridge is done", any("done" in l for l in section(out, "  NEXT")), section(out, "  NEXT"))
rc, out = run("unbridge undone: --cutover puts the bridges back", C1, "--cutover", "app-210", "--commit")
check("no NEXT after the unbridge's way back", not section(out, "  NEXT") and rc == 0, "rc=%s %s" % (rc, section(out, "  NEXT")))

# 5. the way back: no NEXT after a rollback or a return; the return leaves the config as it was
rc, out = run("rollback: commit", C1, "--rollback", "app-210", "--commit")
check("no NEXT after a rollback", not section(out, "  NEXT"))
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-3", "tags": []})
run("return: plan", C1, "--return", "--vm", "wave1.csv")
rc, out = run("return: commit", C1, "--return", "--vm", "wave1.csv", "--commit")
check("the wave is back on Blue", where("app-vm-01") == "blue" and where("app-vm-02") == "blue",
      "%s %s" % (where("app-vm-01"), where("app-vm-02")))
bf = mock("vc-blue", "/mock/folders")
check("back on Blue in the folders they left", bf["vms"].get("app-vm-01") == "Apps/Billing" and bf["vms"].get("app-vm-02") == "Apps", bf)
check("the config is untouched", digest_of(C1P) == before)
undo = section(out, "  UNDO")
check("UNDO of the return is one --move", any("fp --move --vm wave1.csv --commit" in l for l in undo), undo)
check("no NEXT after a return", not section(out, "  NEXT"))
rc, out = run("return again: nothing to do", C1, "--return", "--vm", "wave1.csv", "--commit")
check("return again says No changes", "No changes" in out and "the VMs listed to return are on Blue" in out)

# 6. a wave while the scope has an NSX change pending (db-211 to be taken apart): held, nothing moved
mock("lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-g-1"})
C2 = cfgv("env.s2.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_skip_site-a": "[db-211]",
                           "mig_move_tag_wait": "0"})
rc, out = run("wave while db-211 waits to be taken apart", C2, "--move", "--vm", "wave1.csv", "--commit")
check("the take-apart is HELD", re.search(r"\[HELD +\] .*db-211", out) is not None and "  HELD: " in out)
check("db-211 still on Green", "/segments/db-211" in mock("green", "/mock/state")["S"])
check("the VMs wait, none moved", where("app-vm-01") == "blue" and "waits for the build" in out and rc == 1)
check("no NEXT while something is held", not section(out, "  NEXT"))

# 6b. a wave the config's move_vms lists: its UNDO is return_vms (which wins over move_vms), not a one-run --return
rc, out = run("wave after the take-apart", C1, "--move", "--vm", "app-vm-02", "--commit")
C3 = cfgv("env.s3.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_vms_site-a": "[wave1.csv]",
                           "mig_move_tag_wait": "0"})
rc, out = run("declared wave: commit", C3, "--move", "--vm", "wave1.csv", "--commit")
check("moved again: the folders exist, no vc-folder row", "vc-folder" not in out and
      mock("vc-green", "/mock/folders")["vms"].get("app-vm-01") == "Apps/Billing")
undo = section(out, "  UNDO")
check("declared wave: UNDO lists it in return_vms", any("wave1.csv in mig_return_vms" in l or "wave1.csv in sites." in l
                                                       for l in undo) and not any("--return" in l for l in undo), undo)
# 6c. the way back names the Blue folder: its path read on Blue for a VM moved before 1.24.0; a folder gone is said
SP = os.path.join(HERE, "migpath_state_site-a.json")
keep = open(SP).read()
st_ = json.loads(keep)
st_["segments"]["app-210"]["vms"]["app-vm-01"]["from"].pop("folder_path", None)
st_["segments"]["app-210"]["vms"]["app-vm-02"]["from"]["folder"] = "group-v999"
json.dump(st_, open(SP, "w"))
rc, out = run("return plan: the folders by the record", C1, "--return", "--vm", "wave1.csv")
flat = re.sub(r"\s+", " ", out)
check("return plan: a VM moved before 1.24.0 goes back to its folder, the path read on Blue",
      re.search(r"app-vm-01 from \S+ to [^\[]*, folder Apps/Billing", flat) is not None, flat[-500:])
check("return plan: a Blue folder gone is said", re.search(r"app-vm-02 from \S+ to [^\[]*, folder \(the VM folder: the one it "
                                                           r"left, Apps, is gone\)", flat) is not None, flat[-500:])
open(SP, "w").write(keep)
rc, out = run("declared wave: --return names the list it is still in", C3, "--return", "--vm", "app-vm-01")
check("--return of a VM move_vms lists says so", re.search(r"WARN: app-vm-01: in \S+ too, so the next run without --return moves it to Green again", out) is not None)
C4 = cfgv("env.s4.yaml", **{"mig_scope_site-a": "[app-210, db-211]", "mig_move_vms_site-a": "[wave1.csv]",
                           "mig_test_segments_site-a": "[app-210]", "mig_move_tag_wait": "0"})
rc, out = run("declared wave, --test --return: says so too", C4, "--test", "--return", "--vm", "app-vm-01")
check("--test --return of a VM move_vms lists says so", re.search(r"WARN: app-vm-01: in \S+ too", out) is not None)
mock("blue-lm", "/mock/fvm", {"name": "app-vm-01", "external_id": "ext-b-4", "tags": []})
rc, out = run("return while db-211 waits to be taken apart", C2, "--return", "--vm", "wave1.csv", "--commit")
undo = section(out, "  UNDO")
check("a return goes ahead while changes are HELD", where("app-vm-01") == "blue" and where("app-vm-02") == "blue"
      and "  HELD: " in out, "%s %s" % (where("app-vm-01"), where("app-vm-02")))
check("its UNDO says a move waits for the HELD changes", any("a move waits while the HELD change(s)" in l for l in undo), undo)
open(os.path.join(HERE, "empty.csv"), "w").write("vm,subnet\n# nothing tonight\n")

# 7. what the command line refuses
for args, want in ((["--return", "--move", "--vm", "app-vm-01"], "one way each"),
                   (["--return"], "--return sends back the VMs --vm names"),
                   (["--return", "--vm", "app-vm-01", "--cutover", "app-210"], "--return goes with a build run"),
                   (["--vm", "app-vm-01"], "or a --return sends back"),
                   (["--move"], "It never takes the whole scope at once"),
                   (["--move", "--cutover", "app-210"], "--move goes with a build"),
                   (["--move", "--vm", "empty.csv"], "names no VM"),
                   (["--return", "--vm", "empty.csv"], "names no VM")):
    rc, out = run("refused: %s" % " ".join(args), C1, *args)
    check("refused: %s" % " ".join(args), rc != 0 and want in out, out.strip().splitlines()[-1:] if out.strip() else "")

for f in ("env.s1.yaml", "env.s2.yaml", "env.s3.yaml", "env.s4.yaml", "wave1.csv", "empty.csv"):
    if os.path.exists(os.path.join(HERE, f)):
        os.remove(os.path.join(HERE, f))
print("\nsimple flow: %s" % ("all PASS" if not BAD else "%d FAIL: %s" % (len(BAD), "; ".join(BAD))))
sys.exit(1 if BAD else 0)
