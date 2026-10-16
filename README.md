# fleetparity

Moves live workloads from one NSX Federation ("Blue") to another ("Green"), one subnet at a time, over a temporary Layer 2 bridge. VMs keep their IP addresses and move by cross-vCenter vMotion. The default gateway moves per subnet, and every step has a tested way back.

License: GPL-3.0. Built and proved out for [essential.coach](https://essential.coach).
Full write-up: [Bridging Blue to Green: Moving Live Workloads to a New NSX Federation, One Subnet at a Time](https://essential.coach/bridging-blue-to-green-nsx-federation/)

The migration is the `migpath` command. The same file began as a VCF 9 fleet parity check (`run`, `collect`, `compare`) and grew `fedapply` for a stretched Tier-0; `--help` lists them all. This README covers `migpath`.

## Contents

| Path | What it is |
|---|---|
| `fleetparity.py` | The tool, version 1.24.1. One file that uses only the Python standard library. |
| `examples/env_example.yaml` | A two-site config with every setting explained. |
| `examples/scope_example.csv` | The segments to bridge at a site. |
| `examples/wave_example.csv` | A wave: the VMs that move together. |
| `test/` | Mock NSX Managers and vCenters, fake `ssh` and `ping`, and five end-to-end flows. |

## Requirements

- Python 3 (tested with 3.11 and 3.13). PyYAML is used if it's installed; otherwise the tool reads the YAML itself.
- An OpenSSH client, 8.4 or later. Password sign-ins go through `SSH_ASKPASS`, so `sshpass` isn't needed.
- `openssl`, for the tests.
- One jump host that can reach both Global Managers, the Local Managers, the vCenters, the bridge edges and the leaf switches (Cumulus Linux with NVUE).

## Quick start

```
cp examples/env_example.yaml env.yaml && chmod 600 env.yaml        # then edit the sites, hosts and scope
alias fp='python3 fleetparity.py migpath --config env.yaml --site site-a'
fp --set sites.site-a.green.vc_password                             # asked for twice, never shown
fp --help
```

Every step plans first and writes nothing. Review the plan, then run the same command again with `--commit --expect <digest>`, using the digest on the line that begins `plan <digest>:`. Run a step again and it reports `No changes`.

Rehearse on the site's test segment first, with `blue_writes: test` so that only `--test` runs can write to Blue:

```
fp --test --check-leaves              # transit VLANs on the leaf ports; prints the exact NVUE lines
fp --test --edges                     # bridge edges, edge cluster, VLAN zone, trunk port group, DRS rule
fp --test                             # Green segment (gateway off), bridge profiles, both bridges
fp --test --verify                    # one active and one standby bridge per VLAN
fp --test --move --vm wave.csv        # the wave's VMs to Green, one at a time
fp --test --cutover 10.1.125.0/24     # prefix list, Blue's gateway off, Green's on, wait for the leaves
fp --test --unbridge 10.1.125.0/24    # the bridge comes off both sides
```

The ways back are `--return --vm wave.csv`, which puts each VM back where it left, and `--rollback SUBNET`, which puts the bridges back, turns Green's gateway off and turns Blue's on. Every commit that changed something prints `UNDO`, the exact command that reverses it, and a clean forward run ends with `NEXT`, the command to run next.

For production, set `scope` (a list, or a scope .csv) and run the same steps without `--test`. Change `blue_writes` to `true` in the change window that opens production. Outside `--test`, a step that changes NSX itself writes only with `--expect`; otherwise those changes are HELD.

## Safety model

- Nothing is written without `--commit`. With `--expect`, a commit writes exactly the plan that was reviewed, or nothing.
- After every commit, Blue is read again, and the run fails if anything outside its scope changed.
- Production addresses (`probes`) are pinged across every change, and a single lost ping fails the run.
- Each run leaves an evidence folder with the plan, the checks, what was written and the probe results. Passwords never appear in it.
- A state file, `migpath_state_<site>.json`, sits beside the config and records what the tool built and where each VM came from. Keep one folder per config: returns rely on that record.

## Tests

```
bash test/run_tests.sh
```

This starts eight mock managers and vCenters on 127.0.0.1, ports 9443 to 9450. It puts the fake `ssh` and `ping` first in `PATH` and runs the five flows, forward through every step and back again. It then stops the mocks and removes what it wrote. It takes about four minutes and ends with `simple flow: all PASS`.

## Expired certificates

If the first deployment of Blue's bridge edges fails with `OVF certificate validation failed: certificate has expired`, the edges are not the problem: the NSX Manager's own certificates have expired ([Broadcom KB 408930](https://knowledge.broadcom.com/external/article/408930/nsx-manager-deployment-fails-with-ovf-ce.html)). [nsx-cert-fix](https://github.com/noahfarshad/nsx-cert-fix) replaces them one node at a time and deletes the failed edge deployments, so `--edges` can run again. Its write-up is [When the NSX Manager Certificate Is Already Expired](https://essential.coach/nsx-manager-certificate-already-expired/).

## Not included

Customer configs, wave files, state files and evidence. Every name, address and AS number in the examples and tests is a placeholder.
