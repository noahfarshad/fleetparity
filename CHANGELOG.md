# Changelog

All notable changes to this project are documented here.

## [1.24.1] — 2026-10-16

### Added

- Initial public release. `migpath` moves live workloads from one NSX Federation ("Blue") to another ("Green"), one subnet at a time, over a temporary Layer 2 bridge: build the bridge edges and the Green segments, move VMs in waves by cross-vCenter vMotion, cut the routing over per subnet, unbridge, and every step's way back. Plan by default; `--commit --expect <digest>` writes only a reviewed plan; Blue is read again after every commit and the run fails if anything outside its scope changed; production addresses are pinged across every change; every commit that changed something prints its `UNDO`, and a clean forward run ends with `NEXT`.
- `--check-leaves` reads each leaf switch and writes the exact NVUE lines for the transit VLANs. `--verify` confirms one active and one standby bridge per VLAN. `--set` writes one config value by its full name, passwords asked for twice and never shown.
- Mock Global and Local Managers, mock vCenters (REST and SOAP), fake `ssh` and `ping`, and five end-to-end flows under `test/`.

### Notes

- Every name, address and AS number in the examples and tests is a placeholder: `example.com` hosts, `site-a` and `site-b`, and documentation or private address ranges.
- Passwords come from the environment, the config or a prompt, and never appear in the evidence folders.
- Versions before 1.24.1 were delivered privately. The test flows name the version that introduced each guard rail.
- The companion for expired NSX Manager certificates is its own repository, nsx-cert-fix.
