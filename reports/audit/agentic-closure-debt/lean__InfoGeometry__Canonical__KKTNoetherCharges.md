# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:22.533843+00:00`
Root: `lean/InfoGeometry/Canonical/KKTNoetherCharges.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **3**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KKTNoetherCharges.lean` | `advisory` | 16 | 0 | 3 | 10 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/KKTNoetherCharges.lean`
- module: `InfoGeometry.Canonical.KKTNoetherCharges`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L62 [soft] `skeletal-proof` in `theorem noether_charge_of_supercharge_split` — proof appears to close via minimal tactic one-liner
  - L68 [advisory] `local-hypothesis-injection` in `theorem noether_charge_of_supercharge_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [advisory] `local-hypothesis-injection` in `theorem noether_charge_of_supercharge_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L77 [advisory] `local-hypothesis-injection` in `theorem noether_charge_of_supercharge_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L79 [advisory] `local-hypothesis-injection` in `theorem noether_charge_of_supercharge_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [advisory] `local-hypothesis-injection` in `theorem noether_charge_of_supercharge_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L111 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L124 [soft] `skeletal-proof` in `theorem drazin_noether_charge_of_superHamiltonian_split` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `theorem drazin_noether_commutator_of_superHamiltonian_split` — proof appears to close via minimal tactic one-liner
  - L175 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L177 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

