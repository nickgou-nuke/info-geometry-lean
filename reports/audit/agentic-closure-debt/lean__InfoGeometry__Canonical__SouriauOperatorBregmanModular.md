# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:58.042733+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauOperatorBregmanModular.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **27**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauOperatorBregmanModular.lean` | `advisory` | 58 | 0 | 27 | 4 | 31 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauOperatorBregmanModular.lean`
- module: `InfoGeometry.Canonical.SouriauOperatorBregmanModular`
- status: `advisory`
- debt_score: `58`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L58 [soft] `simp-law-injection` in `simp-declaration observablePairing_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem observablePairing_add` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration observablePairing_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `skeletal-proof` in `theorem observablePairing_sub` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `simp-law-injection` in `simp-declaration observablePairing_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem observablePairing_smul` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `simp-law-injection` in `simp-declaration operatorProductPairing_zero_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `skeletal-proof` in `theorem operatorProductPairing_zero_right` — proof appears to close via minimal tactic one-liner
  - L94 [soft] `simp-law-injection` in `simp-declaration boundedOperatorBregman_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `theorem boundedOperatorBregman_self` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `law-field-locker` in `structure-field SouriauOperatorRepresentation.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `simp-law-injection` in `simp-declaration bregmanPullback_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `skeletal-proof` in `theorem bregmanPullback_self` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `simp-law-injection` in `simp-declaration modularBetaExponential_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [soft] `skeletal-proof` in `theorem modularBetaExponential_zero` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `simp-law-injection` in `simp-declaration modularDeltaOfHamiltonian_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L156 [soft] `skeletal-proof` in `theorem modularDeltaOfHamiltonian_eq` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `simp-law-injection` in `simp-declaration modularDeviation_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `skeletal-proof` in `theorem modularDeviation_one` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `simp-law-injection` in `simp-declaration modularDeviation_beta_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L172 [soft] `skeletal-proof` in `theorem modularDeviation_beta_zero` — proof appears to close via minimal tactic one-liner
  - L200 [soft] `simp-law-injection` in `simp-declaration modularBetaFamily_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `skeletal-proof` in `theorem modularBetaFamily_zero` — proof appears to close via minimal tactic one-liner
  - L210 [soft] `simp-law-injection` in `simp-declaration modularDeviationAtOne_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L212 [soft] `skeletal-proof` in `theorem modularDeviationAtOne_eq` — proof appears to close via minimal tactic one-liner
  - L218 [soft] `simp-law-injection` in `simp-declaration regularConeBregman_self_readback` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L221 [advisory] `bridge-shaped-declaration` in `theorem regularConeBregman_self_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L221 [soft] `skeletal-proof` in `theorem regularConeBregman_self_readback` — proof appears to close via minimal tactic one-liner

