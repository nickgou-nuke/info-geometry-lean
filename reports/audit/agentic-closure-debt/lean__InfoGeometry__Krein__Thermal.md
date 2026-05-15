# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.145167+00:00`
Root: `lean/InfoGeometry/Krein/Thermal.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **8**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Thermal.lean` | `advisory` | 22 | 0 | 8 | 6 | 14 |

## Findings by file

### `lean/InfoGeometry/Krein/Thermal.lean`
- module: `InfoGeometry.Krein.Thermal`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [soft] `simp-law-injection` in `simp-declaration krein_modular_shift_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `lemma krein_kms_like_zero_implies_commutation` — proof appears to close via minimal tactic one-liner
  - L84 [advisory] `local-hypothesis-injection` in `lemma krein_kms_like_zero_implies_commutation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L103 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L116 [soft] `simp-law-injection` in `simp-declaration modular_shift_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `skeletal-proof` in `lemma modular_shift_add` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `lemma kms_like_zero_implies_commutation` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `lemma kms_zero_implies_commutation` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `law-field-locker` in `structure-field ThermalVacuum.modular_j_fixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field ThermalVacuum.generator_annihilates` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [advisory] `local-hypothesis-injection` in `lemma modular_flow_inv_Omega_of_spectral_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

