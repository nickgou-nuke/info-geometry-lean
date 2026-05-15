# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:52.481879+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralOperatorConeClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **14**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralOperatorConeClosure.lean` | `advisory` | 32 | 0 | 14 | 4 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralOperatorConeClosure.lean`
- module: `InfoGeometry.Canonical.ChiralOperatorConeClosure`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `skeletal-proof` in `theorem isInChiralOperatorCone_iff_anticommute_GammaS` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem add_mem_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem smul_mem_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `skeletal-proof` in `theorem spectralAdjointFlow_mem_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `theorem spectralCommutator_compact_mem_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `skeletal-proof` in `theorem mul_mem_spectralCompact_of_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `skeletal-proof` in `theorem anticommutator_mem_spectralCompact_of_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L221 [soft] `skeletal-proof` in `theorem spectralCommutator_chiral_chiral_mem_spectralCompact` — proof appears to close via minimal tactic one-liner
  - L336 [soft] `skeletal-proof` in `theorem supercharge_mem_chiralOperatorCone` — proof appears to close via minimal tactic one-liner
  - L351 [soft] `skeletal-proof` in `theorem anticommutator_GammaS_chiralAnomaly_eq_zero` — proof appears to close via minimal tactic one-liner
  - L354 [advisory] `local-hypothesis-injection` in `theorem anticommutator_GammaS_chiralAnomaly_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L372 [soft] `skeletal-proof` in `theorem anticommutator_GammaS_rightChiralAnomaly_eq_zero` — proof appears to close via minimal tactic one-liner
  - L375 [advisory] `local-hypothesis-injection` in `theorem anticommutator_GammaS_rightChiralAnomaly_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L402 [soft] `law-field-locker` in `structure-field SpectralChiralConeAlgebra.anticommutator_GammaS_chiL_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [soft] `law-field-locker` in `structure-field SpectralChiralConeAlgebra.anticommutator_GammaS_chiR_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L415 [soft] `law-field-locker` in `structure-field SpectralChiralConeAlgebra.compact_commutator_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

