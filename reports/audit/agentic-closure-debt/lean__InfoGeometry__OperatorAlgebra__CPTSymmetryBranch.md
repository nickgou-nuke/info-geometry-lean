# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:06.383092+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **50**
- Hard: **0**
- Soft: **41**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean` | `advisory` | 91 | 0 | 41 | 9 | 50 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean`
- module: `InfoGeometry.OperatorAlgebra.CPTSymmetryBranch`
- status: `advisory`
- debt_score: `91`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `simp-law-injection` in `simp-declaration chiralSignToReal_preserves` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L32 [soft] `skeletal-proof` in `theorem chiralSignToReal_preserves` — proof appears to close via minimal tactic one-liner
  - L35 [soft] `simp-law-injection` in `simp-declaration chiralSignToReal_flips` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `skeletal-proof` in `theorem chiralSignToReal_flips` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `law-field-locker` in `structure-field ChiralGrading.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field ModularChiralCPTMirror.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field ModularChiralCPTMirror.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field ModularChiralCPTMirror.J_metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L151 [soft] `skeletal-proof` in `theorem chiralCharge_J` — proof appears to close via minimal tactic one-liner
  - L184 [soft] `law-field-locker` in `structure-field ModularChiralCPTBranch.tomita_mirror_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field ModularChiralCPTBranch.modular_time_reversal_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field ModularChiralCPTBranch.cpt_interpretation_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [soft] `law-field-locker` in `structure-field Datum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field Datum.K_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field Datum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [soft] `law-field-locker` in `structure-field Datum.J_reverses_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [soft] `law-field-locker` in `structure-field Datum.J_chi_relation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field Datum.modular_time_reversal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field Datum.cpt_interpretation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L261 [soft] `skeletal-proof` in `theorem J_chi_apply_of_preserves` — proof appears to close via minimal tactic one-liner
  - L267 [advisory] `local-hypothesis-injection` in `theorem J_chi_apply_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L272 [soft] `skeletal-proof` in `theorem J_chi_apply_of_flips` — proof appears to close via minimal tactic one-liner
  - L278 [advisory] `local-hypothesis-injection` in `theorem J_chi_apply_of_flips` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L392 [soft] `law-field-locker` in `structure-field CPTBranch.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L396 [soft] `law-field-locker` in `structure-field CPTBranch.eps_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L400 [soft] `law-field-locker` in `structure-field CPTBranch.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [soft] `law-field-locker` in `structure-field CPTBranch.J_flips_eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L408 [soft] `law-field-locker` in `structure-field CPTBranch.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L412 [soft] `law-field-locker` in `structure-field CPTBranch.Kmod_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L416 [soft] `law-field-locker` in `structure-field CPTBranch.Kmod_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field CPTBranch.tomita_commutant_mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L424 [soft] `law-field-locker` in `structure-field CPTBranch.cpt_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L432 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L441 [soft] `skeletal-proof` in `theorem J_mul_one_add_chi` — proof appears to close via minimal tactic one-liner
  - L460 [soft] `skeletal-proof` in `theorem J_mul_one_sub_chi` — proof appears to close via minimal tactic one-liner
  - L563 [soft] `law-field-locker` in `structure-field CPTAlgebraCommutantBranch.InAlgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L565 [soft] `law-field-locker` in `structure-field CPTAlgebraCommutantBranch.InCommutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L574 [soft] `law-field-locker` in `structure-field CPTAlgebraCommutantBranch.alphaJ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L577 [soft] `law-field-locker` in `structure-field CPTAlgebraCommutantBranch.alphaJ_maps_algebra_to_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L581 [soft] `law-field-locker` in `structure-field CPTAlgebraCommutantBranch.alphaJ_P_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L589 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L653 [soft] `law-field-locker` in `structure-field CPTSymmetryBranchDatum.J_agrees` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L666 [soft] `law-field-locker` in `structure-field CPTSymmetryBranchDatum.tomita_algebra_commutant_routing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L674 [soft] `law-field-locker` in `structure-field CPTSymmetryBranchDatum.J_reverses_modular_time` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L681 [soft] `law-field-locker` in `structure-field CPTSymmetryBranchDatum.physical_CPT_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L693 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L833 [advisory] `existential-packaging` in `def CPTBranchOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

