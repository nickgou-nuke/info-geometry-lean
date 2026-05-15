# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:25.227097+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **114**
- Hard: **0**
- Soft: **98**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean` | `advisory` | 212 | 0 | 98 | 16 | 114 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean`
- module: `InfoGeometry.OperatorAlgebra.TomitaCartanSplit`
- status: `advisory`
- debt_score: `212`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field MirrorInvolution.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field MirrorInvolution.map_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field MirrorInvolution.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field MirrorInvolution.map_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field MirrorInvolution.map_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field MirrorInvolution.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field MirrorInvolution.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L65 [soft] `skeletal-proof` in `theorem map_sub` — proof appears to close via minimal tactic one-liner
  - L123 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L150 [soft] `law-field-locker` in `structure-field TomitaCartanDatum.theta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field TomitaCartanDatum.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field TomitaCartanDatum.mirror_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L223 [soft] `law-field-locker` in `structure-field AlgebraCommutantRouting.InAlgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field AlgebraCommutantRouting.InCommutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field AlgebraCommutantRouting.overlap_central` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field FactorCenterDatum.IsScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field FactorCenterDatum.center_trivial` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L252 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L275 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `simp-law-injection` in `simp-declaration zero_mem_isotropicCone` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L286 [soft] `skeletal-proof` in `theorem zero_mem_isotropicCone` — proof appears to close via minimal tactic one-liner
  - L304 [soft] `law-field-locker` in `structure-field TomitaOverlapToIsotropicBridge.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L307 [soft] `law-field-locker` in `structure-field TomitaOverlapToIsotropicBridge.overlap_maps_to_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L340 [soft] `law-field-locker` in `structure-field ChiralStage.Pleft_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field ChiralStage.Pright_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field ChiralStage.complementary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field ChiralStage.disjoint_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field ChiralStage.disjoint_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L366 [soft] `law-field-locker` in `structure-field ChiralDynamics.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [soft] `law-field-locker` in `structure-field ChiralDynamics.preserves_left_sector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L370 [soft] `law-field-locker` in `structure-field ChiralDynamics.preserves_right_sector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [soft] `law-field-locker` in `structure-field LeftChiralDynamics.right_sector_trivial` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L437 [soft] `law-field-locker` in `structure-field TomitaCommutantDatum.tomitaMirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L440 [soft] `law-field-locker` in `structure-field TomitaCommutantDatum.mirror_M_to_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L444 [soft] `law-field-locker` in `structure-field TomitaCommutantDatum.mirror_comm_to_M` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [soft] `law-field-locker` in `structure-field TomitaCommutantDatum.overlap_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L459 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L492 [soft] `law-field-locker` in `structure-field TomitaAlgebraPair.Jconj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L495 [soft] `law-field-locker` in `structure-field TomitaAlgebraPair.IsScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L498 [soft] `law-field-locker` in `structure-field TomitaAlgebraPair.J_maps_M_to_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field TomitaAlgebraPair.J_maps_comm_to_M` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L506 [soft] `law-field-locker` in `structure-field TomitaAlgebraPair.overlap_is_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L517 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L555 [soft] `law-field-locker` in `structure-field FactorOverlapExclusion.Dynamic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L558 [soft] `law-field-locker` in `structure-field FactorOverlapExclusion.scalar_not_dynamic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L566 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L630 [soft] `simp-law-injection` in `simp-declaration mirrorSign_compact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L632 [soft] `skeletal-proof` in `theorem mirrorSign_compact` — proof appears to close via minimal tactic one-liner
  - L635 [soft] `simp-law-injection` in `simp-declaration mirrorSign_noncompact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L637 [soft] `skeletal-proof` in `theorem mirrorSign_noncompact` — proof appears to close via minimal tactic one-liner
  - L655 [soft] `simp-law-injection` in `simp-declaration globalFrom_compact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L657 [soft] `skeletal-proof` in `theorem globalFrom_compact` — proof appears to close via minimal tactic one-liner
  - L662 [soft] `simp-law-injection` in `simp-declaration globalFrom_noncompact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L664 [soft] `skeletal-proof` in `theorem globalFrom_noncompact` — proof appears to close via minimal tactic one-liner
  - L692 [soft] `skeletal-proof` in `theorem global_eq_plus` — proof appears to close via minimal tactic one-liner
  - L701 [soft] `skeletal-proof` in `theorem global_eq_minus` — proof appears to close via minimal tactic one-liner
  - L728 [soft] `law-field-locker` in `structure-field TomitaRoutedCartanGenerator.mirror_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L738 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L767 [soft] `simp-law-injection` in `simp-declaration mirrorCombination_compact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L769 [soft] `skeletal-proof` in `theorem mirrorCombination_compact` — proof appears to close via minimal tactic one-liner
  - L774 [soft] `simp-law-injection` in `simp-declaration mirrorCombination_noncompact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L776 [soft] `skeletal-proof` in `theorem mirrorCombination_noncompact` — proof appears to close via minimal tactic one-liner
  - L798 [soft] `law-field-locker` in `structure-field CartanTomitaGenerator.mirror_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L890 [soft] `law-field-locker` in `structure-field SplitPairingDatum.form` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L891 [soft] `law-field-locker` in `structure-field SplitPairingDatum.neg_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L898 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L909 [soft] `skeletal-proof` in `theorem diagonal_isotropic` — proof appears to close via minimal tactic one-liner
  - L958 [soft] `law-field-locker` in `structure-field TomitaDefectNullBridge.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L961 [soft] `law-field-locker` in `structure-field TomitaDefectNullBridge.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L964 [soft] `law-field-locker` in `structure-field TomitaDefectNullBridge.representedOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L967 [soft] `law-field-locker` in `structure-field TomitaDefectNullBridge.defect_overlap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L973 [soft] `law-field-locker` in `structure-field TomitaDefectNullBridge.defect_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1028 [soft] `skeletal-proof` in `theorem diagonal_isotropic` — proof appears to close via minimal tactic one-liner
  - L1040 [soft] `skeletal-proof` in `theorem antidiagonal_isotropic` — proof appears to close via minimal tactic one-liner
  - L1072 [soft] `simp-law-injection` in `simp-declaration mirrorSign_compact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1074 [soft] `skeletal-proof` in `theorem mirrorSign_compact` — proof appears to close via minimal tactic one-liner
  - L1077 [soft] `simp-law-injection` in `simp-declaration mirrorSign_noncompact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1079 [soft] `skeletal-proof` in `theorem mirrorSign_noncompact` — proof appears to close via minimal tactic one-liner
  - L1100 [soft] `law-field-locker` in `structure-field TomitaCartanGeneratorDatum.localGen` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1101 [soft] `law-field-locker` in `structure-field TomitaCartanGeneratorDatum.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1102 [soft] `law-field-locker` in `structure-field TomitaCartanGeneratorDatum.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1118 [soft] `skeletal-proof` in `theorem globalGenerator_compact` — proof appears to close via minimal tactic one-liner
  - L1128 [soft] `skeletal-proof` in `theorem globalGenerator_noncompact` — proof appears to close via minimal tactic one-liner
  - L1138 [advisory] `existential-packaging` in `structure FactorCenterExclusion` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1152 [soft] `law-field-locker` in `structure-field FactorCenterExclusion.overlap_is_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1159 [soft] `law-field-locker` in `structure-field FactorCenterExclusion.dynamicPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1167 [soft] `law-field-locker` in `structure-field FactorCenterExclusion.dynamicPart_scalar_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1203 [soft] `law-field-locker` in `structure-field CenterCollapseMapsToIsotropic.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1206 [soft] `law-field-locker` in `structure-field CenterCollapseMapsToIsotropic.dynamic_zero_is_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1243 [soft] `law-field-locker` in `structure-field FactorOverlapDatum.inAlgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1245 [soft] `law-field-locker` in `structure-field FactorOverlapDatum.inCommutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1248 [soft] `law-field-locker` in `structure-field FactorOverlapDatum.isScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1251 [soft] `law-field-locker` in `structure-field FactorOverlapDatum.overlap_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1259 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1298 [soft] `law-field-locker` in `structure-field TomitaCartanSplitDatum.compact_sector_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1304 [soft] `law-field-locker` in `structure-field TomitaCartanSplitDatum.noncompact_sector_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1316 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1349 [advisory] `existential-packaging` in `def TomitaCartanSplitModelOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1370 [soft] `law-field-locker` in `structure-field AlgebraCommutantDatum.center_eq_intersection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1373 [soft] `law-field-locker` in `structure-field AlgebraCommutantDatum.factor_center_trivial` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1384 [soft] `law-field-locker` in `structure-field TomitaMirror.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1385 [soft] `law-field-locker` in `structure-field TomitaMirror.mirror_maps_algebra_to_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1387 [soft] `law-field-locker` in `structure-field TomitaMirror.mirror_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1427 [soft] `law-field-locker` in `structure-field DoubledKreinQuadratic.q0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1461 [soft] `law-field-locker` in `structure-field TomitaIsotropicBridge.carrierRep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1463 [soft] `law-field-locker` in `structure-field TomitaIsotropicBridge.overlap_maps_to_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1494 [soft] `law-field-locker` in `structure-field TomitaDrazinBridge.defect_maps_to_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1499 [soft] `law-field-locker` in `structure-field TomitaDrazinBridge.defect_supported_by_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1508 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

