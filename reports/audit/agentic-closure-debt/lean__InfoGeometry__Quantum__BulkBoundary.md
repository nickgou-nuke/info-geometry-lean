# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:33.213401+00:00`
Root: `lean/InfoGeometry/Quantum/BulkBoundary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **49**
- Hard: **0**
- Soft: **22**
- Advisory: **27**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/BulkBoundary.lean` | `advisory` | 71 | 0 | 22 | 27 | 49 |

## Findings by file

### `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- module: `InfoGeometry.Quantum.BulkBoundary`
- status: `advisory`
- debt_score: `71`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L38 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L55 [soft] `law-field-locker` in `structure-field OperatorZeroModeWitness.vector_zeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `skeletal-proof` in `lemma add` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `lemma smul` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `skeletal-proof` in `lemma maps_plus_to_minus` — proof appears to close via minimal tactic one-liner
  - L121 [advisory] `local-hypothesis-injection` in `lemma maps_plus_to_minus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [soft] `skeletal-proof` in `lemma maps_minus_to_plus` — proof appears to close via minimal tactic one-liner
  - L137 [advisory] `local-hypothesis-injection` in `lemma maps_minus_to_plus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L177 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_hasZeroMode` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L196 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_operatorZeroModeWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L203 [soft] `skeletal-proof` in `theorem hasZeroMode_of_dim_mismatch` — proof appears to close via minimal tactic one-liner
  - L221 [advisory] `local-hypothesis-injection` in `theorem hasZeroMode_of_dim_mismatch` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L256 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_dim_mismatch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L270 [soft] `skeletal-proof` in `theorem hasZeroMode_conjugate_of_hasZeroMode` — proof appears to close via minimal tactic one-liner
  - L288 [advisory] `local-hypothesis-injection` in `theorem hasZeroMode_conjugate_of_hasZeroMode` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [advisory] `local-hypothesis-injection` in `theorem hasZeroMode_conjugate_of_hasZeroMode` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L305 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_hasZeroMode_conjugate` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L325 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L325 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L327 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L327 [soft] `section-law-variable` in `variable P0` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L345 [soft] `simp-law-injection` in `simp-declaration globalChainOperatorFromOpenChain_nil` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L350 [soft] `simp-law-injection` in `simp-declaration globalChainOperatorFromOpenChain_cons` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L415 [advisory] `existential-packaging` in `def BoundaryLocalizedZeroModePair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L445 [soft] `law-field-locker` in `structure-field BoundaryLocalizedZeroModeWitness.psiPlus_zeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L447 [soft] `law-field-locker` in `structure-field BoundaryLocalizedZeroModeWitness.psiMinus_zeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L455 [soft] `classical-witness-smuggling` in `def boundaryLocalizedZeroModeWitnessOfPair` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L522 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_boundaryLocalizedZeroModeWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L545 [soft] `law-field-locker` in `structure-field BoundaryLocalizationBridge.negPhase_to_boundaryLocalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L548 [soft] `law-field-locker` in `structure-field BoundaryLocalizationBridge.boundaryLocalized_to_dimMismatch` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L560 [soft] `law-field-locker` in `structure-field SimplifiedBoundaryModel.boundaryPair_of_negativePhase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L563 [soft] `law-field-locker` in `structure-field SimplifiedBoundaryModel.dimMismatch_of_boundaryPair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L592 [advisory] `local-hypothesis-injection` in `def boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L652 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L670 [advisory] `existential-packaging` in `theorem boundaryLocalizedZeroModePair_under_bogoliubov_of_preservesPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L724 [advisory] `existential-packaging` in `theorem weylZeroModePair_under_bogoliubov_of_preservesChiralityPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L724 [soft] `skeletal-proof` in `theorem weylZeroModePair_under_bogoliubov_of_preservesChiralityPolarization` — proof appears to close via minimal tactic one-liner
  - L776 [soft] `classical-witness-smuggling` in `def weylZeroModeWitnessUnderBogoliubov_of_preservesChiralityPolarization` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L821 [advisory] `existential-packaging` in `theorem boundaryLocalizedZeroModePair_of_negativePhase_under_bogoliubov_of_simplifiedBoundaryModel_of_preservesPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L875 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L875 [soft] `section-law-variable` in `variable globalChainOperator` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L902 [advisory] `existential-packaging` in `theorem zero_mode_is_information_sink` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L952 [advisory] `existential-packaging` in `theorem zero_mode_is_information_sink_concrete` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1008 [advisory] `existential-packaging` in `theorem zero_mode_is_information_sink_concrete_of_boundaryLocalization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1051 [advisory] `existential-packaging` in `theorem zero_mode_is_information_sink_concrete_of_boundaryLocalization_under_bogoliubov` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1099 [advisory] `existential-packaging` in `theorem zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1143 [advisory] `existential-packaging` in `theorem zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel_under_bogoliubov` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

