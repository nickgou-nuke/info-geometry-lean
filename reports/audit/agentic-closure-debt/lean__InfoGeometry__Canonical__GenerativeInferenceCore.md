# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:10.320020+00:00`
Root: `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **22**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean` | `advisory` | 50 | 0 | 22 | 6 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean`
- module: `InfoGeometry.Canonical.GenerativeInferenceCore`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [soft] `law-field-locker` in `structure-field GenerativeInferenceDatum.routingWeights` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field GenerativeInferenceDatum.routingLabels` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field GenerativeInferenceDatum.beliefChain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `skeletal-proof` in `lemma contextSemanticState_fst_eq_plusChannelMass` — proof appears to close via minimal tactic one-liner
  - L137 [soft] `skeletal-proof` in `lemma contextSemanticState_snd_eq_minusChannelMass` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `lemma contextSemanticState_coord_sum_eq_weight_sum` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem bayesianChainAction_nonneg` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `skeletal-proof` in `lemma routingMassCoupling_eq_coord_diff` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `skeletal-proof` in `theorem hyperbolicBoostScale_eq_exp` — proof appears to close via minimal tactic one-liner
  - L172 [advisory] `local-hypothesis-injection` in `theorem hyperbolicallyBoostedBayesianAction_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L176 [soft] `skeletal-proof` in `theorem spectralObstruction_eq_zero_iff_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `skeletal-proof` in `theorem anomalyScale_eq_zero_of_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L214 [soft] `law-field-locker` in `structure-field BridgeCandidate.anomalyOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `skeletal-proof` in `theorem bridgeCandidate_chainAction_nonneg` — proof appears to close via minimal tactic one-liner
  - L234 [advisory] `existential-packaging` in `theorem bridgeCandidate_boostedChainAction_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L234 [soft] `skeletal-proof` in `theorem bridgeCandidate_boostedChainAction_nonneg` — proof appears to close via minimal tactic one-liner
  - L248 [advisory] `existential-packaging` in `theorem exists_contextSemanticState_of_bistochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L248 [soft] `skeletal-proof` in `theorem exists_contextSemanticState_of_bistochastic` — proof appears to close via minimal tactic one-liner
  - L283 [soft] `simp-law-injection` in `simp-declaration splitDoubledAtom_phaseAxis_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L289 [soft] `skeletal-proof` in `theorem splitDoubledCarrier_finrank_eq_two_mul_finrank` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `theorem splitDoubledCarrier_finrank_eq_128_of_finrank_eq_64` — proof appears to close via minimal tactic one-liner
  - L318 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L318 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L319 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L319 [soft] `section-law-variable` in `variable Q` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L330 [soft] `skeletal-proof` in `theorem weylMassLikeCoupling_eq_zero_iff_balanced` — proof appears to close via minimal tactic one-liner
  - L344 [soft] `simp-law-injection` in `simp-declaration canonicalHyperbolicBoostRotor_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

