# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:59.849474+00:00`
Root: `lean/InfoGeometry/MaxEnt/Finite.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **39**
- Hard: **0**
- Soft: **13**
- Advisory: **26**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/Finite.lean` | `advisory` | 52 | 0 | 13 | 26 | 39 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/Finite.lean`
- module: `InfoGeometry.MaxEnt.Finite`
- status: `advisory`
- debt_score: `52`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field MaxEntProblem.p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field MaxEntProblem.norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field MaxEntProblem.expectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field MaxEntProblem.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [advisory] `existential-packaging` in `lemma partition_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L65 [advisory] `existential-packaging` in `lemma partition_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L71 [advisory] `existential-packaging` in `lemma gibbs_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L78 [advisory] `existential-packaging` in `lemma gibbs_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L84 [advisory] `existential-packaging` in `lemma gibbs_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L103 [advisory] `existential-packaging` in `lemma gibbs_eq_exp_sub_logPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [advisory] `local-hypothesis-injection` in `lemma gibbs_eq_exp_sub_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L116 [advisory] `existential-packaging` in `def gibbsMaxEntProblemOfExpectation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L161 [soft] `law-field-locker` in `structure-field FiniteJaynesProblem.feature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field FiniteJaynesProblem.target` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `simp-law-injection` in `simp-declaration energy_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [advisory] `existential-packaging` in `lemma partition_pos_of_fullSupport` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L189 [soft] `classical-witness-smuggling` in `lemma partition_pos_of_fullSupport` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L198 [advisory] `local-hypothesis-injection` in `lemma partition_pos_of_fullSupport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L201 [advisory] `local-hypothesis-injection` in `lemma partition_pos_of_fullSupport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L208 [advisory] `existential-packaging` in `lemma partition_ne_zero_of_fullSupport` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L220 [soft] `simp-law-injection` in `simp-declaration gibbsWeight_nonneg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L238 [advisory] `local-hypothesis-injection` in `lemma gibbsProb_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [advisory] `local-hypothesis-injection` in `lemma gibbsProb_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L263 [soft] `skeletal-proof` in `lemma sum_toReal_eq_one` — proof appears to close via minimal tactic one-liner
  - L267 [advisory] `local-hypothesis-injection` in `lemma sum_toReal_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L270 [advisory] `local-hypothesis-injection` in `lemma sum_toReal_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L303 [soft] `skeletal-proof` in `lemma sum_prob_mul_energy` — proof appears to close via minimal tactic one-liner
  - L321 [advisory] `local-hypothesis-injection` in `lemma sum_prob_mul_energy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L355 [advisory] `local-hypothesis-injection` in `lemma gibbsDist_pointwise` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L376 [advisory] `local-hypothesis-injection` in `lemma satisfiesTargetMoments_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [soft] `skeletal-proof` in `lemma gibbsProb_eq_prior_mul_exp_tilt` — proof appears to close via minimal tactic one-liner
  - L395 [advisory] `local-hypothesis-injection` in `lemma gibbsProb_eq_prior_mul_exp_tilt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L396 [advisory] `local-hypothesis-injection` in `lemma gibbsProb_eq_prior_mul_exp_tilt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L423 [advisory] `local-hypothesis-injection` in `lemma log_gibbsRatio_eq_energy_sub_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L424 [advisory] `local-hypothesis-injection` in `lemma log_gibbsRatio_eq_energy_sub_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L444 [advisory] `local-hypothesis-injection` in `lemma mul_log_ratio_to_gibbs_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L501 [advisory] `local-hypothesis-injection` in `lemma kl_gibbs_variational_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L546 [soft] `simp-law-injection` in `simp-declaration ofLogLikelihood_energy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

