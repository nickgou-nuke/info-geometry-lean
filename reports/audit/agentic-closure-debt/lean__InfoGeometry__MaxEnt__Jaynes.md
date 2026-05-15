# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:00.100883+00:00`
Root: `lean/InfoGeometry/MaxEnt/Jaynes.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **38**
- Hard: **0**
- Soft: **21**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | `advisory` | 59 | 0 | 21 | 17 | 38 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/Jaynes.lean`
- module: `InfoGeometry.MaxEnt.Jaynes`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `simp-law-injection` in `simp-declaration xlogx_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `skeletal-proof` in `lemma ShannonEntropy_eq_xlogx` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `simp-law-injection` in `simp-declaration ShannonEntropy_eq_entropy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration mem_simplex_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [advisory] `existential-packaging` in `lemma partitionWithPrior_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L100 [soft] `skeletal-proof` in `lemma partitionWithPrior_pos` — proof appears to close via minimal tactic one-liner
  - L115 [advisory] `local-hypothesis-injection` in `lemma partitionWithPrior_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L118 [advisory] `local-hypothesis-injection` in `lemma partitionWithPrior_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `lemma partitionWithPrior_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L133 [advisory] `local-hypothesis-injection` in `lemma partitionWithPrior_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `lemma gibbsWithPrior_eq_exp_sub_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L230 [soft] `skeletal-proof` in `lemma empiricalFreq_sum_one` — proof appears to close via minimal tactic one-liner
  - L259 [soft] `skeletal-proof` in `lemma multiplicity_pos` — proof appears to close via minimal tactic one-liner
  - L265 [soft] `skeletal-proof` in `lemma multiplicity_spec` — proof appears to close via minimal tactic one-liner
  - L286 [advisory] `local-hypothesis-injection` in `lemma logMultiplicity_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L309 [soft] `law-field-locker` in `structure-field AsymptoticEquipartitionWitness.countsSeq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [soft] `law-field-locker` in `structure-field AsymptoticEquipartitionWitness.total_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [soft] `law-field-locker` in `structure-field AsymptoticEquipartitionWitness.tendsToEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [soft] `simp-law-injection` in `simp-declaration mem_feasibleClass_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L385 [advisory] `existential-packaging` in `lemma goodFraction_le_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L393 [advisory] `local-hypothesis-injection` in `lemma goodFraction_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L400 [advisory] `local-hypothesis-injection` in `lemma goodFraction_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L403 [advisory] `local-hypothesis-injection` in `lemma goodFraction_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L419 [advisory] `existential-packaging` in `structure EntropyConcentrationCertificate` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L424 [soft] `law-field-locker` in `structure-field EntropyConcentrationCertificate.eps_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L425 [soft] `law-field-locker` in `structure-field EntropyConcentrationCertificate.eta_bounds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L427 [soft] `law-field-locker` in `structure-field EntropyConcentrationCertificate.lower_fraction_bound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L428 [soft] `skeletal-proof` in `lemma entropyBand_of_mem_confidenceInterval` — proof appears to close via minimal tactic one-liner
  - L435 [advisory] `local-hypothesis-injection` in `lemma entropyBand_of_mem_confidenceInterval` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L436 [advisory] `local-hypothesis-injection` in `lemma entropyBand_of_mem_confidenceInterval` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L438 [advisory] `existential-packaging` in `lemma mem_confidenceInterval_of_entropyBand` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L452 [soft] `skeletal-proof` in `theorem gibbs_maximizes_shannon_under_moment` — proof appears to close via minimal tactic one-liner
  - L465 [advisory] `existential-packaging` in `structure CanonicalProblem` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L470 [soft] `law-field-locker` in `structure-field CanonicalProblem.b` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L471 [soft] `law-field-locker` in `structure-field CanonicalProblem.obs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L565 [soft] `law-field-locker` in `structure-field BurgModel.coeff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L567 [soft] `law-field-locker` in `structure-field BurgModel.noiseVar_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

