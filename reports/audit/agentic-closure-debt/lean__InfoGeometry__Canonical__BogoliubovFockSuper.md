# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.336496+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **34**
- Hard: **0**
- Soft: **20**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean` | `advisory` | 54 | 0 | 20 | 14 | 34 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
- module: `InfoGeometry.Canonical.BogoliubovFockSuper`
- status: `advisory`
- debt_score: `54`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `law-field-locker` in `structure-field HyperbolicMixingParams.normalization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `skeletal-proof` in `theorem bogoliubovAnnihilation_map_zero` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `theorem bogoliubovCreation_map_zero` — proof appears to close via minimal tactic one-liner
  - L190 [soft] `skeletal-proof` in `lemma superBracket_smul_right` — proof appears to close via minimal tactic one-liner
  - L198 [soft] `simp-law-injection` in `simp-declaration superBracket_even_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L204 [soft] `simp-law-injection` in `simp-declaration superBracket_odd_odd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `skeletal-proof` in `theorem anticommutator_annihilation_self` — proof appears to close via minimal tactic one-liner
  - L268 [soft] `skeletal-proof` in `theorem anticommutator_creation_self` — proof appears to close via minimal tactic one-liner
  - L352 [advisory] `local-hypothesis-injection` in `theorem not_isCARPair_base` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L359 [advisory] `local-hypothesis-injection` in `theorem not_isCARPair_base` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L363 [soft] `skeletal-proof` in `lemma anticommutator_symm` — proof appears to close via minimal tactic one-liner
  - L384 [soft] `skeletal-proof` in `theorem superBracket_bogoliubov_covariance` — proof appears to close via minimal tactic one-liner
  - L402 [soft] `skeletal-proof` in `theorem anticommutator_bogoliubov_projector_model` — proof appears to close via minimal tactic one-liner
  - L437 [advisory] `local-hypothesis-injection` in `theorem anticommutator_bogoliubov_projector_model` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L450 [advisory] `local-hypothesis-injection` in `theorem anticommutator_bogoliubov_projector_model` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L454 [advisory] `local-hypothesis-injection` in `theorem anticommutator_bogoliubov_projector_model` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L467 [advisory] `local-hypothesis-injection` in `theorem anticommutator_bogoliubov_projector_model` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L469 [soft] `skeletal-proof` in `theorem commutator_bogoliubov_projector_model` — proof appears to close via minimal tactic one-liner
  - L510 [soft] `skeletal-proof` in `theorem anticommutator_ofAngle_projector_model` — proof appears to close via minimal tactic one-liner
  - L659 [soft] `simp-law-injection` in `simp-declaration cliffordConcreteAnnihilation_toLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L668 [advisory] `local-hypothesis-injection` in `def cliffordConcreteCreation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L671 [advisory] `local-hypothesis-injection` in `def cliffordConcreteCreation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L695 [soft] `simp-law-injection` in `simp-declaration cliffordConcreteCreation_toLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L704 [advisory] `local-hypothesis-injection` in `def cliffordConcreteCreation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L707 [advisory] `local-hypothesis-injection` in `def cliffordConcreteCreation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L731 [soft] `simp-law-injection` in `simp-declaration cliffordConcreteAnnihilation_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L736 [advisory] `local-hypothesis-injection` in `def cliffordConcreteCreation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L748 [soft] `simp-law-injection` in `simp-declaration cliffordConcreteCreation_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L753 [advisory] `local-hypothesis-injection` in `def cliffordConcreteCreation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L835 [soft] `skeletal-proof` in `lemma einsteinFockDeformation_eq_zero_of_vacuumTransported` — proof appears to close via minimal tactic one-liner
  - L845 [advisory] `local-hypothesis-injection` in `lemma einsteinFockDeformation_eq_zero_of_vacuumTransported` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L895 [soft] `skeletal-proof` in `lemma grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported` — proof appears to close via minimal tactic one-liner
  - L912 [soft] `skeletal-proof` in `lemma grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported` — proof appears to close via minimal tactic one-liner

