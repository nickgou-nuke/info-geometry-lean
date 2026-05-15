# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:06.099227+00:00`
Root: `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **51**
- Hard: **0**
- Soft: **40**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TomitaTakesaki.lean` | `advisory` | 91 | 0 | 40 | 11 | 51 |

## Findings by file

### `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- module: `InfoGeometry.Canonical.TomitaTakesaki`
- status: `advisory`
- debt_score: `91`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `simp-law-injection` in `simp-declaration cptJ_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration cptJeps_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `skeletal-proof` in `lemma cptJ_cptJeps_anticommute` — proof appears to close via minimal tactic one-liner
  - L59 [advisory] `local-hypothesis-injection` in `lemma cptJ_cptJeps_anticommute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [advisory] `local-hypothesis-injection` in `lemma iota_mem_adjoin_cptAtomSet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L117 [advisory] `local-hypothesis-injection` in `theorem cptAtoms_generate_splitCliffordAlg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L128 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L176 [soft] `simp-law-injection` in `simp-declaration modularConjugationJ_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L183 [soft] `simp-law-injection` in `simp-declaration modularSignEpsilon_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `skeletal-proof` in `lemma clockAxis_eq_modular_j_comp_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L200 [soft] `skeletal-proof` in `lemma phaseAxisK_eq_clockAxis` — proof appears to close via minimal tactic one-liner
  - L207 [soft] `skeletal-proof` in `lemma modularComplexI_eq_clockAxis` — proof appears to close via minimal tactic one-liner
  - L210 [soft] `simp-law-injection` in `simp-declaration modularComplexI_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L215 [soft] `simp-law-injection` in `simp-declaration modularComplexI_apply_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L220 [soft] `skeletal-proof` in `lemma clockAxis_eq_complex_i` — proof appears to close via minimal tactic one-liner
  - L234 [soft] `skeletal-proof` in `lemma clockAxis_eq_dilationOperator` — proof appears to close via minimal tactic one-liner
  - L239 [soft] `simp-law-injection` in `simp-declaration modularConjugationJ_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L244 [soft] `simp-law-injection` in `simp-declaration modularSignEpsilon_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `skeletal-proof` in `lemma modularConjugationJ_anticommutes_modularSign` — proof appears to close via minimal tactic one-liner
  - L255 [soft] `simp-law-injection` in `simp-declaration clockAxis_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L262 [soft] `simp-law-injection` in `simp-declaration modularComplexI_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L267 [soft] `skeletal-proof` in `lemma modularConjugationJ_anticommutes_modularComplexI` — proof appears to close via minimal tactic one-liner
  - L281 [soft] `skeletal-proof` in `lemma modularSignEpsilon_isOdd` — proof appears to close via minimal tactic one-liner
  - L286 [soft] `skeletal-proof` in `lemma modularComplexI_isOdd` — proof appears to close via minimal tactic one-liner
  - L304 [soft] `skeletal-proof` in `lemma clockAxis_kreinInner_swap` — proof appears to close via minimal tactic one-liner
  - L314 [soft] `skeletal-proof` in `lemma modularComplexI_kreinInner_comp` — proof appears to close via minimal tactic one-liner
  - L325 [advisory] `local-hypothesis-injection` in `lemma modularComplexI_kreinInner_comp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L340 [soft] `skeletal-proof` in `lemma clockAxis_kreinInner_comp` — proof appears to close via minimal tactic one-liner
  - L364 [soft] `skeletal-proof` in `lemma clockAxis_inner_skew` — proof appears to close via minimal tactic one-liner
  - L372 [soft] `skeletal-proof` in `lemma complex_i_inner_skew` — proof appears to close via minimal tactic one-liner
  - L379 [soft] `skeletal-proof` in `lemma modularComplexI_inner_comp` — proof appears to close via minimal tactic one-liner
  - L388 [advisory] `local-hypothesis-injection` in `lemma modularComplexI_inner_comp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L397 [soft] `skeletal-proof` in `lemma clockAxis_inner_comp` — proof appears to close via minimal tactic one-liner
  - L405 [soft] `skeletal-proof` in `lemma complex_i_inner_comp` — proof appears to close via minimal tactic one-liner
  - L421 [advisory] `local-hypothesis-injection` in `lemma modularConjugationJ_anticommutator_modularSignEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L428 [soft] `skeletal-proof` in `lemma modularConjugationJ_commutator_modularSignEpsilon` — proof appears to close via minimal tactic one-liner
  - L437 [advisory] `local-hypothesis-injection` in `lemma modularConjugationJ_commutator_modularSignEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L439 [advisory] `local-hypothesis-injection` in `lemma modularConjugationJ_commutator_modularSignEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L449 [soft] `skeletal-proof` in `theorem modularConjugationJ_exp_modularSignEpsilon` — proof appears to close via minimal tactic one-liner
  - L515 [soft] `skeletal-proof` in `theorem modularConjugationJ_exp_modularComplexI` — proof appears to close via minimal tactic one-liner
  - L576 [soft] `skeletal-proof` in `theorem modularConjugationJ_exp_modularComplexI_right` — proof appears to close via minimal tactic one-liner
  - L644 [soft] `simp-law-injection` in `simp-declaration modularSignAdditiveModularFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L685 [soft] `skeletal-proof` in `lemma modularCPTSupercharge_hamiltonian` — proof appears to close via minimal tactic one-liner
  - L710 [advisory] `existential-packaging` in `def DiagonalPositiveTimeVector` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L774 [soft] `simp-law-injection` in `simp-declaration modularAtomRepresentation_cptJ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L779 [soft] `simp-law-injection` in `simp-declaration tomitaRepresentation_cptJ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L783 [soft] `simp-law-injection` in `simp-declaration modularAtomRepresentation_cptJeps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L788 [soft] `simp-law-injection` in `simp-declaration tomitaRepresentation_cptJeps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L792 [soft] `simp-law-injection` in `simp-declaration modularAtomRepresentation_cptEps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L797 [soft] `simp-law-injection` in `simp-declaration tomitaRepresentation_cptEps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

