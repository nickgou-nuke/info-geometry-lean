# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:50.020593+00:00`
Root: `lean/InfoGeometry/Krein/Clifford.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **27**
- Hard: **0**
- Soft: **24**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Clifford.lean` | `advisory` | 51 | 0 | 24 | 3 | 27 |

## Findings by file

### `lean/InfoGeometry/Krein/Clifford.lean`
- module: `InfoGeometry.Krein.Clifford`
- status: `advisory`
- debt_score: `51`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [soft] `law-field-locker` in `class-field KreinGradedModule.grade_invol` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `class-field KreinGradedModule.grade_selfAdj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `simp-law-injection` in `simp-declaration gradeCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration gradeCLM_comp_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `simp-law-injection` in `simp-declaration hilbertSwapMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L231 [soft] `simp-law-injection` in `simp-declaration hilbertSwapLIE_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L238 [soft] `simp-law-injection` in `simp-declaration hilbertSwapCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `simp-law-injection` in `simp-declaration toDoubled_hilbertSwapCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L251 [soft] `skeletal-proof` in `lemma hilbertSwap_selfAdj_clm` — proof appears to close via minimal tactic one-liner
  - L265 [soft] `simp-law-injection` in `simp-declaration gradeCLM_eq_hilbertSwapCLM` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L268 [soft] `simp-law-injection` in `simp-declaration jCLM_apply_coords` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L289 [soft] `simp-law-injection` in `simp-declaration J_apply_coords` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L294 [soft] `simp-law-injection` in `simp-declaration toDoubled_jCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L306 [soft] `simp-law-injection` in `simp-declaration hilbertComplexI_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L311 [soft] `simp-law-injection` in `simp-declaration toDoubled_hilbertComplexI_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L349 [soft] `skeletal-proof` in `lemma kreinAdjoint_jCLM_hilbert` — proof appears to close via minimal tactic one-liner
  - L362 [soft] `skeletal-proof` in `lemma kreinAdjoint_hilbertComplexI` — proof appears to close via minimal tactic one-liner
  - L413 [advisory] `local-hypothesis-injection` in `lemma cl11RepLinHilbert_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L428 [soft] `simp-law-injection` in `simp-declaration cl11RepHilbert_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L444 [advisory] `local-hypothesis-injection` in `instance instSymmetricCliffordModuleHilbertDoubled` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L462 [soft] `simp-law-injection` in `simp-declaration rotation45_apply_rotation45Isometry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L508 [soft] `simp-law-injection` in `simp-declaration rot45Conj_symm_apply_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L521 [soft] `simp-law-injection` in `simp-declaration cl11RepNeutral_apply_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L541 [soft] `simp-law-injection` in `simp-declaration rotation45_cl11RepNeutral_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L548 [soft] `simp-law-injection` in `simp-declaration cl11RepNeutral_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L553 [soft] `simp-law-injection` in `simp-declaration rotation45_gradeCLM_neutral_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

