# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:25.516168+00:00`
Root: `lean/InfoGeometry/Core/UnifiedGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **13**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/UnifiedGeometry.lean` | `advisory` | 36 | 0 | 13 | 10 | 23 |

## Findings by file

### `lean/InfoGeometry/Core/UnifiedGeometry.lean`
- module: `InfoGeometry.Core.UnifiedGeometry`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [soft] `law-field-locker` in `structure-field SymmetricSpace.reflection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L17 [soft] `law-field-locker` in `structure-field SymmetricSpace.reflection_fix` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L18 [soft] `simp-law-injection` in `simp-declaration reflection_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L25 [soft] `simp-law-injection` in `simp-declaration reflection_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [advisory] `local-hypothesis-injection` in `lemma reflection_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L44 [advisory] `local-hypothesis-injection` in `lemma reflection_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L66 [soft] `simp-law-injection` in `simp-declaration SymmetricSpace.toLegacy_ofLegacy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `simp-law-injection` in `simp-declaration SymmetricSpace.ofLegacy_toLegacy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [soft] `law-field-locker` in `structure-field CartanLieStructure.bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field CartanLieStructure.bracket_compat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [advisory] `local-hypothesis-injection` in `lemma conjugationMap_involutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L187 [advisory] `local-hypothesis-injection` in `lemma conjugationMap_involutive_sq_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `lemma conjugationMapNeg_involutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L227 [advisory] `local-hypothesis-injection` in `lemma conjugationMapNeg_bracket` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L267 [advisory] `local-hypothesis-injection` in `lemma conjugationMap_bracket` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L326 [soft] `skeletal-proof` in `lemma conjugation_bracket_even_even_mem_even` — proof appears to close via minimal tactic one-liner
  - L342 [soft] `skeletal-proof` in `lemma conjugation_bracket_even_odd_mem_odd` — proof appears to close via minimal tactic one-liner
  - L359 [soft] `skeletal-proof` in `lemma conjugation_bracket_odd_odd_mem_even` — proof appears to close via minimal tactic one-liner
  - L443 [advisory] `local-hypothesis-injection` in `lemma cartanInvolution_ext` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L445 [advisory] `local-hypothesis-injection` in `lemma cartanInvolution_ext` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L481 [soft] `simp-law-injection` in `simp-declaration mulInvolutiveOfCartan_toCartan` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L488 [soft] `simp-law-injection` in `simp-declaration cartanOfMulInvolutive_toMulInvolutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

