# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:24.864471+00:00`
Root: `lean/InfoGeometry/Core/SymmetricLie.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **81**
- Hard: **0**
- Soft: **36**
- Advisory: **45**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/SymmetricLie.lean` | `advisory` | 117 | 0 | 36 | 45 | 81 |

## Findings by file

### `lean/InfoGeometry/Core/SymmetricLie.lean`
- module: `InfoGeometry.Core.SymmetricLie`
- status: `advisory`
- debt_score: `117`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `law-field-locker` in `structure-field LieTripleSystem.triple` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field LieTripleSystem.jacobi_like` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `simp-law-injection` in `simp-declaration of_toInvolutiveLieAut` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L134 [soft] `simp-law-injection` in `simp-declaration to_ofInvolutiveLieAut` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L153 [advisory] `local-hypothesis-injection` in `def evenSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L158 [advisory] `local-hypothesis-injection` in `def evenSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L159 [advisory] `local-hypothesis-injection` in `def evenSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `def evenSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L174 [advisory] `local-hypothesis-injection` in `def oddSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L189 [soft] `skeletal-proof` in `lemma mem_evenSubmodule_iff` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `lemma mem_oddSubmodule_iff` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `theorem intersection_eq_zero` — proof appears to close via minimal tactic one-liner
  - L203 [advisory] `local-hypothesis-injection` in `theorem intersection_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L204 [advisory] `local-hypothesis-injection` in `theorem intersection_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L205 [advisory] `local-hypothesis-injection` in `theorem intersection_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L209 [advisory] `local-hypothesis-injection` in `theorem intersection_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `theorem intersection_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L260 [advisory] `local-hypothesis-injection` in `def evenLieSubalgebra` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L261 [advisory] `local-hypothesis-injection` in `def evenLieSubalgebra` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L262 [advisory] `local-hypothesis-injection` in `def evenLieSubalgebra` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L269 [soft] `skeletal-proof` in `lemma even_convex` — proof appears to close via minimal tactic one-liner
  - L274 [soft] `skeletal-proof` in `lemma odd_convex` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `theorem symmetric_pair_axioms` — proof appears to close via minimal tactic one-liner
  - L320 [advisory] `local-hypothesis-injection` in `theorem symmetric_pair_axioms` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L321 [advisory] `local-hypothesis-injection` in `theorem symmetric_pair_axioms` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L322 [advisory] `local-hypothesis-injection` in `theorem symmetric_pair_axioms` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L329 [advisory] `local-hypothesis-injection` in `theorem symmetric_pair_axioms` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L330 [advisory] `local-hypothesis-injection` in `theorem symmetric_pair_axioms` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L331 [advisory] `local-hypothesis-injection` in `theorem symmetric_pair_axioms` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L337 [soft] `skeletal-proof` in `theorem cartan_decomposition` — proof appears to close via minimal tactic one-liner
  - L341 [advisory] `local-hypothesis-injection` in `theorem cartan_decomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L344 [advisory] `local-hypothesis-injection` in `theorem cartan_decomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L350 [soft] `skeletal-proof` in `theorem bracket_k_k` — proof appears to close via minimal tactic one-liner
  - L358 [advisory] `local-hypothesis-injection` in `theorem bracket_k_k` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L359 [advisory] `local-hypothesis-injection` in `theorem bracket_k_k` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L360 [advisory] `local-hypothesis-injection` in `theorem bracket_k_k` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L363 [soft] `skeletal-proof` in `theorem bracket_k_p` — proof appears to close via minimal tactic one-liner
  - L371 [advisory] `local-hypothesis-injection` in `theorem bracket_k_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L372 [advisory] `local-hypothesis-injection` in `theorem bracket_k_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L373 [advisory] `local-hypothesis-injection` in `theorem bracket_k_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L379 [soft] `skeletal-proof` in `theorem bracket_p_p` — proof appears to close via minimal tactic one-liner
  - L387 [advisory] `local-hypothesis-injection` in `theorem bracket_p_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L388 [advisory] `local-hypothesis-injection` in `theorem bracket_p_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L389 [advisory] `local-hypothesis-injection` in `theorem bracket_p_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L403 [soft] `simp-law-injection` in `simp-declaration P_plus_eq_plusPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L408 [soft] `simp-law-injection` in `simp-declaration P_minus_eq_minusPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L413 [soft] `skeletal-proof` in `lemma plusPart_add` — proof appears to close via minimal tactic one-liner
  - L417 [soft] `skeletal-proof` in `lemma minusPart_add` — proof appears to close via minimal tactic one-liner
  - L421 [soft] `skeletal-proof` in `lemma plusPart_smul` — proof appears to close via minimal tactic one-liner
  - L425 [soft] `skeletal-proof` in `lemma minusPart_smul` — proof appears to close via minimal tactic one-liner
  - L441 [soft] `skeletal-proof` in `lemma convex_plusPart_image` — proof appears to close via minimal tactic one-liner
  - L446 [soft] `skeletal-proof` in `lemma convex_minusPart_image` — proof appears to close via minimal tactic one-liner
  - L451 [soft] `skeletal-proof` in `lemma convex_plusPart_preimage` — proof appears to close via minimal tactic one-liner
  - L456 [soft] `skeletal-proof` in `lemma convex_minusPart_preimage` — proof appears to close via minimal tactic one-liner
  - L461 [soft] `skeletal-proof` in `lemma decomposition` — proof appears to close via minimal tactic one-liner
  - L465 [soft] `skeletal-proof` in `lemma plusPart_mem_even` — proof appears to close via minimal tactic one-liner
  - L471 [soft] `skeletal-proof` in `lemma minusPart_mem_odd` — proof appears to close via minimal tactic one-liner
  - L477 [soft] `skeletal-proof` in `lemma plusPart_of_mem_even` — proof appears to close via minimal tactic one-liner
  - L480 [advisory] `local-hypothesis-injection` in `lemma plusPart_of_mem_even` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L481 [advisory] `local-hypothesis-injection` in `lemma plusPart_of_mem_even` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L492 [advisory] `local-hypothesis-injection` in `lemma minusPart_of_mem_even` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L497 [advisory] `local-hypothesis-injection` in `lemma plusPart_of_mem_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L499 [soft] `skeletal-proof` in `lemma minusPart_of_mem_odd` — proof appears to close via minimal tactic one-liner
  - L502 [advisory] `local-hypothesis-injection` in `lemma minusPart_of_mem_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L503 [advisory] `local-hypothesis-injection` in `lemma minusPart_of_mem_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L560 [advisory] `existential-packaging` in `theorem cartan_direct_sum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L624 [advisory] `local-hypothesis-injection` in `lemma triple_jacobi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L698 [soft] `simp-law-injection` in `simp-declaration oddLocalModel_odd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L701 [soft] `simp-law-injection` in `simp-declaration oddLocalModel_tripleSystem` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L704 [soft] `skeletal-proof` in `lemma oddLocalModel_convex` — proof appears to close via minimal tactic one-liner
  - L707 [soft] `skeletal-proof` in `lemma oddLocalModel_pathConnected` — proof appears to close via minimal tactic one-liner
  - L729 [advisory] `local-hypothesis-injection` in `lemma killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L730 [advisory] `local-hypothesis-injection` in `lemma killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L731 [advisory] `local-hypothesis-injection` in `lemma killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L737 [advisory] `local-hypothesis-injection` in `lemma killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L743 [soft] `simp-law-injection` in `simp-declaration cartanForm_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L755 [advisory] `local-hypothesis-injection` in `lemma cartanForm_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L756 [advisory] `local-hypothesis-injection` in `lemma cartanForm_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L763 [soft] `law-field-locker` in `structure-field CartanSignature.nonneg_on_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L765 [soft] `law-field-locker` in `structure-field CartanSignature.nonpos_on_even` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

