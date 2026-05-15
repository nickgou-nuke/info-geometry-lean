# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:53.363986+00:00`
Root: `lean/InfoGeometry/Krein/KreinSpace.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **37**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/KreinSpace.lean` | `advisory` | 77 | 0 | 37 | 3 | 40 |

## Findings by file

### `lean/InfoGeometry/Krein/KreinSpace.lean`
- module: `InfoGeometry.Krein.KreinSpace`
- status: `advisory`
- debt_score: `77`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `class-field KreinSpace.J_invol` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `class-field KreinSpace.J_selfAdj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `simp-law-injection` in `simp-declaration jCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration jCLM_comp_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration jCLM_comp_jCLM_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration comp_jCLM_comp_jCLM` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L88 [soft] `simp-law-injection` in `simp-declaration adjoint_jCLM` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration kreinInner_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `skeletal-proof` in `lemma kreinInner_symm` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `lemma kreinInner_add_left` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `lemma kreinInner_add_right` — proof appears to close via minimal tactic one-liner
  - L117 [soft] `skeletal-proof` in `lemma kreinInner_smul_left` — proof appears to close via minimal tactic one-liner
  - L121 [soft] `skeletal-proof` in `lemma kreinInner_smul_right` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `skeletal-proof` in `lemma kreinInner_kreinAdjoint` — proof appears to close via minimal tactic one-liner
  - L144 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [soft] `skeletal-proof` in `lemma kreinAdjoint_involutive` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L174 [soft] `simp-law-injection` in `simp-declaration kreinAdjoint_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [soft] `skeletal-proof` in `lemma kreinAdjoint_lie` — proof appears to close via minimal tactic one-liner
  - L182 [soft] `skeletal-proof` in `lemma kreinAdjoint_lie_neg` — proof appears to close via minimal tactic one-liner
  - L210 [soft] `skeletal-proof` in `lemma isKreinSelfAdjoint_iff` — proof appears to close via minimal tactic one-liner
  - L230 [soft] `skeletal-proof` in `lemma isKreinSelfAdjoint_iff_j_comp_selfAdjoint` — proof appears to close via minimal tactic one-liner
  - L279 [soft] `skeletal-proof` in `lemma isKreinSkewAdjoint_iff` — proof appears to close via minimal tactic one-liner
  - L304 [soft] `skeletal-proof` in `lemma isKreinIsometry_iff_star_comp_self` — proof appears to close via minimal tactic one-liner
  - L347 [soft] `simp-law-injection` in `simp-declaration kreinQuad_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L351 [soft] `simp-law-injection` in `simp-declaration kreinQuad_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L391 [soft] `simp-law-injection` in `simp-declaration signFlipMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L403 [advisory] `local-hypothesis-injection` in `lemma signFlipMap_norm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L407 [advisory] `local-hypothesis-injection` in `lemma signFlipMap_norm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L428 [soft] `simp-law-injection` in `simp-declaration signFlipLIE_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L430 [soft] `skeletal-proof` in `lemma signFlipLIE_apply` — proof appears to close via minimal tactic one-liner
  - L466 [soft] `law-field-locker` in `structure-field KreinHom.hom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L467 [soft] `law-field-locker` in `structure-field KreinHom.isometric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L475 [soft] `law-field-locker` in `structure-field KreinEquiv.isometric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

