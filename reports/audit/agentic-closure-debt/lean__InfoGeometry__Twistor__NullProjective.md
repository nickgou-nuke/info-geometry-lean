# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:50.112866+00:00`
Root: `lean/InfoGeometry/Twistor/NullProjective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **5**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Twistor/NullProjective.lean` | `advisory` | 16 | 0 | 5 | 6 | 11 |

## Findings by file

### `lean/InfoGeometry/Twistor/NullProjective.lean`
- module: `InfoGeometry.Twistor.NullProjective`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `definitional-equality-bypass` in `cast <cast>` — cast/propext/unsafe equality transport detected; verify this is not hiding a failed `rfl` or definitional-equality hallucination
  - L33 [advisory] `local-hypothesis-injection` in `def IsNull` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L35 [advisory] `local-hypothesis-injection` in `def IsNull` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L36 [advisory] `local-hypothesis-injection` in `def IsNull` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L40 [advisory] `local-hypothesis-injection` in `def IsNull` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L53 [soft] `simp-law-injection` in `simp-declaration isNull_mk_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [advisory] `existential-packaging` in `class ChiralFactorization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [soft] `law-field-locker` in `class-field ChiralFactorization.factor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `class-field ChiralFactorization.null_of_factor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `class-field ChiralFactorization.factor_of_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

