# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:25.689179+00:00`
Root: `lean/DAG/TripleSystem.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/DAG/TripleSystem.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/DAG/TripleSystem.lean`
- module: `DAG.TripleSystem`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [soft] `law-field-locker` in `structure-field TripleSystem.triple` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field Hom.mapObj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field Hom.mapRel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field Hom.preserves` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `simp-law-injection` in `simp-declaration id_mapObj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `simp-law-injection` in `simp-declaration id_mapRel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `simp-law-injection` in `simp-declaration comp_mapObj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration comp_mapRel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

