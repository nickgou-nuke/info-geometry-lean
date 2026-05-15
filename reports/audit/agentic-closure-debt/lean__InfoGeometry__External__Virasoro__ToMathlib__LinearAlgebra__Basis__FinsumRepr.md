# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:33.330551+00:00`
Root: `lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Basis/FinsumRepr.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **2**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Basis/FinsumRepr.lean` | `advisory` | 10 | 0 | 2 | 6 | 8 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Basis/FinsumRepr.lean`
- module: `InfoGeometry.External.Virasoro.ToMathlib.LinearAlgebra.Basis.FinsumRepr`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `local-hypothesis-injection` in `lemma finsum_mem_mem_span` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L90 [advisory] `local-hypothesis-injection` in `lemma finsum_repr_smul_basis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L91 [advisory] `local-hypothesis-injection` in `lemma finsum_repr_smul_basis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L116 [soft] `skeletal-proof` in `lemma repr_finsum_mem_eq_ite` — proof appears to close via minimal tactic one-liner
  - L164 [advisory] `local-hypothesis-injection` in `def basis_submodule_span` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `def basis_submodule_span` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L197 [soft] `simp-law-injection` in `simp-declaration basis_submodule_span_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

