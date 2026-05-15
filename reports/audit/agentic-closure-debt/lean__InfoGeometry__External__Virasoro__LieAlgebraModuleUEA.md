# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:32.151996+00:00`
Root: `lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **11**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean` | `advisory` | 25 | 0 | 11 | 3 | 14 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean`
- module: `InfoGeometry.External.Virasoro.LieAlgebraModuleUEA`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L70 [soft] `skeletal-proof` in `lemma Algebra.scalar_smul_eq_smul_algebraMap_mul` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `skeletal-proof` in `lemma Algebra.smul_scalar_smul_eq_smul_algebraMap_mul` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `lemma moduleScalarOfModule.smul_def` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `skeletal-proof` in `lemma ModuleOfModuleAlgebra.lsmul_apply` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `skeletal-proof` in `lemma centralSMulHom_apply` — proof appears to close via minimal tactic one-liner
  - L203 [soft] `skeletal-proof` in `lemma mem_centralValueSubmodule_iff` — proof appears to close via minimal tactic one-liner
  - L246 [soft] `skeletal-proof` in `lemma UniversalEnvelopingAlgebra.mkAlgHom_range_eq_top` — proof appears to close via minimal tactic one-liner
  - L254 [soft] `skeletal-proof` in `lemma UniversalEnvelopingAlgebra.mkAlgHom_surjective` — proof appears to close via minimal tactic one-liner
  - L291 [soft] `skeletal-proof` in `lemma UniversalEnvelopingAlgebra.smul_eq_of_cyclic_of_forall_lie_eq_zero` — proof appears to close via minimal tactic one-liner
  - L335 [advisory] `local-hypothesis-injection` in `def UniversalEnvelopingAlgebra.representation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L357 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L385 [soft] `simp-law-injection` in `simp-declaration LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra_smul_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L391 [soft] `skeletal-proof` in `lemma LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra_` — proof appears to close via minimal tactic one-liner

