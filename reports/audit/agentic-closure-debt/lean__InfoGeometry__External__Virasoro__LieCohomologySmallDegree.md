# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:32.421616+00:00`
Root: `lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **26**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean` | `advisory` | 56 | 0 | 26 | 4 | 30 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean`
- module: `InfoGeometry.External.Virasoro.LieCohomologySmallDegree`
- status: `advisory`
- debt_score: `56`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L74 [soft] `simp-law-injection` in `simp-declaration toLinearMap_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `lemma toLinearMap_zero` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `simp-law-injection` in `simp-declaration toLinearMap_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `skeletal-proof` in `lemma toLinearMap_add` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `simp-law-injection` in `simp-declaration toLinearMap_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `skeletal-proof` in `lemma toLinearMap_smul` — proof appears to close via minimal tactic one-liner
  - L167 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L168 [soft] `simp-law-injection` in `simp-declaration self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `skeletal-proof` in `lemma apply_add` — proof appears to close via minimal tactic one-liner
  - L177 [soft] `skeletal-proof` in `lemma apply_smul` — proof appears to close via minimal tactic one-liner
  - L181 [soft] `skeletal-proof` in `lemma skew` — proof appears to close via minimal tactic one-liner
  - L183 [advisory] `local-hypothesis-injection` in `lemma skew` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L207 [soft] `simp-law-injection` in `simp-declaration toBilin_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L209 [soft] `skeletal-proof` in `lemma toBilin_zero` — proof appears to close via minimal tactic one-liner
  - L210 [soft] `simp-law-injection` in `simp-declaration toBilin_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L212 [soft] `skeletal-proof` in `lemma toBilin_add` — proof appears to close via minimal tactic one-liner
  - L214 [soft] `simp-law-injection` in `simp-declaration toBilin_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `skeletal-proof` in `lemma toBilin_smul` — proof appears to close via minimal tactic one-liner
  - L260 [soft] `skeletal-proof` in `lemma add_apply` — proof appears to close via minimal tactic one-liner
  - L263 [soft] `skeletal-proof` in `lemma smul_apply` — proof appears to close via minimal tactic one-liner
  - L266 [soft] `skeletal-proof` in `lemma sub_apply` — proof appears to close via minimal tactic one-liner
  - L272 [soft] `simp-law-injection` in `simp-declaration zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L274 [soft] `simp-law-injection` in `simp-declaration zero_apply'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L312 [soft] `simp-law-injection` in `simp-declaration LieOneCochain.neg_bdry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L316 [soft] `skeletal-proof` in `lemma LieOneCochain.bdry_apply` — proof appears to close via minimal tactic one-liner
  - L361 [soft] `skeletal-proof` in `lemma cohomologyClass_add_bdry` — proof appears to close via minimal tactic one-liner
  - L367 [advisory] `existential-packaging` in `lemma exists_eq_bdry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L384 [soft] `skeletal-proof` in `lemma LieOneCochain.bdry_apply_eq_zero_of_isLieAbelian` — proof appears to close via minimal tactic one-liner
  - L413 [soft] `skeletal-proof` in `lemma LieTwoCocycle.toLieTwoCohomologyEquiv_toLinearMap` — proof appears to close via minimal tactic one-liner

