# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:14.737910+00:00`
Root: `lean/InfoGeometry/Canonical/ZetaDeterminant.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **14**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ZetaDeterminant.lean` | `advisory` | 31 | 0 | 14 | 3 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/ZetaDeterminant.lean`
- module: `InfoGeometry.Canonical.ZetaDeterminant`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `skeletal-proof` in `lemma zetaRegularizedDet_pos` — proof appears to close via minimal tactic one-liner
  - L41 [soft] `simp-law-injection` in `simp-declaration zetaRegularizedLogDet_eq_logAbsDet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `skeletal-proof` in `theorem zetaRegularizedLogDet_mul` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem operatorZetaRegularizedLogDet_mul_right` — proof appears to close via minimal tactic one-liner
  - L93 [advisory] `local-hypothesis-injection` in `theorem operatorZetaRegularizedLogDet_mul_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [soft] `skeletal-proof` in `theorem operatorZetaRegularizedLogDet_mul_left` — proof appears to close via minimal tactic one-liner
  - L133 [advisory] `local-hypothesis-injection` in `theorem operatorZetaRegularizedLogDet_mul_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [soft] `law-field-locker` in `structure-field SpectralZetaLogDetData.regularizedOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `simp-law-injection` in `simp-declaration logDet_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L183 [soft] `simp-law-injection` in `simp-declaration cutoff_ne_zero'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L199 [soft] `simp-law-injection` in `simp-declaration spectralZetaLogDetDataOfRegularizedTriple_logDet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `simp-law-injection` in `simp-declaration spectralZetaLogDetDataOfChiralTriple_logDet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L232 [soft] `simp-law-injection` in `simp-declaration zetaLogDetBarrier_eq_logDetBarrier` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `simp-law-injection` in `simp-declaration zetaRegularizedLogVolume_eq_logAbsVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L257 [soft] `skeletal-proof` in `theorem zetaRegularizedLogVolume_add` — proof appears to close via minimal tactic one-liner
  - L264 [soft] `skeletal-proof` in `theorem capstone_logAbsVolume_add_from_zeta` — proof appears to close via minimal tactic one-liner

