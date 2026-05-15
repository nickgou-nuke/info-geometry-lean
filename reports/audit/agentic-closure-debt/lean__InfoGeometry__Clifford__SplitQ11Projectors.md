# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:19.963020+00:00`
Root: `lean/InfoGeometry/Clifford/SplitQ11Projectors.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **18**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/SplitQ11Projectors.lean` | `advisory` | 37 | 0 | 18 | 1 | 19 |

## Findings by file

### `lean/InfoGeometry/Clifford/SplitQ11Projectors.lean`
- module: `InfoGeometry.Clifford.SplitQ11Projectors`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `simp-law-injection` in `simp-declaration jGen_mul_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L28 [soft] `simp-law-injection` in `simp-declaration epsGen_mul_jGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `simp-law-injection` in `simp-declaration kGen_mul_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration epsGen_mul_kGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration epsGen_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration epsMinusProjector_eq_half_one_sub_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `simp-law-injection` in `simp-declaration epsPlusProjector_eq_half_one_add_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `simp-law-injection` in `simp-declaration epsMinusProjector_add_epsPlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration epsMinusProjector_mul_epsPlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `simp-law-injection` in `simp-declaration epsPlusProjector_mul_epsMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration epsMinusProjector_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration epsPlusProjector_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [soft] `simp-law-injection` in `simp-declaration epsGen_mul_epsMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L160 [soft] `simp-law-injection` in `simp-declaration epsMinusProjector_mul_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L175 [soft] `simp-law-injection` in `simp-declaration epsGen_mul_epsPlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `simp-law-injection` in `simp-declaration epsPlusProjector_mul_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L205 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_epsMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_epsPlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

