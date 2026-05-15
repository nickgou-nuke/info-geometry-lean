# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:19.846835+00:00`
Root: `lean/InfoGeometry/Clifford/SplitQ11PhaseFlip.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **17**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/SplitQ11PhaseFlip.lean` | `advisory` | 39 | 0 | 17 | 5 | 22 |

## Findings by file

### `lean/InfoGeometry/Clifford/SplitQ11PhaseFlip.lean`
- module: `InfoGeometry.Clifford.SplitQ11PhaseFlip`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L57 [soft] `simp-law-injection` in `simp-declaration jGen_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration kGen_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration jGen_mul_kGen_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [advisory] `local-hypothesis-injection` in `def nullPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [soft] `simp-law-injection` in `simp-declaration kGen_mul_jGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration nullMinus_eq_half_jGen_add_kGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [advisory] `local-hypothesis-injection` in `def nullPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L86 [soft] `simp-law-injection` in `simp-declaration nullPlus_eq_half_jGen_sub_kGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [advisory] `local-hypothesis-injection` in `def nullPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [soft] `simp-law-injection` in `simp-declaration nullMinus_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `simp-law-injection` in `simp-declaration nullPlus_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `simp-law-injection` in `simp-declaration nullMinus_mul_nullPlus_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [advisory] `local-hypothesis-injection` in `def nullPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L155 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_nullMinusVec` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_nullPlusVec` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_jGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L175 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_kGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L187 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L192 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_nullMinus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L196 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_nullPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

