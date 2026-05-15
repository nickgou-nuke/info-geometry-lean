# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:19.071841+00:00`
Root: `lean/InfoGeometry/Clifford/RealMod8Classification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **26**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/RealMod8Classification.lean` | `advisory` | 54 | 0 | 26 | 2 | 28 |

## Findings by file

### `lean/InfoGeometry/Clifford/RealMod8Classification.lean`
- module: `InfoGeometry.Clifford.RealMod8Classification`
- status: `advisory`
- debt_score: `54`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L67 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r0` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r2` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r3` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r4` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r5` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r6` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration divisionRingKind_r7` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration structuralKind_r0` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration structuralKind_r1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `simp-law-injection` in `simp-declaration structuralKind_r2` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration structuralKind_r3` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration structuralKind_r4` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `simp-law-injection` in `simp-declaration structuralKind_r5` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration structuralKind_r6` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration structuralKind_r7` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_ppp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L161 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_pmm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_mpm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L165 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_mmp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_mmm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_mpp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_pmp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `simp-law-injection` in `simp-declaration coverGroupKind_ppm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `simp-law-injection` in `simp-declaration broadAllowedSignatures_r1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [soft] `simp-law-injection` in `simp-declaration broadAllowedSignatures_r5` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L222 [advisory] `bridge-shaped-declaration` in `theorem semisimpleResidues_admit_all_signatures` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

