# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:30.900134+00:00`
Root: `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **16**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/CentralExtension.lean` | `advisory` | 36 | 0 | 16 | 4 | 20 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`
- module: `InfoGeometry.External.Virasoro.CentralExtension`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `simp-law-injection` in `simp-declaration coeProd_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `lemma smul_def` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration zero_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration zero_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `simp-law-injection` in `simp-declaration add_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration add_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration smul_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `simp-law-injection` in `simp-declaration smul_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration bracket_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `skeletal-proof` in `lemma bracket_smul` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `lemma bracket_leibniz` — proof appears to close via minimal tactic one-liner
  - L147 [soft] `skeletal-proof` in `lemma lie_def` — proof appears to close via minimal tactic one-liner
  - L151 [soft] `simp-law-injection` in `simp-declaration lie_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L155 [soft] `simp-law-injection` in `simp-declaration lie_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L215 [soft] `skeletal-proof` in `lemma congr_apply` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `simp-law-injection` in `simp-declaration congr_trans` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L255 [advisory] `local-hypothesis-injection` in `def equiv_of_lieTwoCoboundary` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L258 [advisory] `local-hypothesis-injection` in `def equiv_of_lieTwoCoboundary` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

