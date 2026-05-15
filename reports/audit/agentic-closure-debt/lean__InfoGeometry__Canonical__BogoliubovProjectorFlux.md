# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.865194+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **33**
- Hard: **0**
- Soft: **20**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean` | `advisory` | 53 | 0 | 20 | 13 | 33 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean`
- module: `InfoGeometry.Canonical.BogoliubovProjectorFlux`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [soft] `skeletal-proof` in `theorem epsilonBoost_comp_spectralPlusProj` — proof appears to close via minimal tactic one-liner
  - L46 [advisory] `local-hypothesis-injection` in `theorem epsilonBoost_comp_spectralPlusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [soft] `skeletal-proof` in `theorem epsilonBoost_comp_spectralMinusProj` — proof appears to close via minimal tactic one-liner
  - L64 [advisory] `local-hypothesis-injection` in `theorem epsilonBoost_comp_spectralMinusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L83 [advisory] `local-hypothesis-injection` in `theorem JBoost_comp_spectralPlusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [soft] `skeletal-proof` in `theorem JBoost_comp_spectralPlusProj_modular_j` — proof appears to close via minimal tactic one-liner
  - L102 [advisory] `local-hypothesis-injection` in `theorem JBoost_comp_spectralMinusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [soft] `skeletal-proof` in `theorem JBoost_comp_spectralMinusProj_modular_j` — proof appears to close via minimal tactic one-liner
  - L121 [advisory] `local-hypothesis-injection` in `theorem KRotation_comp_spectralPlusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [soft] `skeletal-proof` in `theorem KRotation_comp_spectralPlusProj_complex_i` — proof appears to close via minimal tactic one-liner
  - L140 [advisory] `local-hypothesis-injection` in `theorem KRotation_comp_spectralMinusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [soft] `skeletal-proof` in `theorem KRotation_comp_spectralMinusProj_complex_i` — proof appears to close via minimal tactic one-liner
  - L151 [soft] `simp-law-injection` in `simp-declaration transportedPlusProjector_epsilonBoost` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L157 [soft] `simp-law-injection` in `simp-declaration transportedMinusProjector_epsilonBoost` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [soft] `simp-law-injection` in `simp-declaration transportedPlusProjector_JBoost` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration transportedPlusProjector_JBoost_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L175 [soft] `simp-law-injection` in `simp-declaration transportedMinusProjector_JBoost` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `simp-law-injection` in `simp-declaration transportedMinusProjector_JBoost_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L187 [soft] `simp-law-injection` in `simp-declaration transportedPlusProjector_KRotation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L193 [soft] `simp-law-injection` in `simp-declaration transportedPlusProjector_KRotation_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L200 [soft] `simp-law-injection` in `simp-declaration transportedMinusProjector_KRotation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L206 [soft] `simp-law-injection` in `simp-declaration transportedMinusProjector_KRotation_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L245 [soft] `skeletal-proof` in `theorem plusProjectorFlux_JBoost_modular_j` — proof appears to close via minimal tactic one-liner
  - L267 [soft] `skeletal-proof` in `theorem minusProjectorFlux_JBoost_modular_j` — proof appears to close via minimal tactic one-liner
  - L289 [soft] `skeletal-proof` in `theorem plusProjectorFlux_KRotation_complex_i` — proof appears to close via minimal tactic one-liner
  - L311 [soft] `skeletal-proof` in `theorem minusProjectorFlux_KRotation_complex_i` — proof appears to close via minimal tactic one-liner

