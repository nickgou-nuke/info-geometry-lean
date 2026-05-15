# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:14.771704+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesPhaseSpectral.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **8**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesPhaseSpectral.lean` | `advisory` | 25 | 0 | 8 | 9 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesPhaseSpectral.lean`
- module: `InfoGeometry.Canonical.HestenesPhaseSpectral`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [soft] `skeletal-proof` in `theorem eigenvector_phaseAxis_of_hestenesLinear` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem phaseAxis_mapsTo_eigenspace_of_hestenesLinear` — proof appears to close via minimal tactic one-liner
  - L77 [advisory] `local-hypothesis-injection` in `theorem phaseAxis_mapsTo_eigenspace_of_hestenesLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L79 [advisory] `local-hypothesis-injection` in `theorem phaseAxis_mapsTo_eigenspace_of_hestenesLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L82 [soft] `skeletal-proof` in `theorem commuting_antilinear_preserves_real_eigenspace` — proof appears to close via minimal tactic one-liner
  - L96 [advisory] `local-hypothesis-injection` in `theorem commuting_antilinear_preserves_real_eigenspace` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [soft] `skeletal-proof` in `theorem anticommuting_antilinear_flips_real_eigenvalue` — proof appears to close via minimal tactic one-liner
  - L115 [advisory] `local-hypothesis-injection` in `theorem anticommuting_antilinear_flips_real_eigenvalue` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L117 [advisory] `local-hypothesis-injection` in `theorem anticommuting_antilinear_flips_real_eigenvalue` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L124 [soft] `skeletal-proof` in `theorem isPhaseLinear_comp` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `theorem spectral_projector_isHestenesLinear` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `theorem certifiedConformal_A_isPhaseLinear_of_kreinCompat` — proof appears to close via minimal tactic one-liner
  - L216 [soft] `skeletal-proof` in `theorem certifiedConformal_AD_isPhaseLinear_of_kreinCompat` — proof appears to close via minimal tactic one-liner

