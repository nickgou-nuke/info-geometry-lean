# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:56.349642+00:00`
Root: `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **19**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean` | `advisory` | 44 | 0 | 19 | 6 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`
- module: `InfoGeometry.Canonical.ConnesArakiTomita`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L103 [advisory] `existential-packaging` in `theorem tomitaFiniteDiagonalLane_shadow_alias` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L103 [soft] `skeletal-proof` in `theorem tomitaFiniteDiagonalLane_shadow_alias` — proof appears to close via minimal tactic one-liner
  - L115 [advisory] `existential-packaging` in `theorem tomitaFiniteDiagonalLane_shadow_marker` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [soft] `skeletal-proof` in `theorem tomitaFiniteDiagonalLane_shadow_marker` — proof appears to close via minimal tactic one-liner
  - L125 [advisory] `existential-packaging` in `theorem tomitaFiniteDiagonalLane_shadow_projection_only` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L125 [soft] `skeletal-proof` in `theorem tomitaFiniteDiagonalLane_shadow_projection_only` — proof appears to close via minimal tactic one-liner
  - L136 [advisory] `existential-packaging` in `theorem tomitaFiniteDiagonalLane_shadow_projection_channel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L136 [soft] `skeletal-proof` in `theorem tomitaFiniteDiagonalLane_shadow_projection_channel` — proof appears to close via minimal tactic one-liner
  - L147 [soft] `simp-law-injection` in `simp-declaration tomita_modularSignAdditiveModularFlow_map_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `simp-law-injection` in `simp-declaration tomitaUnitConnesAraki_flowUnitCocycle_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `simp-law-injection` in `simp-declaration tomitaUnitConnesAraki_flowUnitCocycle_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L191 [soft] `simp-law-injection` in `simp-declaration tomitaUnitConnesAraki_flowUnitCocycle_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L201 [soft] `simp-law-injection` in `simp-declaration tomitaUnit_connesAraki_flowUnitCocycle_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `simp-law-injection` in `simp-declaration tomitaUnitConnesAraki_flowUnitCocycle_shadow_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L221 [soft] `skeletal-proof` in `theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_readout_eq_one` — proof appears to close via minimal tactic one-liner
  - L231 [soft] `skeletal-proof` in `theorem tomitaUnitConnesAraki_flowUnitCocycle_cocycle` — proof appears to close via minimal tactic one-liner
  - L242 [soft] `skeletal-proof` in `theorem tomitaUnit_connesAraki_flowUnitCocycle_isConnesCocycle` — proof appears to close via minimal tactic one-liner
  - L314 [soft] `skeletal-proof` in `theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_isConnesCocycle` — proof appears to close via minimal tactic one-liner
  - L327 [soft] `simp-law-injection` in `simp-declaration tomitaUnitConnesArakiData_scalarCocycle_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L393 [advisory] `bridge-shaped-declaration` in `theorem tomitaUnitConnesArakiDataOfCasini_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L393 [soft] `skeletal-proof` in `theorem tomitaUnitConnesArakiDataOfCasini_bridge` — proof appears to close via minimal tactic one-liner
  - L417 [soft] `simp-law-injection` in `simp-declaration tomitaUnitConnesArakiDataOfCasini_relEnt` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L438 [soft] `skeletal-proof` in `theorem tomitaUnitConnesArakiDataOfCasini_casini` — proof appears to close via minimal tactic one-liner
  - L507 [soft] `skeletal-proof` in `theorem topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData_root` — proof appears to close via minimal tactic one-liner

