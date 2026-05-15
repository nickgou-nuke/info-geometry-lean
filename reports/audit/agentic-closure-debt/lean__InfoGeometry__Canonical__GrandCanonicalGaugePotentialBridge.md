# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:11.665194+00:00`
Root: `lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **7**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean` | `advisory` | 19 | 0 | 7 | 5 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean`
- module: `InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `simp-law-injection` in `simp-declaration chemicalPotentialGauge_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `skeletal-proof` in `theorem chemicalPotentialGauge_apply` — proof appears to close via minimal tactic one-liner
  - L47 [soft] `skeletal-proof` in `theorem shiftedEnergy_eq_energy_sub_chemicalPotentialGauge` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `skeletal-proof` in `theorem grandCanonicalGaugeKernelExponent_eq` — proof appears to close via minimal tactic one-liner
  - L88 [advisory] `existential-packaging` in `def grandCanonicalMassieuPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [advisory] `existential-packaging` in `theorem grandCanonicalMassieuPotential_eq_potentialGC` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [soft] `skeletal-proof` in `theorem grandCanonicalMassieuPotential_eq_potentialGC` — proof appears to close via minimal tactic one-liner
  - L106 [advisory] `existential-packaging` in `theorem chemicalPotential_conjugate_count_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L106 [soft] `skeletal-proof` in `theorem chemicalPotential_conjugate_count_readout` — proof appears to close via minimal tactic one-liner
  - L119 [advisory] `existential-packaging` in `theorem inverseTemperature_conjugate_shiftedEnergy_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L119 [soft] `skeletal-proof` in `theorem inverseTemperature_conjugate_shiftedEnergy_readout` — proof appears to close via minimal tactic one-liner

