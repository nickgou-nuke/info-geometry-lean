# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:32.777222+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimeBitWittenIndex.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimeBitWittenIndex.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimeBitWittenIndex.lean`
- module: `InfoGeometry.Arithmetic.PrimeBitWittenIndex`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field PrimeRegister.prime_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `skeletal-proof` in `theorem mobius_prime_product_eq_parity` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `theorem mobius_representedNat_eq_fermionParity` — proof appears to close via minimal tactic one-liner
  - L144 [soft] `skeletal-proof` in `theorem mobius_representedNatOfState_eq_fermionParity` — proof appears to close via minimal tactic one-liner
  - L171 [advisory] `existential-packaging` in `theorem finite_witten_index_cancel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L185 [advisory] `existential-packaging` in `theorem finite_witten_supertrace_cancel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L195 [advisory] `existential-packaging` in `theorem finite_divisor_mobius_sum_cancel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

