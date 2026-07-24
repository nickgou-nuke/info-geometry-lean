# QUARANTINED: SplitQuaternionCore.lean

## Date: 2026-07-19

## Reason for quarantine

File uses `sorry` (lines 97, 127) and has type-class synthesis failures:
- `NonUnitalNonAssocRing (Canonical.ZornMatrix ℝ)` not found
- `Module ℝ CZ` not found
- Unknown identifier `i` (lines 135, 136)

Violates theorem-safe discipline (No `sorry`/`admit`). Quarantined until fixed.
