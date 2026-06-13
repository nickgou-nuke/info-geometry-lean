# Cuntz Weyl UHF Bridge API

Finite bridge between a hyperbolic `Z₂` grading and a Cuntz-style left shift.

## Owner file

- `lean/InfoGeometry/Canonical/CuntzWeylUHFBridge.lean`

## What is proved

- `weyl_cuntz_reflection_invariance`
  - If the left shift is declared odd with respect to the induced grading, the
    reflection parity relation is exactly the same statement.
- `weyl_signum_cuntz_parity_match`
  - A linear trace functional carries the same sign change through the bridge.

## What is not proved

- No derivation of the grading from the conformal null-pair lane.
- No global Weyl-group theorem.
- No analytic zeta identity.

This is a finite assumption-carrying owner surface, not a continuum theorem.
