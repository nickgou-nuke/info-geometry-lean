# Universal Volume Stack

This is the maintained reading path for multiplicative-to-additive volume language in the current repo.

## Current owner chain

1. projective and strict-positive roots:
   - `ProjectiveStateCore`
   - `PositiveRayCore`
   - `RelativeGeneratorCore`
   - `RelativePotentialCore`
2. presentation bridges:
   - `RelativePotentialDiscreteBridge`
   - `RelativePotentialCountBridge`
   - `RelativePotentialScalarBridge`
3. umbrella export:
   - `RedLine`
4. downstream scalar and geometry consumers:
   - `KMSSinkhornScalarPotential`
   - `RicciMongeAmpere`
   - `CalabiYauRNMongeAmpere`
   - determinant/log-volume lemmas in `GrandSynthesis`

## Interpretation

In current code, the stack is:
- multiplicative relative density;
- additive log-density;
- negative log modular potential;
- representation-specific lifts in count, scalar, geometry, and operator settings.

## Non-claim

This file is a maintained code map. It is not a claim that every consumer has already been fully deduplicated onto one final abstraction.
