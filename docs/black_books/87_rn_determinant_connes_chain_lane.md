# RN, Determinant, and Connes Chain Lane

## Why this lane exists

This lane fixes a methodological error: for noncommutative operator data,
`log (A * B) = log A + log B` is not the primary law.  
The primary laws are:

- Radon-Nikodym chain rules,
- determinant/Jacobian multiplicative character laws,
- Connes 1-cocycle chaining.

Only after these are fixed do additive scalar shadows appear.

## New formalization surface

Implemented in:

- `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean`

The file packages four connected theorem surfaces:

1. State-to-state RN chain:
   - `relativeDensity_state_chain`
2. State-to-state operator and volume chain:
   - `relativeModularOperator_state_chain`
   - `relativeModularVolumeShadow_state_chain`
   - `relativeModularVolumePotential_state_chain` (shadow)
3. Determinant/Jacobian homomorphism:
   - `jacobianDeterminant_chain`
4. Type-III Connes cocycle chaining:
   - `connesCocycle_state_chain`
   - `connesCocycle_state_chain_three`
   - `realTypeIII_flowUnit_state_chain`
   - `typeIII_connes_chain_package`

## Interpretation

The repo now has an explicit lane where composition is governed by cocycle and
character laws directly. Additive potentials remain derived shadows rather than
definitional roots.
