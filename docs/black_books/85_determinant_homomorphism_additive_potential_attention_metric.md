# Determinant Homomorphism as Additive Potential in the Attention-Metric Lane

## Thesis

The stable finite owner lane already encodes the key translation:

- multiplicative operator composition,
- to multiplicative scalar shadow (`det`-style volume character),
- to additive potential (`-log` readout),
- then to Hamiltonian readout.

This is the strict, compiled version of “noncommutative multiplicative geometry
heard as additive potential.”

## What Is Proved in Repo

### 1. Multiplicative operator owner (`Δ`)

- [`relativeModularOperator`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:100)
- cocycle:
  [`relativeModularOperator_cocycle`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:168)

### 2. Multiplicative scalar shadow (determinant character)

- [`relativeModularVolumeShadow`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:188)
- cocycle:
  [`relativeModularVolumeShadow_cocycle`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:222)

### 3. Additive potential (`-log` of volume shadow)

- [`relativeModularVolumePotential`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:235)
- additive decomposition:
  [`relativeModularVolumePotential_eq_sum_relativeModularPotential`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:255)

### 4. Hamiltonian readout

- [`relativeModularHamiltonianReadout`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:349)
- link to volume potential:
  [`relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:373)

## Attention-Metric Link (Finite Thermodynamic Lane)

The attention surface is encoded thermodynamically via Gibbs/softmax bridges:

- [`gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean:78)
- row-stochastic attention matrix ownership:
  [`polarizedPlusAttentionMatrix_mem_rowStochastic`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean:65)

Log-det thermodynamic energy is exposed in:

- [`energyFromLogDet`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Thermo/FromLogDet.lean:16)
- [`freeEnergyFromLogDet`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Thermo/FromLogDet.lean:29)

## New Structural Upgrade in This Pass

Support/domain surrogate for `K := -log Δ` is now formalized:

- [`supportRestrictedModularHamiltonianOperator`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:37)
- support compression identities:
  [`supportRestrictedModularHamiltonianOperator_eq_supportProjector_mul`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:59),
  [`supportRestrictedModularHamiltonianOperator_eq_mul_supportProjector`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:76)
- support-restricted cocycle:
  [`supportRestrictedModularHamiltonianOperator_cocycle`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:139)

## Boundary Law

This chapter is finite-lane factual. It does **not** claim full unbounded
Tomita–Takesaki logarithmic functional calculus in-core. The support-restricted
lane is a strict owner bridge, not a replacement for the Type III unbounded
operator stack.

