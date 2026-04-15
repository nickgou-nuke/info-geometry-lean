# First Quantization of Probability: Dictionary Closure

## Thesis

The finite owner lane now compiles the substitution dictionary:

- density ratio `λ = p/q` -> relative modular operator `Δ`,
- surprisal `-log λ` -> relative modular Hamiltonian readout `K = -log Δ`,
- classical expectation -> operator/vacuum expectation pairing.

## Compiled Owner Surface

New owner file:

- [FirstQuantizationProbability.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:1)

Core declarations:

- [quantizedDensityRatioOperator_eq_relativeModularOperator](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:54)
- [classicalSurprisal_eq_relativeModularPotential](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:68)
- [quantizedSurprisalOperator_eq_relativeModularPotentialOperator](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:87)
- [relativeModularHamiltonianOperator_eq_quantizedSurprisalOperator](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:105)
- [classicalExpectation_eq_diagonalExpectation_firstQuantize](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:138)
- [vacuumExpectation_eq_inner](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:164)
- [firstQuantization_dictionary](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:179)

## Interpretation Law

This lane does not claim full Type-III unbounded affiliated-operator closure.
It formalizes the finite compiled dictionary and its standard-form expectation
pairing surface, while preserving the existing RN/Connes primaries.
