# Gull-Doran Pseudoscalar Bridge API

Lean module:

- `lean/InfoGeometry/Clifford/GullDoranPseudoscalarBridge.lean`

SymPy witness:

- `tools/sympy/gull_doran_pseudoscalar_bridge.py`

This module records the finite theorem-backed fragment of the
Gull-Lasenby-Doran geometric-algebra dictionary: the scalar imaginary phase
can be represented as a Clifford pseudoscalar in the concrete Pauli matrix
model, and the same phase has a real `4 x 4` matrix realification.

## Theorem Surface

- `pauli_sigma1_sq`, `pauli_sigma2_sq`, `pauli_sigma3_sq`
  prove the three Pauli generators square to the identity.

- `pauli_sigma1_sigma2_anticomm`,
  `pauli_sigma1_sigma3_anticomm`,
  `pauli_sigma2_sigma3_anticomm`
  prove the finite Clifford anticommutation table.

- `pauli_pseudoscalar_eq_complex_phase`
  proves `sigma1 * sigma2 * sigma3 = I • 1`.

- `pauli_pseudoscalar_sq`
  proves the Pauli pseudoscalar squares to `-1`.

- `realPhaseAxis`
  is the real `4 x 4` block representation of complex multiplication by `I`
  on two complex coordinates.

- `realSigma1`, `realSigma2`, `realSigma3`
  are the realifications of the three Pauli generators.

- `realSigma1_sq`, `realSigma2_sq`, `realSigma3_sq`
  prove the realified generators square to the identity.

- `realSigma1_realSigma2_anticomm`,
  `realSigma1_realSigma3_anticomm`,
  `realSigma2_realSigma3_anticomm`
  prove the realified Clifford anticommutation table.

- `real_pseudoscalar_eq_phaseAxis`
  proves the realified Pauli volume product is the real phase axis.

- `real_pseudoscalar_sq`
  proves that realified volume product squares to `-1`.

- `gull_doran_pseudoscalar_capstone`
  bundles the finite complex Pauli and realified phase-axis identities.

## Boundary

This is not a formalization of spacetime algebra as a continuum field theory.
It does not prove Maxwell equations, the Dirac equation, rotor/spinor
analysis, geometric calculus, STA dynamics, or any Riemann Hypothesis
consequence.  It proves only the finite matrix pseudoscalar corridor.
