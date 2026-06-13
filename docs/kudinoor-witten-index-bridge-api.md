# Kudinoor Witten Index Bridge API

Source PDF inspected:

- `/home/goutev/Downloads/drazin/SupersymmetryAndTheWittenIndex.pdf`

Lean module:

- `lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean`

SymPy witness:

- `tools/sympy/kudinoor_witten_index_bridge.py`

The PDF is Arjun Kudinoor's 2023 exposition "Supersymmetry and the Witten
Index."  The finite formalized corridor is Section 1: nonzero bosonic and
fermionic energy levels pair, so the graded weighted supertrace reduces to the
zero-energy Witten index and is independent of the supplied inverse-temperature
weights.

## Theorem Surface

- `levelSuperdimension`
  defines the signed finite count `boson - fermion` at one level.

- `finiteWittenIndex`
  sums the signed count over the zero-energy levels.

- `finiteWeightedSupertrace`
  sums the signed count over all finite levels with a supplied integer weight.

- `nonzero_level_superdimension_zero`
  proves that an explicitly paired level has zero superdimension.

- `zero_weighted_level_eq_unweighted`
  proves that a zero level with weight `1` contributes its ordinary
  superdimension.

- `finiteWeightedSupertrace_eq_finiteWittenIndex`
  proves the finite supertrace collapse under explicit zero-weight and
  nonzero-pairing hypotheses.

- `finiteWeightedSupertrace_weight_independent`
  proves two normalized weights produce the same supertrace under the same
  pairing hypothesis.

- `kudinoor_finite_witten_index_capstone`
  bundles the finite collapse and weight-independence statements.

## Boundary

This is not a proof of Atiyah-Singer, McKean-Singer, heat-kernel asymptotics,
Dirac operator index theory, nonlinear sigma models, supersymmetric quantum
mechanics on Hilbert spaces, or any physical/RH consequence.  It is a finite
graded-spectrum cancellation theorem.
