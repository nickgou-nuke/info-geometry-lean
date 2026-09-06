import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# Concrete S_left / clockAxis commutation on DoubledSpace ℝ

#### BUCKET 1: CLOSED FINITE THEOREMS
None in this file.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None in this file.

#### BUCKET 3: OPEN CLOSURE DEBT
- Construct the full tensor-product Hilbert representation
  `ℓ²(CantorBoundary) ⊗ DoubledSpace ℝ`.
- Prove the tensor-factor separation identity
  `(S_left ⊗ Id) * (Id ⊗ K) = (Id ⊗ K) * (S_left ⊗ Id)`.
- Transport that identity to the `KLinear` premise used by the
  `e₂` self-adjointness chain.

This file used to contain a theorem claiming

```lean
M.cuntz.S_left * canonicalRealDoubledPhaseAxis =
  canonicalRealDoubledPhaseAxis * M.cuntz.S_left
```

for an arbitrary `RealDoubledCuntzMajoranaPacket`. That statement was not a
closed theorem: the file itself explains that the corresponding single-fiber
matrix calculation is false. Keeping it as an unfinished theorem would
therefore hide open representation debt behind a false proof surface.

## Concrete representation

On DoubledSpace ℝ = ℝ² with the standard basis, the operators are:

  clockAxis = [[0, -1], [1, 0]]    (complex structure, K² = -1, isometry ‖K‖ = 1)
  S_left    = [[1, 0], [0, 0]]     (Cuntz left projection)

  S_left · clockAxis = [[0, -1], [0, 0]]
  clockAxis · S_left = [[0, 0], [1, 0]]
  Therefore: S_left · clockAxis ≠ clockAxis · S_left

The commutation FAILS on the 2×2 fiber!

## Resolution

The commutation S_left · K = K · S_left is NOT true on the single-doubled
fiber alone.  It holds only on the FULL Hilbert space

  H = ℓ²(CantorBoundary) ⊗ DoubledSpace ℝ

where S_left acts on the base (Cantor boundary) as the shift and K acts
on the fiber.  The commutation is:

  (S_left ⊗ Id) · (Id ⊗ K) = (Id ⊗ K) · (S_left ⊗ Id)

This is the tensor-factor separation.  The KLinear predicate on EndH
alone cannot prove this — it requires the full tensor product.

## The closed chain

The remaining KLinear S_left property cannot be proved on the abstract
EndH level.  It requires either:

1. The concrete tensor product construction H = ℓ²(CantorBoundary) ⊗ ℂ²
2. Acceptance as an explicit structural premise of the spectral triple model

The theorem chain is complete CONDITIONAL on KLinear S_left, which is
true by construction of the Cuntz/Cantor spectral triple.
-/
