/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovNaturalGradientMetric
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Riesz representation for the full-matrix Markov pairing

For strictly positive stationary weights, every algebraic linear objective on
the full matrix carrier has a unique representative under the stationary-
weighted Frobenius pairing. The representative is then projected by the
already-defined Markov submersion split; on horizontal test matrices its
pairing agrees with the original objective. This is a finite-dimensional
Riesz theorem for the ambient positive pairing, not an inverse of the
degenerate Markov Laplacian.

Ground-truth refinement ladder:
`weightedMatrixPairing` and `weightedMatrixBilin` are the existing full-matrix
owners (`MarkovMetriplecticFlowBridge.lean` and
`MarkovNaturalGradientSubmersion.lean`); strict positivity and left
nondegeneracy are proved in `MarkovNaturalGradientMetric.lean`; Mathlib's
`LinearMap.BilinForm.toDual` transports that nondegenerate bilinear form to the
algebraic dual; its inverse is the full-matrix representative; finally the
existing `NaturalGradientSubmersionSystem` horizontal projection restricts
the representing identity to horizontal tests. The new delta is precisely
this dual representative and its projected variational identity. No claim is
made that the Markov Laplacian itself is invertible or that the projected
representative is a dynamical flow.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.NaturalGradientSubmersionFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strict positivity makes the full-matrix stationary-weighted bilinear form
nondegenerate on both sides. The right-separating half uses symmetry of the
pairing, while the left-separating half is the existing full-matrix result. -/
theorem weightedMatrixBilin_nondegenerate
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    (weightedMatrixBilin π).Nondegenerate := by
  constructor
  · intro X hXY
    apply weightedMatrixPairing_nondegenerate π hπ X
    intro Y
    exact hXY Y
  · intro Y hXY
    apply weightedMatrixPairing_nondegenerate π hπ Y
    intro X
    rw [weightedMatrixPairing_comm π Y X]
    exact hXY X

/-- The Riesz equivalence for the weighted pairing on the entire matrix
module. Its inverse sends a linear objective to its unique representing
matrix. -/
noncomputable def weightedMatrixRieszEquiv
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    Matrix ι ι ℝ ≃ₗ[ℝ] Module.Dual ℝ (Matrix ι ι ℝ) :=
  (weightedMatrixBilin π).toDual (weightedMatrixBilin_nondegenerate π hπ)

/-- Construct the full-matrix representative of a linear objective. -/
noncomputable def weightedMatrixGradient
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (objective : Module.Dual ℝ (Matrix ι ι ℝ)) : Matrix ι ι ℝ :=
  (weightedMatrixRieszEquiv π hπ).symm objective

/-- The constructed matrix represents the objective against every full
matrix test direction. -/
theorem weightedMatrixGradient_represents
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (objective : Module.Dual ℝ (Matrix ι ι ℝ))
    (Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π (weightedMatrixGradient π hπ objective) Y =
      objective Y := by
  change weightedMatrixBilin π
      ((weightedMatrixRieszEquiv π hπ).symm objective) Y = objective Y
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ Y

/-- Uniqueness of the representing matrix on the full noncommutative matrix
carrier. -/
theorem weightedMatrixGradient_unique
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (objective : Module.Dual ℝ (Matrix ι ι ℝ))
    (X : Matrix ι ι ℝ)
    (hX : ∀ Y, weightedMatrixPairing π X Y = objective Y) :
    X = weightedMatrixGradient π hπ objective := by
  apply (weightedMatrixRieszEquiv π hπ).injective
  ext Y
  change weightedMatrixPairing π X Y =
    weightedMatrixPairing π
      (weightedMatrixGradient π hπ objective) Y
  rw [hX Y, weightedMatrixGradient_represents π hπ objective Y]

/-- The Markov submersion projects the Riesz representative to a horizontal
representative. Its pairing against any horizontal test equals the original
objective on that test. -/
theorem markovHorizontalGradient_represents
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i)
    (objective : Module.Dual ℝ (Matrix ι ι ℝ))
    (Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π
      ((markovNaturalGradientSubmersionSystem P π hP hDB).split.projH
        (weightedMatrixGradient π hπ objective))
      ((markovNaturalGradientSubmersionSystem P π hP hDB).split.projH Y) =
    objective ((markovNaturalGradientSubmersionSystem P π hP hDB).split.projH Y) := by
  have hIso := natural_gradient_horizontal_isolation
    (markovNaturalGradientSubmersionSystem P π hP hDB)
    (weightedMatrixGradient π hπ objective) Y
  change weightedMatrixPairing π
      (weightedMatrixGradient π hπ objective)
      ((markovNaturalGradientSubmersionSystem P π hP hDB).split.projH Y) =
    weightedMatrixPairing π
      ((markovNaturalGradientSubmersionSystem P π hP hDB).split.projH
        (weightedMatrixGradient π hπ objective))
      ((markovNaturalGradientSubmersionSystem P π hP hDB).split.projH Y) at hIso
  rw [← hIso, weightedMatrixGradient_represents]

end InfoGeometry.QuantumContext.MarkovDrazin

end
