import Mathlib
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace

/-!
# Certified 27-Dimensional Basis and Finrank for the Split-Albert Carrier H₃(𝕆_s)

This module provides the coordinate equivalence and dimension certificate for
`H3Zorn ℝ`.  The inverse reconstruction is supplied directly to the linear
equivalence; a separate inverse `LinearMap` is unnecessary because linearity
is inherited from the forward linear map together with the two-sided inverse
laws.
-/

namespace InfoGeometry.Algebra

/-- Reconstruction map from 27 scalar coordinates. -/
def reconstructH3Zorn (v : Fin 27 → ℝ) : H3Zorn ℝ :=
  ⟨v 0, v 1, v 2,
   ⟨v 3, fun i => if i = 0 then v 4 else if i = 1 then v 5 else v 6,
         fun i => if i = 0 then v 7 else if i = 1 then v 8 else v 9, v 10⟩,
   ⟨v 11, fun i => if i = 0 then v 12 else if i = 1 then v 13 else v 14,
          fun i => if i = 0 then v 15 else if i = 1 then v 16 else v 17, v 18⟩,
   ⟨v 19, fun i => if i = 0 then v 20 else if i = 1 then v 21 else v 22,
          fun i => if i = 0 then v 23 else if i = 1 then v 24 else v 25, v 26⟩⟩

@[simp] theorem coordinate_reconstructH3Zorn (v : Fin 27 → ℝ) :
    h3ZornCoordinate (reconstructH3Zorn v) = v := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem reconstruct_h3ZornCoordinate (X : H3Zorn ℝ) :
    reconstructH3Zorn (h3ZornCoordinate X) = X := by
  apply H3Zorn.ext_h3 <;> try rfl
  all_goals
    apply ZornVectorMatrix.ext <;>
      first
      | rfl
      | (intro i; fin_cases i <;> rfl)

/-- Coordinate readout as a linear map. -/
def h3ZornCoordinateLM : H3Zorn ℝ →ₗ[ℝ] (Fin 27 → ℝ) where
  toFun := h3ZornCoordinate
  map_add' X Y := by ext i; fin_cases i <;> rfl
  map_smul' r X := by ext i; fin_cases i <;> rfl

/-- Full linear equivalence `H3Zorn ℝ ≃ₗ ℝ²⁷`.

The inverse is supplied as the set-theoretic reconstruction map; no duplicate
inverse linear map or inverse-linearity proof is required. -/
def h3ZornCoordEquiv : H3Zorn ℝ ≃ₗ[ℝ] (Fin 27 → ℝ) :=
  { h3ZornCoordinateLM with
    invFun := reconstructH3Zorn
    left_inv := reconstruct_h3ZornCoordinate
    right_inv := coordinate_reconstructH3Zorn }

/-- Canonical coordinate basis of the 27-dimensional carrier. -/
noncomputable def h3ZornBasis : Basis (Fin 27) ℝ (H3Zorn ℝ) :=
  Basis.ofEquivFun h3ZornCoordEquiv

/-- Exact real dimension of the split-Albert carrier. -/
theorem finrank_h3zorn : Module.finrank ℝ (H3Zorn ℝ) = 27 := by
  rw [Module.finrank_eq_card_basis h3ZornBasis]
  simp

end InfoGeometry.Algebra
