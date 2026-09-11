import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace

/-!
# Certified 27-Dimensional Basis and Finrank for the Split-Albert Carrier H₃(𝕆_s)

This module provides the rigorous, kernel-checked basis construction and dimension
theorem for the 27-dimensional split-Albert Jordan carrier `H3Zorn ℝ`:

1. `reconstructH3Zorn`: Native linear reconstruction from 27 scalar coordinates.
2. `h3ZornCoordEquiv`: Complete linear equivalence `H3Zorn ℝ ≃ₗ[ℝ] (Fin 27 → ℝ)`.
3. `h3ZornBasis`: Formally certified basis `Module.Basis (Fin 27) ℝ (H3Zorn ℝ)`.
4. `finrank_h3zorn`: Kernel-checked proof that `Module.finrank ℝ (H3Zorn ℝ) = 27`.

This eliminates the structural gap concerning the dimension and basis of the carrier
space $V = H_3(\mathbb{O}_s)$ prior to evaluation of the 52 derivations of $F_4$.
-/

namespace InfoGeometry.Algebra

/-- Reconstruction map from 27 coordinates to an `H3Zorn ℝ` element. -/
def reconstructH3Zorn (v : Fin 27 → ℝ) : H3Zorn ℝ :=
  ⟨v 0, v 1, v 2,
   ⟨v 3, fun i => if i = 0 then v 4 else if i = 1 then v 5 else v 6,
         fun i => if i = 0 then v 7 else if i = 1 then v 8 else v 9, v 10⟩,
   ⟨v 11, fun i => if i = 0 then v 12 else if i = 1 then v 13 else v 14,
          fun i => if i = 0 then v 15 else if i = 1 then v 16 else v 17, v 18⟩,
   ⟨v 19, fun i => if i = 0 then v 20 else if i = 1 then v 21 else v 22,
          fun i => if i = 0 then v 23 else if i = 1 then v 24 else v 25, v 26⟩⟩

/-- Coordinate readout of a reconstructed vector is identity on `Fin 27 → ℝ`. -/
@[simp] theorem coordinate_reconstructH3Zorn (v : Fin 27 → ℝ) :
    h3ZornCoordinate (reconstructH3Zorn v) = v := by
  ext i
  fin_cases i <;> rfl

/-- Reconstructing the coordinate readout of an `H3Zorn ℝ` matrix recovers the original element. -/
@[simp] theorem reconstruct_h3ZornCoordinate (X : H3Zorn ℝ) :
    reconstructH3Zorn (h3ZornCoordinate X) = X := by
  apply H3Zorn.ext_h3 <;> try rfl
  · apply ZornVectorMatrix.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  · apply ZornVectorMatrix.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  · apply ZornVectorMatrix.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl

/-- Linearity of coordinate readout. -/
def h3ZornCoordinateLM : H3Zorn ℝ →ₗ[ℝ] (Fin 27 → ℝ) where
  toFun := h3ZornCoordinate
  map_add' X Y := by
    ext i
    fin_cases i <;> rfl
  map_smul' r X := by
    ext i
    fin_cases i <;> rfl

/-- Linearity of reconstruction. -/
def h3ZornReconstructLM : (Fin 27 → ℝ) →ₗ[ℝ] H3Zorn ℝ where
  toFun := reconstructH3Zorn
  map_add' v w := by
    apply H3Zorn.ext_h3 <;> try rfl
    · apply ZornVectorMatrix.ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    · apply ZornVectorMatrix.ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    · apply ZornVectorMatrix.ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · rfl
  map_smul' r v := by
    apply H3Zorn.ext_h3 <;> try rfl
    · apply ZornVectorMatrix.ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    · apply ZornVectorMatrix.ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    · apply ZornVectorMatrix.ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · rfl

/-- Full linear equivalence between `H3Zorn ℝ` and `ℝ²⁷`. -/
def h3ZornCoordEquiv : H3Zorn ℝ ≃ₗ[ℝ] (Fin 27 → ℝ) :=
  LinearEquiv.ofLinear h3ZornCoordinateLM h3ZornReconstructLM
    (LinearMap.ext coordinate_reconstructH3Zorn)
    (LinearMap.ext reconstruct_h3ZornCoordinate)

/-- Canonical 27-dimensional certified Basis for `H3Zorn ℝ`. -/
noncomputable def h3ZornBasis : Module.Basis (Fin 27) ℝ (H3Zorn ℝ) :=
  Module.Basis.ofEquivFun h3ZornCoordEquiv

/-- **Theorem (Exact Carrier Dimension is 27)**:
    $$\dim_{\mathbb{R}}(H_3(\mathbb{O}_s)) = 27$$
-/
theorem finrank_h3zorn : Module.finrank ℝ (H3Zorn ℝ) = 27 := by
  rw [Module.finrank_eq_card_basis h3ZornBasis]
  simp

end InfoGeometry.Algebra
