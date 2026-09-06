import InfoGeometry.Twistor.TwoTwistorSpacetimeNode
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Reality and null adjacency for two-twistor incidence

This owner records consequences of the existing Penrose incidence map.  It
does not introduce a second twistor carrier, a connection, or a holonomy
interpretation.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeNode
open Matrix

def IsHermitianSpacetime (X : ComplexSpacetime) : Prop :=
  Xᴴ = X

def HasRealCommonNode (Z₁ Z₂ : Twistor4) : Prop :=
  ∃ X : ComplexSpacetime,
    IsHermitianSpacetime X ∧
      incidenceLinearMap X Z₁.2 = Z₁ ∧
      incidenceLinearMap X Z₂.2 = Z₂

theorem shared_twistor_mulVec_eq
    (Z : Twistor4) (X Y : ComplexSpacetime)
    (hX : incidenceLinearMap X Z.2 = Z)
    (hY : incidenceLinearMap Y Z.2 = Z) :
    Matrix.mulVec X Z.2 = Matrix.mulVec Y Z.2 := by
  funext a
  have hx := congrFun (congrArg Prod.fst hX) a
  have hy := congrFun (congrArg Prod.fst hY) a
  have hxy :
      Complex.I * (X a 0 * Z.2 0 + X a 1 * Z.2 1) =
        Complex.I * (Y a 0 * Z.2 0 + Y a 1 * Z.2 1) := by
    simpa [incidenceLinearMap_apply, omegaLinearMap_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hx.trans hy.symm
  have hc :
      X a 0 * Z.2 0 + X a 1 * Z.2 1 =
        Y a 0 * Z.2 0 + Y a 1 * Z.2 1 := by
    exact mul_left_cancel₀ (by norm_num : (Complex.I : ℂ) ≠ 0) hxy
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hc

theorem shared_twistor_difference_mulVec_zero
    (Z : Twistor4) (X Y : ComplexSpacetime)
    (hX : incidenceLinearMap X Z.2 = Z)
    (hY : incidenceLinearMap Y Z.2 = Z) :
    Matrix.mulVec (X - Y) Z.2 = 0 := by
  rw [Matrix.sub_mulVec, shared_twistor_mulVec_eq Z X Y hX hY]
  exact sub_self _

theorem det_sub_eq_zero_of_shared_nonzero_twistor
    (Z : Twistor4) (X Y : ComplexSpacetime)
    (hπ : Z.2 ≠ 0)
    (hX : incidenceLinearMap X Z.2 = Z)
    (hY : incidenceLinearMap Y Z.2 = Z) :
    Matrix.det (X - Y) = 0 := by
  by_contra hdet
  have hunit : IsUnit (Matrix.det (X - Y)) :=
    isUnit_iff_ne_zero.mpr hdet
  have hker : Matrix.mulVec (X - Y) Z.2 = 0 :=
    shared_twistor_difference_mulVec_zero Z X Y hX hY
  have hback := congrArg (Matrix.mulVec (X - Y)⁻¹) hker
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (X - Y) hunit,
    Matrix.one_mulVec] at hback
  simp at hback
  exact hπ hback

theorem adjacent_reconstructed_nodes_det_difference_zero
    (P₁ Ω₁ P₂ Ω₂ : ComplexSpacetime)
    (hP₁ : IsUnit P₁.det) (hP₂ : IsUnit P₂.det)
    (hπ : P₁.mulVec ![0, 1] ≠ 0)
    (hshared : P₁.mulVec ![0, 1] = P₂.mulVec ![1, 0])
    (hωshared : Ω₁.mulVec ![0, 1] = Ω₂.mulVec ![1, 0]) :
    Matrix.det (frameSpacetimeNode P₁ Ω₁ - frameSpacetimeNode P₂ Ω₂) = 0 := by
  let Z : Twistor4 := (Ω₁.mulVec ![0, 1], P₁.mulVec ![0, 1])
  apply det_sub_eq_zero_of_shared_nonzero_twistor Z
    (frameSpacetimeNode P₁ Ω₁) (frameSpacetimeNode P₂ Ω₂) hπ
  · exact frameSpacetimeNode_incidence P₁ Ω₁ hP₁ ![0, 1]
  · change incidenceLinearMap (frameSpacetimeNode P₂ Ω₂)
      (P₁.mulVec ![0, 1]) =
        (Ω₁.mulVec ![0, 1], P₁.mulVec ![0, 1])
    rw [hshared, hωshared]
    exact frameSpacetimeNode_incidence P₂ Ω₂ hP₂ ![1, 0]

theorem reconstructed_nodes_form_complex_null_triangle
    (P₁₂ Ω₁₂ P₂₃ Ω₂₃ P₃₁ Ω₃₁ : ComplexSpacetime)
    (hP₁₂ : IsUnit P₁₂.det) (hP₂₃ : IsUnit P₂₃.det)
    (hP₃₁ : IsUnit P₃₁.det)
    (hπ₂ : P₁₂.mulVec ![0, 1] ≠ 0)
    (hπ₃ : P₂₃.mulVec ![0, 1] ≠ 0)
    (hπ₁ : P₃₁.mulVec ![0, 1] ≠ 0)
    (h₁₂₂₃ : P₁₂.mulVec ![0, 1] = P₂₃.mulVec ![1, 0])
    (hω₁₂₂₃ : Ω₁₂.mulVec ![0, 1] = Ω₂₃.mulVec ![1, 0])
    (h₂₃₃₁ : P₂₃.mulVec ![0, 1] = P₃₁.mulVec ![1, 0])
    (hω₂₃₃₁ : Ω₂₃.mulVec ![0, 1] = Ω₃₁.mulVec ![1, 0])
    (h₃₁₁₂ : P₃₁.mulVec ![0, 1] = P₁₂.mulVec ![1, 0])
    (hω₃₁₁₂ : Ω₃₁.mulVec ![0, 1] = Ω₁₂.mulVec ![1, 0]) :
    Matrix.det (frameSpacetimeNode P₁₂ Ω₁₂ - frameSpacetimeNode P₂₃ Ω₂₃) = 0 ∧
    Matrix.det (frameSpacetimeNode P₂₃ Ω₂₃ - frameSpacetimeNode P₃₁ Ω₃₁) = 0 ∧
    Matrix.det (frameSpacetimeNode P₃₁ Ω₃₁ - frameSpacetimeNode P₁₂ Ω₁₂) = 0 := by
  exact ⟨
    adjacent_reconstructed_nodes_det_difference_zero
      P₁₂ Ω₁₂ P₂₃ Ω₂₃ hP₁₂ hP₂₃ hπ₂ h₁₂₂₃ hω₁₂₂₃,
    adjacent_reconstructed_nodes_det_difference_zero
      P₂₃ Ω₂₃ P₃₁ Ω₃₁ hP₂₃ hP₃₁ hπ₃ h₂₃₃₁ hω₂₃₃₁,
    adjacent_reconstructed_nodes_det_difference_zero
      P₃₁ Ω₃₁ P₁₂ Ω₁₂ hP₃₁ hP₁₂ hπ₁ h₃₁₁₂ hω₃₁₁₂⟩

end InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency
