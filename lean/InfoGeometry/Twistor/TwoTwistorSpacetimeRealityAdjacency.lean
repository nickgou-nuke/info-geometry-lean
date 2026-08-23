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

end InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency
