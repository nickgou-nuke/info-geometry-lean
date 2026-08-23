import InfoGeometry.Twistor.TwoTwistorSpacetimeNode
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Reality and adjacent null edges for reconstructed twistor nodes

This owner adds two theorem-level consequences of the two-twistor spacetime
node construction.

1. A pair of independent twistors determines a *real* Minkowski-type node
   exactly when its unique reconstructed complex spacetime matrix is Hermitian.
   The definition is incidence-based, so it does not depend on choosing a
   second, potentially incompatible, Hermitian form on twistor coordinates.

2. Two spacetime matrices incident with the same nonzero lower spinor differ
   by a singular matrix.  Applied to reconstructed nodes `X₁₂` and `X₂₃`, this
   gives the exact null-edge determinant condition

   `det (X₁₂ - X₂₃) = 0`.

This is finite incidence geometry.  No connection, holonomy, curvature, or
birefringence claim is made here.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeNode
open Matrix

/-- A complex spacetime matrix represents a real node when it is Hermitian. -/
def IsHermitianSpacetime (X : ComplexSpacetime) : Prop :=
  Xᴴ = X

/-- Two twistors admit a real common spacetime node when there exists a
Hermitian spacetime matrix incident with both of them. -/
def HasRealCommonNode (Z₁ Z₂ : Twistor4) : Prop :=
  ∃ X : ComplexSpacetime,
    IsHermitianSpacetime X ∧
      incidenceLinearMap X Z₁.2 = Z₁ ∧
      incidenceLinearMap X Z₂.2 = Z₂

/-- For independent rays, reality of the twistor pair is exactly Hermiticity
of the unique reconstructed spacetime node. -/
theorem hasRealCommonNode_iff_reconstructedNode_hermitian
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    HasRealCommonNode Z₁ Z₂ ↔
      IsHermitianSpacetime (reconstructedSpacetimeNode Z₁ Z₂ h) := by
  constructor
  · rintro ⟨X, hHerm, h₁, h₂⟩
    have hX : X = reconstructedSpacetimeNode Z₁ Z₂ h :=
      reconstructedSpacetimeNode_eq_of_incident Z₁ Z₂ h X h₁ h₂
    rw [← hX]
    exact hHerm
  · intro hHerm
    exact ⟨reconstructedSpacetimeNode Z₁ Z₂ h, hHerm,
      reconstructedNode_incident_first Z₁ Z₂ h,
      reconstructedNode_incident_second Z₁ Z₂ h⟩

/-- The first lower spinor of an independent twistor pair is nonzero. -/
theorem first_spinor_ne_zero_of_independent
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    Z₁.2 ≠ 0 := by
  intro hzero
  apply h
  simp [AreIndependentRays, twistorSpinorMatrixPi, hzero,
    Matrix.det_fin_two]

/-- The second lower spinor of an independent twistor pair is nonzero. -/
theorem second_spinor_ne_zero_of_independent
    (Z₁ Z₂ : Twistor4) (h : AreIndependentRays Z₁ Z₂) :
    Z₂.2 ≠ 0 := by
  intro hzero
  apply h
  simp [AreIndependentRays, twistorSpinorMatrixPi, hzero,
    Matrix.det_fin_two]

/-- If the same twistor is incident with two spacetime matrices, those matrices
act identically on its lower spinor. -/
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
    exact hx.trans hy.symm
  have hc :
      X a 0 * Z.2 0 + X a 1 * Z.2 1 =
        Y a 0 * Z.2 0 + Y a 1 * Z.2 1 := by
    exact mul_left_cancel₀ (by norm_num : (Complex.I : ℂ) ≠ 0) hxy
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hc

/-- Shared incidence puts the common lower spinor in the kernel of the
spacetime difference. -/
theorem shared_twistor_difference_mulVec_zero
    (Z : Twistor4) (X Y : ComplexSpacetime)
    (hX : incidenceLinearMap X Z.2 = Z)
    (hY : incidenceLinearMap Y Z.2 = Z) :
    Matrix.mulVec (X - Y) Z.2 = 0 := by
  rw [Matrix.sub_mulVec]
  rw [shared_twistor_mulVec_eq Z X Y hX hY]
  exact sub_self _

/-- A shared nonzero incident spinor forces the matrix difference to be
singular.  This is the matrix form of null separation. -/
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

/-- Consecutive reconstructed nodes `X₁₂` and `X₂₃` share `Z₂`; hence their
separation matrix is singular. -/
theorem adjacent_reconstructed_nodes_det_difference_zero
    (Z₁ Z₂ Z₃ : Twistor4)
    (h₁₂ : AreIndependentRays Z₁ Z₂)
    (h₂₃ : AreIndependentRays Z₂ Z₃) :
    Matrix.det
      (reconstructedSpacetimeNode Z₁ Z₂ h₁₂ -
        reconstructedSpacetimeNode Z₂ Z₃ h₂₃) = 0 := by
  apply det_sub_eq_zero_of_shared_nonzero_twistor Z₂
    (reconstructedSpacetimeNode Z₁ Z₂ h₁₂)
    (reconstructedSpacetimeNode Z₂ Z₃ h₂₃)
  · exact second_spinor_ne_zero_of_independent Z₁ Z₂ h₁₂
  · exact reconstructedNode_incident_second Z₁ Z₂ h₁₂
  · exact reconstructedNode_incident_first Z₂ Z₃ h₂₃

end InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency
