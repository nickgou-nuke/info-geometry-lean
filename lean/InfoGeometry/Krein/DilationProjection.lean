import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Isometric dilation and the induced Krein involution

This file records the carrier-independent part of the covariance/purification
construction.  A bounded isometry `V : H →L[ℝ] K` produces the projection
`V V†` on the doubled carrier `K`, and hence the fundamental symmetry
`2 V V† - I`.  No diagonalization, commutative scalar model, or Tomita
commutant identification is used here.

The separate covariance owner must provide the square-root lift and prove its
isometry equation.  The results below then supply the projection and Krein
layers without hiding that input behind `Nonempty`.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Krein.DilationProjection

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- An explicit bounded isometric dilation from `H` into `K`. -/
structure IsometricDilation where
  lift : H →L[ℝ] K
  lift_adjoint_comp :
    (ContinuousLinearMap.adjoint lift).comp lift =
      ContinuousLinearMap.id ℝ H

namespace IsometricDilation

variable (D : IsometricDilation (H := H) (K := K))

/-- The range projection of an isometric dilation. -/
noncomputable def rangeProjection : K →L[ℝ] K :=
  D.lift.comp (ContinuousLinearMap.adjoint D.lift)

@[simp] theorem rangeProjection_apply (x : K) :
    D.rangeProjection x = D.lift (ContinuousLinearMap.adjoint D.lift x) := rfl

/-- The dilation range projection is self-adjoint. -/
theorem rangeProjection_selfAdjoint :
    ContinuousLinearMap.adjoint D.rangeProjection = D.rangeProjection := by
  simp [rangeProjection, ContinuousLinearMap.adjoint_comp]

/-- The dilation range projection is idempotent. -/
theorem rangeProjection_idem :
    D.rangeProjection.comp D.rangeProjection = D.rangeProjection := by
  calc
    D.rangeProjection.comp D.rangeProjection =
        D.lift.comp
          (((ContinuousLinearMap.adjoint D.lift).comp D.lift).comp
            (ContinuousLinearMap.adjoint D.lift)) := by
              simp [rangeProjection, ContinuousLinearMap.comp_assoc]
    _ = D.lift.comp
          ((ContinuousLinearMap.id ℝ H).comp
            (ContinuousLinearMap.adjoint D.lift)) := by
              rw [D.lift_adjoint_comp]
    _ = D.rangeProjection := by simp [rangeProjection]

/-- The range projection fixes the image of the isometric lift. -/
theorem rangeProjection_comp_lift :
    D.rangeProjection.comp D.lift = D.lift := by
  calc
    D.rangeProjection.comp D.lift =
        D.lift.comp ((ContinuousLinearMap.adjoint D.lift).comp D.lift) := by
          simp [rangeProjection, ContinuousLinearMap.comp_assoc]
    _ = D.lift.comp (ContinuousLinearMap.id ℝ H) := by
          rw [D.lift_adjoint_comp]
    _ = D.lift := by simp

/-- An isometric lift is injective. -/
theorem lift_injective : Function.Injective D.lift := by
  intro x y hxy
  have hadj := congrArg (ContinuousLinearMap.adjoint D.lift) hxy
  change (ContinuousLinearMap.adjoint D.lift) (D.lift x) =
    (ContinuousLinearMap.adjoint D.lift) (D.lift y) at hadj
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    D.lift_adjoint_comp] at hadj
  simpa using hadj

/-- The range projection vanishes precisely on the kernel of the adjoint lift. -/
theorem rangeProjection_apply_eq_zero_iff (x : K) :
    D.rangeProjection x = 0 ↔
      ContinuousLinearMap.adjoint D.lift x = 0 := by
  constructor
  · intro hx
    have hlift :
        D.lift (ContinuousLinearMap.adjoint D.lift x) = D.lift 0 := by
      simpa [rangeProjection_apply] using hx
    exact D.lift_injective hlift
  · intro hx
    simp [rangeProjection_apply, hx]

/-- The data-induced fundamental symmetry on the dilation carrier. -/
noncomputable def fundamentalSymmetry : K →L[ℝ] K :=
  (2 : ℝ) • D.rangeProjection - ContinuousLinearMap.id ℝ K

/-- The induced fundamental symmetry is self-adjoint. -/
theorem fundamentalSymmetry_selfAdjoint :
    ContinuousLinearMap.adjoint D.fundamentalSymmetry =
      D.fundamentalSymmetry := by
  change ContinuousLinearMap.adjoint
      (2 • D.rangeProjection - ContinuousLinearMap.id ℝ K) = _
  rw [map_sub, map_smul, ContinuousLinearMap.adjoint_id,
    D.rangeProjection_selfAdjoint]
  rfl

/-- The induced fundamental symmetry squares to the identity. -/
theorem fundamentalSymmetry_sq :
    D.fundamentalSymmetry.comp D.fundamentalSymmetry =
      ContinuousLinearMap.id ℝ K := by
  simp only [fundamentalSymmetry, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, D.rangeProjection_idem,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  module

/-- The induced fundamental symmetry is the identity on the lifted range. -/
theorem fundamentalSymmetry_comp_lift :
    D.fundamentalSymmetry.comp D.lift = D.lift := by
  unfold fundamentalSymmetry
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp,
    D.rangeProjection_comp_lift, ContinuousLinearMap.id_comp]
  module

/-- The fundamental symmetry is negative on the orthogonal complement of the
    lifted range. -/
theorem fundamentalSymmetry_apply_of_adjoint_lift_eq_zero
    (x : K) (hx : ContinuousLinearMap.adjoint D.lift x = 0) :
    D.fundamentalSymmetry x = -x := by
  change (2 : ℝ) • D.rangeProjection x - x = -x
  rw [rangeProjection_apply, hx, map_zero]
  module

end IsometricDilation

/-- A compatible complex rotation for the data-induced fundamental symmetry. -/
structure SplitCompatible (D : IsometricDilation (H := H) (K := K)) where
  J0 : K →L[ℝ] K
  J0_sq : J0.comp J0 = -ContinuousLinearMap.id ℝ K
  anticommutes :
    J0.comp D.fundamentalSymmetry =
      -(D.fundamentalSymmetry.comp J0)

namespace SplitCompatible

variable {D : IsometricDilation (H := H) (K := K)}
variable (S : SplitCompatible D)

/-- The product of the complex and split involutions. -/
noncomputable def splitComplexOperator : K →L[ℝ] K :=
  S.J0.comp D.fundamentalSymmetry

/-- The split-complex product squares to `+I`. -/
theorem splitComplexOperator_sq :
    S.splitComplexOperator.comp S.splitComplexOperator =
      ContinuousLinearMap.id ℝ K := by
  calc
    S.splitComplexOperator.comp S.splitComplexOperator =
        S.J0.comp ((D.fundamentalSymmetry.comp S.J0).comp
          D.fundamentalSymmetry) := by
            simp [splitComplexOperator, ContinuousLinearMap.comp_assoc]
    _ = S.J0.comp ((-(S.J0.comp D.fundamentalSymmetry)).comp
          D.fundamentalSymmetry) := by
            rw [S.anticommutes]
            simp
    _ = -((S.J0.comp S.J0).comp
          (D.fundamentalSymmetry.comp D.fundamentalSymmetry)) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = ContinuousLinearMap.id ℝ K := by
          rw [S.J0_sq, D.fundamentalSymmetry_sq]
          simp

end SplitCompatible

end InfoGeometry.Krein.DilationProjection
