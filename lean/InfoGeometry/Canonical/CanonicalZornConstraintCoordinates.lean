/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.CanonicalZornDerivativeFiniteReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dimension.Free

namespace InfoGeometry.Canonical

noncomputable section

abbrev ConstraintTarget := LinearMap.range tangentConstraintReadoutLinear

theorem tangentConstraintReadoutToRange_range_eq_top :
    LinearMap.range tangentConstraintReadoutToRange = (⊤ : Submodule ℝ ConstraintTarget) := by
  exact LinearMap.range_eq_top.mpr tangentConstraintReadoutToRange_surjective

theorem tangentConstraintReadoutContinuousToRange_toLinearMap_range_eq_top :
    LinearMap.range
        tangentConstraintReadoutContinuousToRange.toLinearMap =
      (⊤ : Submodule ℝ ConstraintTarget) := by
  exact LinearMap.range_eq_top.mpr
    tangentConstraintReadoutContinuousToRange_surjective

/-- The chosen finite basis of the intrinsic constraint range. -/
noncomputable def constraintBasis :
    Module.Basis (Fin 50) ℝ ConstraintTarget :=
  Module.finBasisOfFinrankEq ℝ ConstraintTarget
    finrank_tangentConstraintReadout_range

/-- Coordinates on the constraint range relative to `constraintBasis`. -/
noncomputable def constraintCoordinateEquiv :
    ConstraintTarget ≃ₗ[ℝ] (Fin 50 → ℝ) :=
  constraintBasis.equivFun

abbrev ConstraintAmbient := TangentConstraintValues

noncomputable def constraintRangeComplement :
    Submodule ℝ ConstraintAmbient :=
  Classical.choose (Submodule.exists_isCompl
    (LinearMap.range tangentConstraintReadoutLinear))

noncomputable def constraintRangeComplement_isCompl :
    IsCompl (LinearMap.range tangentConstraintReadoutLinear)
      constraintRangeComplement :=
  Classical.choose_spec (Submodule.exists_isCompl
    (LinearMap.range tangentConstraintReadoutLinear))

/-- A scalar-coordinate projection of the full readout onto its intrinsic
range.  The complement is noncanonical; the range and its coordinates are the
canonical data used by the differential owner. -/
noncomputable def constraintCoordinateProjection :
    ConstraintAmbient →ₗ[ℝ] (Fin 50 → ℝ) :=
  constraintCoordinateEquiv.comp
    ((LinearMap.range tangentConstraintReadoutLinear).linearProjOfIsCompl
      constraintRangeComplement constraintRangeComplement_isCompl)

theorem constraintCoordinateProjection_on_range (y : ConstraintTarget) :
    constraintCoordinateProjection y.1 = constraintCoordinateEquiv y := by
  unfold constraintCoordinateProjection
  change constraintCoordinateEquiv
      ((LinearMap.range tangentConstraintReadoutLinear).linearProjOfIsCompl
        constraintRangeComplement constraintRangeComplement_isCompl y.1) =
    constraintCoordinateEquiv y
  rw [Submodule.linearProjOfIsCompl_apply_left
    constraintRangeComplement_isCompl y]

@[simp] theorem constraintCoordinateEquiv_apply
    (y : ConstraintTarget) (i : Fin 50) :
    constraintCoordinateEquiv y i = constraintBasis.repr y i := by
  rfl

/-- The corresponding scalar dual coordinates. -/
noncomputable def constraintDualBasis :
    Module.Basis (Fin 50) ℝ (Module.Dual ℝ ConstraintTarget) :=
  constraintBasis.dualBasis

@[simp] theorem constraintDualBasis_apply
    (y : ConstraintTarget) (i : Fin 50) :
    constraintDualBasis i y = constraintCoordinateEquiv y i := by
  exact Module.Basis.dualBasis_apply constraintBasis i y

end

end InfoGeometry.Canonical
