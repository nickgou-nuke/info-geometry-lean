import InfoGeometry.Physics.IncidentNullFlagStress
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Explicit incident null-flag variational readouts

This file is argument-based.  It defines no action carrier and imports no
operator facade.  Boundary action and stress readout are functions of concrete
`Vec4` data and concrete linear maps.
-/

noncomputable section

namespace InfoGeometry.Physics.IncidentNullFlagVariationalAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Physics.IncidentNullFlagStress

/-- Explicit boundary action: the residual-square friction of the concrete maps at `Z`. -/
def boundaryAction
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4) : ℝ :=
  boundaryMajoranaFriction Z Pboundary Pzero J Dboundary

/-- The explicit boundary action is nonnegative. -/
theorem boundaryAction_nonneg
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4) :
    0 ≤ boundaryAction Z Pboundary Pzero J Dboundary :=
  boundaryMajoranaFriction_nonneg Z Pboundary Pzero J Dboundary

/-- Boundary support/fixed/zero-mode equations force zero explicit boundary action. -/
theorem boundaryAction_eq_zero_of_boundaryMajorana
    {Z : Vec4}
    {Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4}
    (h : IsBoundaryMajoranaFlag Z Pboundary Pzero J Dboundary) :
    boundaryAction Z Pboundary Pzero J Dboundary = 0 :=
  boundaryMajoranaFriction_eq_zero_of_boundaryMajorana h

/-- Explicit metric/stress readout for the concrete incident null-flag model. -/
def metricStressReadout
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4) :
    Vec4 → Vec4 → ℝ :=
  incidentStressTensor Z Pboundary Pzero J Dboundary

/-- The explicit metric/stress readout is symmetric. -/
theorem metricStressReadout_swap
    (Z : Vec4)
    (Pboundary Pzero J Dboundary : Vec4 →ₗ[ℝ] Vec4)
    (X Y : Vec4) :
    metricStressReadout Z Pboundary Pzero J Dboundary X Y =
      metricStressReadout Z Pboundary Pzero J Dboundary Y X :=
  incidentStressTensor_swap Z Pboundary Pzero J Dboundary X Y

end InfoGeometry.Physics.IncidentNullFlagVariationalAction
