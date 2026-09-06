import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Heat-equation residuals on the Hestenes--Krein colimit

This owner translates the equation-shaped heat-flow interface into native real
readouts.  The two component readouts (parameter derivative and spatial
second derivative) are supplied finite-stage data.  Theorems below transport
their residual identity through canonical colimit images; no differentiability,
PDE existence, or de Bruijn--Newman theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinHeatEquationColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Krein

def heatResidual (parameterDerivative spatialSecondDerivative : ℝ) : ℝ :=
  parameterDerivative + spatialSecondDerivative

def stageHeatResidual
    {C : HestenesKreinCone}
    (parameterDerivative spatialSecondDerivative :
      ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  heatResidual (parameterDerivative n x) (spatialSecondDerivative n x)

def limitHeatResidual
    {C : HestenesKreinCone}
    (parameterDerivative spatialSecondDerivative :
      DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  heatResidual (parameterDerivative x) (spatialSecondDerivative x)

theorem stageHeatResidual_eq_limitHeatResidual
    {C : HestenesKreinCone}
    (parameterDerivative spatialSecondDerivative :
      ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitParameterDerivative limitSpatialSecondDerivative :
      DoubledSpace C.LimitBase → ℝ)
    (hparameter : ∀ n x,
      parameterDerivative n x = limitParameterDerivative (C.ι n x))
    (hspatial : ∀ n x,
      spatialSecondDerivative n x = limitSpatialSecondDerivative (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageHeatResidual parameterDerivative spatialSecondDerivative n x =
      limitHeatResidual limitParameterDerivative limitSpatialSecondDerivative
        (C.ι n x) := by
  unfold stageHeatResidual limitHeatResidual heatResidual
  rw [hparameter n x, hspatial n x]

theorem stageHeatResidual_bondIterate_eq
    {C : HestenesKreinCone}
    (parameterDerivative spatialSecondDerivative :
      ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hparameter : ∀ n m x,
      parameterDerivative (n + m)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        parameterDerivative n x)
    (hspatial : ∀ n m x,
      spatialSecondDerivative (n + m)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        spatialSecondDerivative n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageHeatResidual parameterDerivative spatialSecondDerivative (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      stageHeatResidual parameterDerivative spatialSecondDerivative n x := by
  unfold stageHeatResidual heatResidual
  rw [hparameter n m x, hspatial n m x]

theorem limitHeatResidual_eq_zero_of_stage
    {C : HestenesKreinCone}
    (parameterDerivative spatialSecondDerivative :
      ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitParameterDerivative limitSpatialSecondDerivative :
      DoubledSpace C.LimitBase → ℝ)
    (hparameter : ∀ n x,
      parameterDerivative n x = limitParameterDerivative (C.ι n x))
    (hspatial : ∀ n x,
      spatialSecondDerivative n x = limitSpatialSecondDerivative (C.ι n x))
    (hlaw : ∀ n x, stageHeatResidual parameterDerivative spatialSecondDerivative n x = 0)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    limitHeatResidual limitParameterDerivative limitSpatialSecondDerivative
        (C.ι n x) = 0 := by
  rw [← stageHeatResidual_eq_limitHeatResidual parameterDerivative
    spatialSecondDerivative limitParameterDerivative limitSpatialSecondDerivative
    hparameter hspatial n x]
  exact hlaw n x

end InfoGeometry.Canonical.HestenesKreinHeatEquationColimit

end noncomputable section
