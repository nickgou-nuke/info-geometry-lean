import InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
import InfoGeometry.Clifford.SplitClifford55ExteriorParity
import InfoGeometry.Clifford.Cl55ExteriorSpinorCoordinateReadout
import Mathlib.LinearAlgebra.Trace

/-!
# Finite supertrace and Gibbs operator on the Cl(5,5) right vacuum ideal

The right ideal is the actual principal right ideal of the owned vacuum
idempotent. Its grading is transported from exterior-spinor degree parity,
not inferred from an operator-number proxy. A finite-coordinate diagonal
Boltzmann operator is transported back to this ideal, and its supertrace is
the corresponding right-ideal superpartition functional.

This is a finite algebraic construction. It does not assert an analytic
operator exponential, positivity of a supertrace, or a continuum partition
function.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55RightIdealSupertrace

open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ExteriorParity
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

local instance : FiniteDimensional ℝ
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.Spinor :=
  spinor_finiteDimensional

local instance : FiniteDimensional ℝ MinimalRightIdeal :=
  FiniteDimensional.of_injective
    (rightIdealToLeftIdeal.trans cl55VacuumIdealSpinorEquiv).toLinearMap
    (rightIdealToLeftIdeal.trans cl55VacuumIdealSpinorEquiv).injective

/-- The actual spinor equivalence for the right vacuum ideal. -/
noncomputable def rightIdealSpinorEquiv :
    MinimalRightIdeal ≃ₗ[ℝ]
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.Spinor :=
  rightIdealToLeftIdeal.trans cl55VacuumIdealSpinorEquiv

/-- The concrete right vacuum ideal, identified with its exterior spinor
coordinates by transpose followed by the owner equivalence. -/
noncomputable def rightIdealCoordinateEquiv :
    MinimalRightIdeal ≃ₗ[ℝ] (Fin 32 → ℝ) :=
  rightIdealSpinorEquiv.trans spinorCoordinateEquiv

/-- Exterior-degree parity transported to the right vacuum ideal. -/
noncomputable def rightIdealParity : Module.End ℝ MinimalRightIdeal :=
  rightIdealSpinorEquiv.symm.toLinearMap.comp
    (gradeLinear.comp rightIdealSpinorEquiv.toLinearMap)

/-- The right-ideal grading operator is an involution. -/
theorem rightIdealParity_sq :
    rightIdealParity * rightIdealParity = (1 : Module.End ℝ MinimalRightIdeal) := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, Module.End.one_apply]
  have hx : rightIdealParity (rightIdealParity x) = x := by
    apply rightIdealSpinorEquiv.injective
    simp [rightIdealParity, LinearMap.comp_apply]
    exact gradeInvolution_involutive (rightIdealSpinorEquiv x)
  exact hx

/-- Graded trace on the actual principal right ideal `e Cl(5,5)`: trace of
parity composed with the operator. -/
noncomputable def rightIdealSupertrace
    (T : Module.End ℝ MinimalRightIdeal) : ℝ :=
  LinearMap.trace ℝ MinimalRightIdeal (rightIdealParity * T)

/-- The superpartition functional of a finite thermal operator on the right
vacuum ideal. -/
noncomputable def rightIdealSuperPartitionFunction
    (thermalOperator : Module.End ℝ MinimalRightIdeal) : ℝ :=
  rightIdealSupertrace thermalOperator

noncomputable def coordinateGibbsOperator
    (energy : Fin 32 → ℝ) (β : ℝ) : Module.End ℝ (Fin 32 → ℝ) where
  toFun f i := Real.exp (-energy i / β) * f i
  map_add' f g := by
    funext i
    simp [mul_add]
  map_smul' c f := by
    funext i
    simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- A diagonal finite Gibbs operator on the 32 exterior-spinor coordinates,
transported to the right vacuum ideal. -/
noncomputable def rightIdealGibbsOperator
    (energy : Fin 32 → ℝ) (β : ℝ) : Module.End ℝ MinimalRightIdeal :=
  rightIdealCoordinateEquiv.symm.toLinearMap.comp
    ((coordinateGibbsOperator energy β).comp
      rightIdealCoordinateEquiv.toLinearMap)

/-- The finite Gibbs superpartition is the right-ideal supertrace of the
transported diagonal Boltzmann operator. -/
noncomputable def rightIdealGibbsSuperPartitionFunction
    (energy : Fin 32 → ℝ) (β : ℝ) : ℝ :=
  rightIdealSuperPartitionFunction (rightIdealGibbsOperator energy β)

end InfoGeometry.Clifford.Cl55RightIdealSupertrace

end noncomputable section
