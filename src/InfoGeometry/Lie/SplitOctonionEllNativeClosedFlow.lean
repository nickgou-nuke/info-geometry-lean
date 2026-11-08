import InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Native closed flow of the off-diagonal split-octonion ell grading

For `T = (1/2) ad_lUnit`, define the finite closed form

`Phi(t) = P0 + exp(t) P+ + exp(-t) P-`.

The proof is algebraic on the actual eight-dimensional weight basis.  No
analytic operator exponential and no global `G₂` automorphism claim enters.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- Scalar character of the closed flow at a tripotent weight. -/
def ellFlowScale (t w : ℝ) : ℝ :=
  (1 - w * w) + Real.exp t * ((w * w + w) / 2) +
    Real.exp (-t) * ((w * w - w) / 2)

/-- Closed hyperbolic flow of the normalized native ell grading. -/
def ellNativeFlow (t : ℝ) : EndCZ :=
  flowZero + (Real.exp t : ℝ) • flowPlus +
    (Real.exp (-t) : ℝ) • flowMinus

@[simp] theorem ellNativeFlow_apply (t : ℝ) (Z : CZ) :
    ellNativeFlow t Z =
      flowZero Z + (Real.exp t : ℝ) • flowPlus Z +
        (Real.exp (-t) : ℝ) • flowMinus Z := rfl

/-- The closed flow is diagonal on the actual canonical Zorn basis. -/
theorem ellNativeFlow_ellWeightBasisReal (t : ℝ) (i : Fin 8) :
    ellNativeFlow t (ellWeightBasisReal i) =
      ellFlowScale t (ellWeight i) • ellWeightBasisReal i := by
  rw [ellNativeFlow_apply, flowZero_ellWeightBasisReal,
    flowPlus_ellWeightBasisReal, flowMinus_ellWeightBasisReal]
  unfold ellFlowScale
  module

/-- Each negative native root channel has character `exp (-t)`. -/
@[simp] theorem ellNativeFlow_rootMinus (t : ℝ) (a : Fin 3) :
    ellNativeFlow t (rootMinus a) =
      (Real.exp (-t) : ℝ) • rootMinus a := by
  fin_cases a
  · simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
      ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 0
  · simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
      ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 1
  · simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
      ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 2

/-- The unital anchor is stationary under the native closed flow. -/
@[simp] theorem ellNativeFlow_one (t : ℝ) :
    ellNativeFlow t (1 : CZ) = 1 := by
  simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
    ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 3

/-- The distinguished split unit is stationary under its adjoint flow. -/
@[simp] theorem ellNativeFlow_lUnit (t : ℝ) :
    ellNativeFlow t InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit =
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit := by
  simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
    ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 4

/-- Each positive native root channel has character `exp t`. -/
@[simp] theorem ellNativeFlow_rootPlus (t : ℝ) (a : Fin 3) :
    ellNativeFlow t (rootPlus a) =
      (Real.exp t : ℝ) • rootPlus a := by
  fin_cases a
  · simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
      ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 5
  · simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
      ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 6
  · simpa [ellWeightBasisReal_apply, ellWeightBasis, ellWeight,
      ellFlowScale] using ellNativeFlow_ellWeightBasisReal t 7

/-- At zero flow parameter the closed flow is the identity. -/
@[simp] theorem ellNativeFlow_zero : ellNativeFlow 0 = 1 := by
  apply Module.Basis.ext ellWeightBasisReal
  intro i
  rw [ellNativeFlow_ellWeightBasisReal]
  fin_cases i <;> norm_num [ellFlowScale, ellWeight]

/-- The three possible weights give multiplicative scalar characters. -/
theorem ellFlowScale_add_on_weight (s t : ℝ) (i : Fin 8) :
    ellFlowScale (s + t) (ellWeight i) =
      ellFlowScale s (ellWeight i) * ellFlowScale t (ellWeight i) := by
  fin_cases i <;>
    simp [ellFlowScale, ellWeight, Real.exp_add] <;> ring

/-- The closed form is a one-parameter group. -/
theorem ellNativeFlow_add (s t : ℝ) :
    ellNativeFlow (s + t) = ellNativeFlow s * ellNativeFlow t := by
  apply Module.Basis.ext ellWeightBasisReal
  intro i
  rw [Module.End.mul_apply]
  rw [ellNativeFlow_ellWeightBasisReal,
    ellFlowScale_add_on_weight]
  rw [ellNativeFlow_ellWeightBasisReal, map_smul,
    ellNativeFlow_ellWeightBasisReal]
  module

/-- Reversing the parameter gives a right inverse. -/
theorem ellNativeFlow_mul_neg (t : ℝ) :
    ellNativeFlow t * ellNativeFlow (-t) = 1 := by
  rw [← ellNativeFlow_add]
  simp

/-- Reversing the parameter gives a left inverse. -/
theorem ellNativeFlow_neg_mul (t : ℝ) :
    ellNativeFlow (-t) * ellNativeFlow t = 1 := by
  rw [← ellNativeFlow_add]
  simp

end InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow
