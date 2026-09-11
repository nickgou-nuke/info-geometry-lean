import InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Left multiplication on the canonical split-octonion carrier

This owner records the first-quantized linear lift without treating the
nonassociative product as an associative operator representation.  The
composition defect is retained explicitly as the ordinary associator.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic

abbrev Carrier := InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.CanonicalZorn
abbrev State := InfoGeometry.Algebra.FiniteSpin.Vec8R

@[simp] theorem leftMulLinearGeneral_apply (Z : Carrier) (v : State) :
    leftMulLinearGeneral Z v = coordLE (Z * coordLE.symm v) := by
  rfl

/-- The associator defect of two left-multiplication operators. -/
def leftMulCompDefect (Z W : Carrier) : Module.End ℝ State :=
  (leftMulLinearGeneral Z).comp (leftMulLinearGeneral W) -
    leftMulLinearGeneral (Z * W)

theorem leftMulCompDefect_apply (Z W : Carrier) (v : State) :
    leftMulCompDefect Z W v =
      coordLE (Z * (W * coordLE.symm v)) -
        coordLE ((Z * W) * coordLE.symm v) := by
  simp only [leftMulCompDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    leftMulLinearGeneral_apply, coordLE.symm_apply_apply]

theorem leftMulCompDefect_eq_zero_iff (Z W : Carrier) :
    leftMulCompDefect Z W = 0 ↔
      ∀ X : Carrier, Z * (W * X) = (Z * W) * X := by
  constructor
  · intro h X
    have hv := congrArg (fun f : Module.End ℝ State => f (coordLE X)) h
    change leftMulCompDefect Z W (coordLE X) = 0 at hv
    rw [leftMulCompDefect_apply] at hv
    exact coordLE.injective (sub_eq_zero.mp hv)
  · intro h
    apply LinearMap.ext
    intro v
    rw [leftMulCompDefect_apply]
    rw [h]
    simp

end InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge
