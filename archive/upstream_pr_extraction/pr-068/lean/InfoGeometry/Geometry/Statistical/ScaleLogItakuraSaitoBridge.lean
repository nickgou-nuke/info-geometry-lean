import InfoGeometry.Algebraic.CartanExponentialFamily
import InfoGeometry.TraceFormula.ItakuraSaitoMongeAmpere

/-!
# Logarithmic scale and finite Itakura--Saito invariance

This owner records the scalar downstream bridge only.  The central
endomorphism cancellation is owned by `WeylSplitOctonionDualFlatBridge`;
the finite exponential-family and Itakura--Saito quotient facts are reused
from their native owners here.
-/

namespace InfoGeometry.Geometry.Statistical.ScaleLogItakuraSaitoBridge

noncomputable section

open InfoGeometry.Algebraic.CartanExponentialFamily
open InfoGeometry.TraceFormula.ItakuraSaito

def positiveScale (κ : ℝ) : ℝ := Real.exp κ

theorem positiveScale_add (κ c : ℝ) :
    positiveScale (κ + c) = Real.exp c * positiveScale κ := by
  unfold positiveScale
  rw [Real.exp_add]
  ring

theorem log_positiveScale (κ : ℝ) :
    Real.log (positiveScale κ) = κ := by
  unfold positiveScale
  exact Real.log_exp κ

theorem scalarItakuraSaito_positiveScale_ratio (u v : ℝ) :
    scalarItakuraSaito (positiveScale u / positiveScale v) =
      Real.exp (u - v) - (u - v) - 1 := by
  exact scalarItakuraSaito_exp_ratio u v

theorem scalarItakuraSaito_positiveScale_common_shift
    (u v c : ℝ) :
    scalarItakuraSaito
        (positiveScale (u + c) / positiveScale (v + c)) =
      scalarItakuraSaito (positiveScale u / positiveScale v) := by
  exact scalarItakuraSaito_exp_common_shift u v c

theorem centeredPart_positiveScale_shift
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → ℝ) (c : ℝ) :
    centeredPart (fun i => θ i + c) = centeredPart θ := by
  exact centeredPart_add_const θ c

theorem prob_positiveScale_shift
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → ℝ) (c : ℝ) (i : ι) :
    prob (fun j => θ j + c) i = prob θ i := by
  exact prob_add_const θ c i

end
end InfoGeometry.Geometry.Statistical.ScaleLogItakuraSaitoBridge
