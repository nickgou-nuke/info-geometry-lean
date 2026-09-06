import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Physics.Pin55Formal
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition
import InfoGeometry.Clifford.Cl55QuadraticSpinAction

/-!
# Ambient `Cl(5,5)` and selected five-grade readouts

This owner records the ambient finite split-Clifford data and the separate
five-grade closure interface.  It does not identify a particular chiral
four-vector carrier with `Cl55`, nor does it promote a supplied grading to a
Pin/Spin representation theorem.
-/

namespace InfoGeometry.Physics.Cl55BranchingSynthesis

open SplitClifford
open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.Physics.Algebra
open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

/-! The finite ambient carrier and its spinor-size readouts. -/
theorem cl55_ambient_dimension_packet :
    splitSpinorDim 5 = 32 ∧
      chiralSheetDim = 16 ∧
      doubledChiralDim = 32 := by
  norm_num [splitSpinorDim, chiralSheetDim, doubledChiralDim]

/-! Exact split-signature generator relations in the native rational Clifford
model used by the Pin55 owner. -/
theorem pin55_generator_packet :
    r₀ * r₀ = 1 ∧
      r₅ * r₅ = -1 ∧
      r₀ * r₅ = -(r₅ * r₀) ∧
      (r₀ * r₅) * (r₀ * r₅) = 1 := by
  exact ⟨r₀_sq, r₅_sq, anticomm, v4_relation⟩

/-! The actual five-grade closure laws, kept independent of ordinary
Clifford parity and multivector grade. -/
theorem five_grade_closure_packet
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    (G : FiveGrading L)
    (Xneg Yneg Xpos Ypos Xmix Ymix : L)
    (hNegOne : Xneg ∈ G.gNegOne ∧ Yneg ∈ G.gNegOne)
    (hPosOne : Xpos ∈ G.gPosOne ∧ Ypos ∈ G.gPosOne)
    (hMixed : Xmix ∈ G.gNegOne ∧ Ymix ∈ G.gPosOne) :
    ⁅Xneg, Yneg⁆ ∈ G.gNegTwo ∧
      ⁅Xpos, Ypos⁆ ∈ G.gPosTwo ∧
      ⁅Xmix, Ymix⁆ ∈ G.gZero := by
  exact ⟨G.bracket_neg_one_neg_one Xneg Yneg hNegOne.1 hNegOne.2,
    G.bracket_pos_one_pos_one Xpos Ypos hPosOne.1 hPosOne.2,
    G.bracket_neg_one_pos_one Xmix Ymix hMixed.1 hMixed.2⟩

end InfoGeometry.Physics.Cl55BranchingSynthesis
