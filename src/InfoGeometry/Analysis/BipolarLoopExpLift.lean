import InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Homotopy.Lifting

/-!
# Endpoint periods of lifted nonzero loops

This file closes the nearest native covering-space edge for the bipolar
period problem.  It does not define a winding number and does not identify
arbitrary loops with the repository's algebraic `WindingPair`.  It records the
exact consequence of Mathlib's exponential covering: a lift of a loop in
`ℂˣ` ends in the same exponential fibre, hence differs from its initial
logarithm by an integral `2πi` deck translation.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopExpLift

open Complex Topology

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}

/-! The lift is the native `IsCoveringMap.liftPath`, not a chosen logarithm
branch or an integral-defined period. -/

theorem exp_lift_loop_endpoint_period
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    ∃ n : ℤ,
      (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 =
        W + n * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h0 : γ 0 =
      (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex) :=
    γ.source.trans hW
  have hlift := Complex.isCoveringMap_exp.liftPath_lifts γ W h0
  have hend := congrFun hlift 1
  have hloop : γ 1 = x := γ.target
  have hexp : Complex.exp ((Complex.isCoveringMap_exp.liftPath γ W h0) 1) =
      Complex.exp W := by
    have hsub :
        (⟨Complex.exp ((Complex.isCoveringMap_exp.liftPath γ W h0) 1),
          Complex.exp_ne_zero _⟩ : NonzeroComplex) = x := by
      simpa [hloop] using hend
    have hval := congrArg (fun z : NonzeroComplex => (z : ℂ)) hsub
    have hxe : (x : ℂ) = Complex.exp W := congrArg Subtype.val hW
    exact hval.trans hxe
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).mp hexp
  exact ⟨n, hn⟩

theorem exp_lift_loop_endpoint_mem_periodSubgroup
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 - W ∈
      AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨n, hn⟩ := exp_lift_loop_endpoint_period γ W hW
  rw [hn, add_sub_cancel_left]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by rw [zsmul_eq_mul]⟩

end InfoGeometry.Analysis.BipolarLoopExpLift
