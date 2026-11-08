import InfoGeometry.Analysis.BipolarDeckIntegerHomotopyClass
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy and the native exponential lift

This file identifies the endpoint readout already supplied by the exponential
covering with Mathlib's native monodromy.  It does not classify loops in the
twice-punctured plane by winding numbers.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarMonodromyDeckReadout

open Complex Topology

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}

theorem exp_monodromy_mk_apply
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    Complex.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk γ)
        (⟨W, hW.symm⟩ :
          (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : NonzeroComplex)) ⁻¹' {x}) =
      ⟨Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW) 1,
        (congr_fun (Complex.isCoveringMap_exp.liftPath_lifts γ W
          (γ.source.trans hW)) 1).trans γ.target⟩ := by
  apply Subtype.ext
  rfl

theorem exp_monodromy_endpoint_period
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    ∃ n : ℤ,
      (Complex.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk γ)
          (⟨W, hW.symm⟩ :
            (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : NonzeroComplex)) ⁻¹' {x})).1 =
        W + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [exp_monodromy_mk_apply γ W hW]
  exact InfoGeometry.Analysis.BipolarLoopExpLift.exp_lift_loop_endpoint_period γ W hW

end InfoGeometry.Analysis.BipolarMonodromyDeckReadout
