import InfoGeometry.Analysis.BipolarLoopWindingCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Homotopy invariance of the native logarithmic lift readout

The exponential covering gives an integer endpoint displacement for an
admissible loop.  This owner proves the nearest global invariance statement:
the displacement is unchanged when the two underlying paths are homotopic
relative to their endpoints.  No winding-number classification is introduced.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopLiftHomotopyInvariant

open Complex Topology
open InfoGeometry.Analysis.BipolarLoopExpLift
open InfoGeometry.Analysis.BipolarLoopWindingCarrier

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}
abbrev Period := 2 * (Real.pi : ℂ) * Complex.I

theorem expLift_endpoint_eq_of_homotopicRel
    {x : NonzeroComplex} {γ₀ γ₁ : Path x x}
    (h : (γ₀ : C(↑unitInterval, NonzeroComplex)).HomotopicRel
      (γ₁ : C(↑unitInterval, NonzeroComplex)) {0, 1})
    (W : ℂ)
    (h₀ : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    (h₁ : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    Complex.isCoveringMap_exp.liftPath γ₀ W
        (γ₀.source.trans h₀) 1 =
      Complex.isCoveringMap_exp.liftPath γ₁ W
        (γ₁.source.trans h₁) 1 := by
  exact Complex.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel
    h W (γ₀.source.trans h₀) (γ₁.source.trans h₁)

theorem liftEndpointInteger_eq_of_homotopicRel
    {x : NonzeroComplex} {γ₀ γ₁ : Path x x}
    (h : (γ₀ : C(↑unitInterval, NonzeroComplex)).HomotopicRel
      (γ₁ : C(↑unitInterval, NonzeroComplex)) {0, 1})
    (W : ℂ)
    (h₀ : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    (h₁ : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    liftEndpointInteger γ₀ W h₀ =
      liftEndpointInteger γ₁ W h₁ := by
  apply liftEndpointInteger_unique γ₀ W h₀
  · exact liftEndpointInteger_spec γ₀ W h₀
  · calc
      Complex.isCoveringMap_exp.liftPath γ₀ W
          (γ₀.source.trans h₀) 1 =
          Complex.isCoveringMap_exp.liftPath γ₁ W
            (γ₁.source.trans h₁) 1 := by
        exact expLift_endpoint_eq_of_homotopicRel h W h₀ h₁
      _ = W + (liftEndpointInteger γ₁ W h₁ : ℂ) * Period := by
        exact liftEndpointInteger_spec γ₁ W h₁

/-! The integer readout is the deck coordinate itself; the following form is
the period-valued statement used by contour and holonomy owners. -/

theorem liftEndpointPeriod_eq_of_homotopicRel
    {x : NonzeroComplex} {γ₀ γ₁ : Path x x}
    (h : (γ₀ : C(↑unitInterval, NonzeroComplex)).HomotopicRel
      (γ₁ : C(↑unitInterval, NonzeroComplex)) {0, 1})
    (W : ℂ)
    (h₀ : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    (h₁ : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    (liftEndpointInteger γ₀ W h₀ : ℂ) * Period =
      (liftEndpointInteger γ₁ W h₁ : ℂ) * Period := by
  rw [liftEndpointInteger_eq_of_homotopicRel h W h₀ h₁]


end InfoGeometry.Analysis.BipolarLoopLiftHomotopyInvariant
