import InfoGeometry.Analysis.BipolarLoopLiftHomotopyInvariant
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Deck integers on homotopy classes

The exponential covering supplies an integer endpoint displacement for every
loop in a nonzero complex space.  This owner descends that readout to
`Path.Homotopic.Quotient`.  It is a genuine homotopy-class carrier; it does
not identify the readout with a winding-number classification of the
twice-punctured plane.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarDeckIntegerHomotopyClass

open Complex Topology
open InfoGeometry.Analysis.BipolarLoopExpLift
open InfoGeometry.Analysis.BipolarLoopWindingCarrier
open InfoGeometry.Analysis.BipolarLoopLiftHomotopyInvariant

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}
abbrev Period := 2 * (Real.pi : ℂ) * Complex.I

/-- The exponential-covering deck integer on a homotopy class of based loops. -/
noncomputable def deckIntegerClass
    {x : NonzeroComplex} (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    Path.Homotopic.Quotient x x → ℤ :=
  Quotient.lift
    (fun γ : Path x x => liftEndpointInteger γ W hW)
    (by
      intro γ₀ γ₁ h
      exact liftEndpointInteger_eq_of_homotopicRel h W hW hW)

/-- The native exponential lift of a reflexive path has zero deck displacement. -/
theorem liftEndpointInteger_refl
    {x : NonzeroComplex} (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    liftEndpointInteger (Path.refl x) W hW = 0 := by
  apply liftEndpointInteger_eq_of_endpoint (Path.refl x) W hW
  have hconst := Complex.isCoveringMap_exp.liftPath_const (e := W) hW
  have hend := congrArg (fun p : C(↑unitInterval, ℂ) => p 1) hconst
  simpa [Path.refl] using hend

@[simp] theorem deckIntegerClass_mk
    {x : NonzeroComplex} (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    (γ : Path x x) :
    deckIntegerClass W hW (Path.Homotopic.Quotient.mk γ) =
      liftEndpointInteger γ W hW := by
  rfl

/-- The reflexive homotopy class has zero exponential deck displacement. -/
@[simp] theorem deckIntegerClass_refl
    {x : NonzeroComplex} (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    deckIntegerClass W hW (Path.Homotopic.Quotient.mk (Path.refl x)) = 0 := by
  rw [deckIntegerClass_mk]
  exact liftEndpointInteger_refl W hW

/-- A loop homotopic rel endpoints to the reflexive path has zero deck class. -/
theorem deckIntegerClass_eq_zero_of_homotopic_refl
    {x : NonzeroComplex} (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    {γ : Path x x}
    (h : (γ : C(↑unitInterval, NonzeroComplex)).HomotopicRel
      (Path.refl x : C(↑unitInterval, NonzeroComplex)) {0, 1}) :
    deckIntegerClass W hW (Path.Homotopic.Quotient.mk γ) = 0 := by
  rw [deckIntegerClass_mk]
  rw [liftEndpointInteger_eq_of_homotopicRel h W hW hW]
  exact liftEndpointInteger_refl W hW

/-- The associated period depends only on the homotopy class. -/
theorem deckPeriodClass_mk
    {x : NonzeroComplex} (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    (γ : Path x x) :
    (deckIntegerClass W hW (Path.Homotopic.Quotient.mk γ) : ℂ) * Period =
      (Complex.isCoveringMap_exp.liftPath γ W
        (γ.source.trans hW) 1 - W) := by
  rw [deckIntegerClass_mk]
  exact liftEndpointPeriod_eq_sub γ W hW

end InfoGeometry.Analysis.BipolarDeckIntegerHomotopyClass
