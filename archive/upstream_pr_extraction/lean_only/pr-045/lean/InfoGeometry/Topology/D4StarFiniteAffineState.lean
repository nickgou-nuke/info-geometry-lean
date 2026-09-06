import InfoGeometry.Topology.D4StarObservableSpectrum

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! A finite affine state on the two-class observable spectrum. -/

abbrev BooleanAffineState :=
  {w : ℚ × ℚ //
    0 ≤ w.1 ∧
    0 ≤ w.2 ∧
    w.1 + w.2 = 1}

namespace BooleanAffineState

abbrev centreWeight (s : BooleanAffineState) : ℚ := s.1.1
abbrev outerWeight (s : BooleanAffineState) : ℚ := s.1.2
abbrev centre_nonneg (s : BooleanAffineState) : 0 ≤ s.centreWeight := s.2.1
abbrev outer_nonneg (s : BooleanAffineState) : 0 ≤ s.outerWeight := s.2.2.1
abbrev normalized (s : BooleanAffineState) : s.centreWeight + s.outerWeight = 1 := s.2.2.2

end BooleanAffineState

def uniformBooleanAffineState : BooleanAffineState :=
  ⟨(1 / 2, 1 / 2), by norm_num⟩

def affineExpectation
    (s : BooleanAffineState)
    (f : C(D4StarQuotient, ℚ)) : ℚ :=
  s.centreWeight * f (starQuotientMap centralVertex) +
    s.outerWeight * f (starQuotientMap (outerVertex ColorChannel.red))

def pullbackByInducedFlow
    (F : ColorPermutationFlow) (t : ℤ)
    (f : C(D4StarQuotient, ℚ)) : C(D4StarQuotient, ℚ) :=
  { toFun := fun q => f ((inducedQuotientFlow F).flow t q)
    continuous_toFun := f.continuous.comp
      ((inducedQuotientFlow F).continuous t) }

theorem pullbackByInducedFlow_eq
    (F : ColorPermutationFlow) (t : ℤ)
    (f : C(D4StarQuotient, ℚ)) :
    pullbackByInducedFlow F t f = f := by
  ext q
  change f ((inducedQuotientFlow F).flow t q) = f q
  rw [inducedQuotientFlow_is_trivial]

theorem affineExpectation_flow_invariant
    (s : BooleanAffineState) (F : ColorPermutationFlow) (t : ℤ)
    (f : C(D4StarQuotient, ℚ)) :
    affineExpectation s (pullbackByInducedFlow F t f) =
      affineExpectation s f := by
  rw [pullbackByInducedFlow_eq]

theorem affineExpectation_uniform_constant
    (c : ℚ) :
    affineExpectation uniformBooleanAffineState
      (ContinuousMap.const D4StarQuotient c) = c := by
  simp [affineExpectation, uniformBooleanAffineState]
  ring

end InfoGeometry.Topology.PauliJungD4Star
