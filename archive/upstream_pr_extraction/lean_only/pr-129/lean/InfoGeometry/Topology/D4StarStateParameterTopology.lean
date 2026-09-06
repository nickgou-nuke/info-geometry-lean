import InfoGeometry.Topology.D4StarAffineStateParameter

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

def parameterExpectation
    (p : BooleanStateParameter)
    (f : C(D4StarQuotient, ℚ)) : ℚ :=
  p.1 * f (starQuotientMap centralVertex) +
    (1 - p.1) * f (starQuotientMap (outerVertex ColorChannel.red))

theorem parameterExpectation_eq_affineExpectation
    (s : BooleanAffineState) (f : C(D4StarQuotient, ℚ)) :
    parameterExpectation (stateToParameter s) f = affineExpectation s f := by
  change s.centreWeight * f (starQuotientMap centralVertex) +
      (1 - s.centreWeight) * f (starQuotientMap (outerVertex ColorChannel.red)) =
    s.centreWeight * f (starQuotientMap centralVertex) +
      s.outerWeight * f (starQuotientMap (outerVertex ColorChannel.red))
  have hweight : 1 - s.centreWeight = s.outerWeight := by
    linarith [s.normalized]
  rw [hweight]

theorem continuous_parameterExpectation
    (f : C(D4StarQuotient, ℚ)) :
    Continuous (fun p : BooleanStateParameter => parameterExpectation p f) := by
  let hp : Continuous (fun p : BooleanStateParameter => (p : ℚ)) :=
    continuous_subtype_val
  have hcentre : Continuous (fun p : BooleanStateParameter =>
      p.1 * f (starQuotientMap centralVertex)) :=
    hp.mul continuous_const
  have houter : Continuous (fun p : BooleanStateParameter =>
      (1 - p.1) * f (starQuotientMap (outerVertex ColorChannel.red))) :=
    (continuous_const.sub hp).mul continuous_const
  exact hcentre.add houter

theorem parameterExpectation_at_uniform
    (f : C(D4StarQuotient, ℚ)) :
    parameterExpectation ⟨1 / 2, by norm_num, by norm_num⟩ f =
      affineExpectation uniformBooleanAffineState f := by
  change (1 / 2 : ℚ) * f (starQuotientMap centralVertex) +
      (1 - (1 / 2 : ℚ)) * f (starQuotientMap (outerVertex ColorChannel.red)) =
    (1 / 2 : ℚ) * f (starQuotientMap centralVertex) +
      (1 / 2 : ℚ) * f (starQuotientMap (outerVertex ColorChannel.red))
  norm_num

end InfoGeometry.Topology.PauliJungD4Star
