import InfoGeometry.Topology.D4StarStateParameterTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

def PointwiseNonnegative (f : C(D4StarQuotient, ℚ)) : Prop :=
  ∀ q, 0 ≤ f q

abbrev FiniteStateFunctional := C(D4StarQuotient, ℚ) →+ ℚ

def FiniteStateFunctional.IsNormalized (ω : FiniteStateFunctional) : Prop :=
  ω (ContinuousMap.const D4StarQuotient 1) = 1

def FiniteStateFunctional.IsPositive (ω : FiniteStateFunctional) : Prop :=
  ∀ f, PointwiseNonnegative f → 0 ≤ ω f

def affineStateFunctional (s : BooleanAffineState) :
    FiniteStateFunctional := {
  toFun := affineExpectation s
  map_zero' := by
    simp [affineExpectation]
  map_add' := by
    intro f g
    simp [affineExpectation]
    ring }

theorem affineStateFunctional_isNormalized (s : BooleanAffineState) :
    FiniteStateFunctional.IsNormalized (affineStateFunctional s) := by
  simp [FiniteStateFunctional.IsNormalized, affineStateFunctional,
    affineExpectation, s.normalized]

theorem affineStateFunctional_isPositive (s : BooleanAffineState) :
    FiniteStateFunctional.IsPositive (affineStateFunctional s) := by
  intro f hf
  have hcentre : 0 ≤ f (starQuotientMap centralVertex) := hf _
  have houter : 0 ≤ f (starQuotientMap (outerVertex ColorChannel.red)) := hf _
  exact add_nonneg
    (mul_nonneg s.centre_nonneg hcentre)
    (mul_nonneg s.outer_nonneg houter)

theorem affineStateFunctional_apply
    (s : BooleanAffineState) (f : C(D4StarQuotient, ℚ)) :
    affineStateFunctional s f = affineExpectation s f := rfl

theorem affineStateFunctional_flow_invariant
    (s : BooleanAffineState) (F : ColorPermutationFlow) (t : ℤ)
    (f : C(D4StarQuotient, ℚ)) :
    affineStateFunctional s
      (pullbackByInducedFlow F t f) =
      affineStateFunctional s f := by
  exact affineExpectation_flow_invariant s F t f

end InfoGeometry.Topology.PauliJungD4Star
