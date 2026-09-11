import InfoGeometry.Canonical.BogoliubovFrameKreinMetricBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Multi-parameter connection coefficients

This owner stays on the associative doubled endomorphism carrier.  The base
actions and connection coefficients are explicit inputs; no octonionic
associator is identified with curvature.
-/

noncomputable section

namespace InfoGeometry.Canonical

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Covariant action of a base endomorphism action and a connection generator. -/
def covariantDerivation
    (δ : EndH → EndH) (X : EndH) : EndH → EndH :=
  fun A => δ A + X.comp A - A.comp X

@[simp] theorem covariantDerivation_apply
    (δ : EndH → EndH) (X A : EndH) :
    covariantDerivation δ X A = δ A + X.comp A - A.comp X := rfl

/-- The coefficient form of the curvature of two connection directions. -/
def connectionCurvature
    (δa δb : EndH → EndH) (Xa Xb : EndH) : EndH :=
  δa Xb - δb Xa + Xa.comp Xb - Xb.comp Xa

theorem connectionCurvature_swap
    (δa δb : EndH → EndH) (Xa Xb : EndH) :
    connectionCurvature δb δa Xb Xa =
      -connectionCurvature δa δb Xa Xb := by
  unfold connectionCurvature
  module

theorem connectionCurvature_eq_base_difference_plus_bracket
    (δa δb : EndH → EndH) (Xa Xb : EndH) :
    connectionCurvature δa δb Xa Xb =
      (δa Xb - δb Xa) + (Xa.comp Xb - Xb.comp Xa) := by
  unfold connectionCurvature
  module

theorem connectionCurvature_commuting_base
    (δa δb : EndH → EndH) (Xa Xb : EndH)
    (hbase : δa Xb - δb Xa = 0) :
    connectionCurvature δa δb Xa Xb =
      Xa.comp Xb - Xb.comp Xa := by
  rw [connectionCurvature_eq_base_difference_plus_bracket, hbase, zero_add]

end InfoGeometry.Canonical
