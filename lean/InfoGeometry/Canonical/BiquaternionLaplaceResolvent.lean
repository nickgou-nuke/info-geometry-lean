import InfoGeometry.Canonical.BiquaternionLaplaceTripotent

/-!
# Biquaternion Laplace resolvent

Maintained owner for the recovered Laplace-resolvent finite slice. The buildable
core is the Pauli biquaternion resolvent numerator/denominator identity routed
through the canonical Laplace/tripotent owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.BiquaternionLaplaceResolvent

abbrev M2C := BiquaternionLaplaceTripotent.M2C

def X (a0 a1 a2 a3 : ℂ) : M2C := BiquaternionLaplaceTripotent.biquatX a0 a1 a2 a3

def v_sq (a1 a2 a3 : ℂ) : ℂ := a1 * a1 + a2 * a2 + a3 * a3

def resolventNumerator (s a0 a1 a2 a3 : ℂ) : M2C :=
  BiquaternionLaplaceTripotent.resolventNumerator s a0 a1 a2 a3

def resolventDenominator (s a0 a1 a2 a3 : ℂ) : ℂ :=
  BiquaternionLaplaceTripotent.resolventDenominator s a0 a1 a2 a3

/-- Left resolvent identity `(sI-X)N=ΔI`. -/
theorem resolvent_identity_left (s a0 a1 a2 a3 : ℂ) :
    (s • (1 : M2C) - X a0 a1 a2 a3) * resolventNumerator s a0 a1 a2 a3 =
      resolventDenominator s a0 a1 a2 a3 • (1 : M2C) :=
  BiquaternionLaplaceTripotent.biquat_resolvent_left s a0 a1 a2 a3

/-- Right resolvent identity `N(sI-X)=ΔI`. -/
theorem resolvent_identity_right (s a0 a1 a2 a3 : ℂ) :
    resolventNumerator s a0 a1 a2 a3 * (s • (1 : M2C) - X a0 a1 a2 a3) =
      resolventDenominator s a0 a1 a2 a3 • (1 : M2C) :=
  BiquaternionLaplaceTripotent.biquat_resolvent_right s a0 a1 a2 a3

/-- Consolidated closed-form resolvent certificate. -/
theorem laplace_resolvent_synthesis (s a0 a1 a2 a3 : ℂ) :
    (s • (1 : M2C) - X a0 a1 a2 a3) * resolventNumerator s a0 a1 a2 a3 =
      resolventDenominator s a0 a1 a2 a3 • (1 : M2C) ∧
    resolventNumerator s a0 a1 a2 a3 * (s • (1 : M2C) - X a0 a1 a2 a3) =
      resolventDenominator s a0 a1 a2 a3 • (1 : M2C) := by
  exact ⟨resolvent_identity_left s a0 a1 a2 a3, resolvent_identity_right s a0 a1 a2 a3⟩

end InfoGeometry.Canonical.BiquaternionLaplaceResolvent
