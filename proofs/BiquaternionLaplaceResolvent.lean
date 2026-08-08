import proofs.BiquaternionLaplaceTripotent

/-!
# Biquaternion Laplace resolvent

Integrated repair of the external resolvent file.  The buildable core is the
Pauli biquaternion resolvent numerator/denominator identity already active in
`BiquaternionLaplaceTripotent`.
-/

noncomputable section

namespace BiquaternionLaplaceResolvent

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

/-- The closed-form numerator is both a left and a right resolvent numerator. -/
theorem resolvent_identity_left_and_right (s a0 a1 a2 a3 : ℂ) :
    (s • (1 : M2C) - X a0 a1 a2 a3) * resolventNumerator s a0 a1 a2 a3 =
      resolventDenominator s a0 a1 a2 a3 • (1 : M2C) ∧
    resolventNumerator s a0 a1 a2 a3 * (s • (1 : M2C) - X a0 a1 a2 a3) =
      resolventDenominator s a0 a1 a2 a3 • (1 : M2C) := by
  constructor
  · exact resolvent_identity_left s a0 a1 a2 a3
  · exact resolvent_identity_right s a0 a1 a2 a3

#check resolvent_identity_left
#check resolvent_identity_right
#check resolvent_identity_left_and_right

end BiquaternionLaplaceResolvent
