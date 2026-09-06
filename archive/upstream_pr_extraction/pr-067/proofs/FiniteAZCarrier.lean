import Mathlib

/-!
# Vector-level AZ carrier

The Hilbert--Schmidt Tomita carrier is an algebra carrier.  The CI-type
antiunitary square belongs instead to a vector-level carrier.  This owner
records the minimal algebraic hypotheses and derives the AZ identities without
pretending that inner conjugation on `HS(M₆)` has square `-1`.
-/

noncomputable section

structure AZCarrier (V : Type*) [AddCommGroup V] [Module ℂ V] where
  gamma : V → V
  timeReversal : V → V
  gamma_sq : ∀ v, gamma (gamma v) = v
  timeReversal_sq : ∀ v, timeReversal (timeReversal v) = v
  gamma_neg : ∀ v, gamma (-v) = -gamma v
  timeReversal_gamma : ∀ v,
    timeReversal (gamma (timeReversal v)) = -gamma v

namespace AZCarrier

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

 def azTimeReversal (C : AZCarrier V) : V → V := C.timeReversal

 def azParticleHole (C : AZCarrier V) : V → V :=
  fun v => C.gamma (C.timeReversal v)

@[simp] theorem azTimeReversal_sq (C : AZCarrier V) (v : V) :
    azTimeReversal C (azTimeReversal C v) = v :=
  C.timeReversal_sq v

@[simp] theorem azParticleHole_sq (C : AZCarrier V) (v : V) :
    azParticleHole C (azParticleHole C v) = -v := by
  unfold azParticleHole
  rw [C.timeReversal_gamma, C.gamma_neg, C.gamma_sq]

 theorem azParticleHole_timeReversal (C : AZCarrier V) (v : V) :
    azParticleHole C (azTimeReversal C v) = C.gamma v := by
  unfold azParticleHole azTimeReversal
  rw [C.timeReversal_sq]

end AZCarrier
end noncomputable section
