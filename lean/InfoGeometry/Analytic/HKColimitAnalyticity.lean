import InfoGeometry.Canonical.FilteredDirectLimitOperatorUniqueness

noncomputable section

namespace InfoGeometry.Analytic.HKColimitAnalyticity

open InfoGeometry.Canonical.FilteredDirectLimitOperator

universe u

variable
    (Stage : ℕ → Type u)
    [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)

/-- A filtered Hestenes-Krein phase is a compatible family of additive stage
operators whose square is minus the identity at every finite stage. -/
structure FilteredKreinPhaseFamily extends CompatibleOperatorFamily Stage f where
  phase_sq : ∀ n x, op n (op n x) = -x

namespace FilteredKreinPhaseFamily

variable (J : FilteredKreinPhaseFamily Stage f)

/-- The Hestenes-Krein phase induced on Mathlib's additive direct limit. -/
def directLimitPhase :
    AddCommGroup.DirectLimit Stage f →+
      AddCommGroup.DirectLimit Stage f :=
  CompatibleOperatorFamily.directLimitOperator
    Stage f J.toCompatibleOperatorFamily

@[simp]
theorem directLimitPhase_of (n : ℕ) (x : Stage n) :
    directLimitPhase Stage f J (AddCommGroup.DirectLimit.of Stage f n x) =
      AddCommGroup.DirectLimit.of Stage f n (J.op n x) :=
  CompatibleOperatorFamily.directLimitOperator_of
    Stage f J.toCompatibleOperatorFamily n x

/-- The finite Hestenes-Krein identity `Jₙ² = -I` survives the filtered
inductive colimit exactly. -/
theorem directLimitPhase_sq_apply
    (z : AddCommGroup.DirectLimit Stage f) :
    directLimitPhase Stage f J (directLimitPhase Stage f J z) = -z := by
  refine AddCommGroup.DirectLimit.induction_on z ?_
  intro n x
  rw [directLimitPhase_of, directLimitPhase_of, J.phase_sq]
  exact (AddCommGroup.DirectLimit.of Stage f n).map_neg x

/-- A colimit Hestenes-Krein phase has trivial kernel. -/
theorem directLimitPhase_eq_zero_iff
    (z : AddCommGroup.DirectLimit Stage f) :
    directLimitPhase Stage f J z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h := congrArg (directLimitPhase Stage f J) hz
    rw [directLimitPhase_sq_apply, map_zero] at h
    exact neg_eq_zero.mp h
  · rintro rfl
    exact map_zero (directLimitPhase Stage f J)

/-- The descended Hestenes-Krein phase is injective, without any analytic
continuation or density assumption. -/
theorem directLimitPhase_injective :
    Function.Injective (directLimitPhase Stage f J) := by
  intro x y hxy
  have h := congrArg (directLimitPhase Stage f J) hxy
  simpa only [directLimitPhase_sq_apply, neg_inj] using h

end FilteredKreinPhaseFamily

end InfoGeometry.Analytic.HKColimitAnalyticity
