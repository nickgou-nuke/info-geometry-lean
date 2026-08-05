import InfoGeometry.Canonical.FilteredDirectLimitOperator

/-!
# HK colimit analyticity

This file records a small direct-limit phase transport package.
It does not rebuild analytic continuation or a full KMS theory.
-/

noncomputable section

namespace InfoGeometry.Analytic.HKColimitAnalyticity

open InfoGeometry.Canonical.FilteredDirectLimitOperator

universe u

variable
    (Stage : ℕ → Type u)
    [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)

/-- A compatible filtered family of stage-wise involutive phase operators. -/
structure FilteredKreinPhaseFamily where
  op : ∀ n, Stage n →+ Stage n
  phase_sq : ∀ n (x : Stage n), op n (op n x) = -x
  commutes :
    ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
      op n (f m n h x) = f m n h (op m x)

namespace FilteredKreinPhaseFamily

variable (J : FilteredKreinPhaseFamily Stage f)

/-- The induced additive endomorphism on the direct limit. -/
def directLimitPhase :
    AddCommGroup.DirectLimit Stage f →+
      AddCommGroup.DirectLimit Stage f :=
  CompatibleOperatorFamily.directLimitOperator
    Stage f J.op J.commutes

@[simp]
theorem directLimitPhase_of (n : ℕ) (x : Stage n) :
    directLimitPhase Stage f J
        (AddCommGroup.DirectLimit.of Stage f n x) =
      AddCommGroup.DirectLimit.of Stage f n (J.op n x) := by
  simpa [directLimitPhase] using
    CompatibleOperatorFamily.directLimitOperator_of
      Stage f J.op J.commutes n x

/-- The descended phase squares to `-1` on the filtered direct limit. -/
theorem directLimitPhase_sq_apply
    (z : AddCommGroup.DirectLimit Stage f) :
    directLimitPhase Stage f J
        (directLimitPhase Stage f J z) = -z := by
  refine Module.DirectLimit.induction_on z ?_
  intro n x
  change directLimitPhase Stage f J
      (directLimitPhase Stage f J
        (AddCommGroup.DirectLimit.of Stage f n x)) =
      -(AddCommGroup.DirectLimit.of Stage f n x)
  simp [directLimitPhase, J.phase_sq n x]

/-- The direct-limit phase map has trivial fixed-point kernel. -/
theorem directLimitPhase_eq_zero_iff
    (z : AddCommGroup.DirectLimit Stage f) :
    directLimitPhase Stage f J z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h := congrArg (directLimitPhase Stage f J) hz
    rw [directLimitPhase_sq_apply Stage f J z, map_zero] at h
    exact neg_eq_zero.mp h
  · rintro rfl
    simp [directLimitPhase]

/-- The induced direct-limit phase is injective. -/
theorem directLimitPhase_injective :
    Function.Injective (directLimitPhase Stage f J) := by
  intro x y hxy
  have h := congrArg (directLimitPhase Stage f J) hxy
  rw [directLimitPhase_sq_apply Stage f J x,
    directLimitPhase_sq_apply Stage f J y] at h
  exact neg_inj.mp h

end FilteredKreinPhaseFamily

end InfoGeometry.Analytic.HKColimitAnalyticity
