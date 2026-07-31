import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.Core.OdometerJoukowsky
import Omega.SyncKernelWeighted.TracePalindrome

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The half-phase-normalized completed amplitude on the unit circle. For the concrete family
`a_n(u) = (u + 1)^n`, this is `J(e^{i θ / 2})^n`. -/
def completedAmplitude (n : ℕ) (θ : ℝ) : ℂ :=
  (Omega.POM.joukowsky (Complex.exp ((((θ / 2 : ℝ) : ℂ) * Complex.I)))) ^ n

/-- The completed amplitude takes real values. -/
def completedAmplitudeReal (n : ℕ) : Prop :=
  ∀ θ : ℝ, ∃ r : ℝ, completedAmplitude n θ = r

/-- The completed amplitude is an even function of the phase. -/
def completedAmplitudeEven (n : ℕ) : Prop :=
  ∀ θ : ℝ, completedAmplitude n (-θ) = completedAmplitude n θ

lemma completedAmplitude_eq_cosine_power (n : ℕ) (θ : ℝ) :
    completedAmplitude n θ = (2 * Real.cos (θ / 2) : ℂ) ^ n := by
  unfold completedAmplitude
  rw [Omega.POM.joukowsky_exp_I_mul (θ / 2)]

lemma completedAmplitudeReal_true (n : ℕ) : completedAmplitudeReal n := by
  intro θ
  refine ⟨(2 * Real.cos (θ / 2)) ^ n, ?_⟩
  simpa using completedAmplitude_eq_cosine_power n θ

lemma completedAmplitudeEven_true (n : ℕ) : completedAmplitudeEven n := by
  intro θ
  rw [completedAmplitude_eq_cosine_power, completedAmplitude_eq_cosine_power]
  congr 1
  have hhalf : (-θ) / 2 = -(θ / 2) := by ring
  rw [hhalf, Real.cos_neg]

/-- Paper label: `cor:trace-palindrome-completed-real`. -/
theorem paper_trace_palindrome_completed_real (n : ℕ) :
    completedAmplitudeReal n ∧ completedAmplitudeEven n := by
  let _ := paper_trace_palindrome
  exact ⟨completedAmplitudeReal_true n, completedAmplitudeEven_true n⟩

end

end Omega.SyncKernelWeighted
