import Mathlib.Tactic

namespace Omega.Zeta

def xi_jet_psd_equivalence_rh (jet : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, jet k = 0

/-- Caratheodory positivity at every finite horizon. -/
def xi_jet_psd_equivalence_caratheodory_positive (caratheodoryMoment : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 0 ≤ caratheodoryMoment N

/-- The finite Toeplitz PSD predicate at one horizon, represented by the audited principal
minor used as the finite failure projection. -/
def xi_jet_psd_equivalence_horizon_toeplitz_psd
    (toeplitzPrincipalMinor : ℕ → ℝ) (N : ℕ) : Prop :=
  0 ≤ toeplitzPrincipalMinor N

/-- Toeplitz PSD at every finite horizon. -/
def xi_jet_psd_equivalence_all_level_toeplitz_psd
    (toeplitzPrincipalMinor : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, xi_jet_psd_equivalence_horizon_toeplitz_psd toeplitzPrincipalMinor N

/-- A projected finite PSD failure witness. -/
def xi_jet_psd_equivalence_finite_psd_failure
    (toeplitzPrincipalMinor : ℕ → ℝ) (N : ℕ) : Prop :=
  toeplitzPrincipalMinor N < 0

/-- Paper-facing statement: RH, Caratheodory positivity, and the all-level Toeplitz PSD tower are
equivalent, and failure of the tower projects to a finite negative principal witness. -/
def xi_jet_psd_equivalence_statement
    (jet caratheodoryMoment toeplitzPrincipalMinor : ℕ → ℝ)
    (coefficientLocalization :
      (∀ k : ℕ, jet k = 0) ↔ ∀ N : ℕ, 0 ≤ caratheodoryMoment N)
    (horizonToeplitzLMI :
      ∀ N : ℕ,
        0 ≤ caratheodoryMoment N ↔ 0 ≤ toeplitzPrincipalMinor N) : Prop :=
  (xi_jet_psd_equivalence_rh jet ↔
    xi_jet_psd_equivalence_caratheodory_positive caratheodoryMoment) ∧
    (xi_jet_psd_equivalence_caratheodory_positive caratheodoryMoment ↔
      xi_jet_psd_equivalence_all_level_toeplitz_psd toeplitzPrincipalMinor) ∧
      (xi_jet_psd_equivalence_rh jet ↔
        xi_jet_psd_equivalence_all_level_toeplitz_psd toeplitzPrincipalMinor) ∧
        (¬ xi_jet_psd_equivalence_all_level_toeplitz_psd toeplitzPrincipalMinor →
          ∃ N : ℕ,
            xi_jet_psd_equivalence_finite_psd_failure toeplitzPrincipalMinor N)

/-- Paper label: `thm:xi-jet-psd-equivalence`. -/
theorem paper_xi_jet_psd_equivalence
    (jet caratheodoryMoment toeplitzPrincipalMinor : ℕ → ℝ)
    (coefficientLocalization :
      (∀ k : ℕ, jet k = 0) ↔ ∀ N : ℕ, 0 ≤ caratheodoryMoment N)
    (horizonToeplitzLMI :
      ∀ N : ℕ,
        0 ≤ caratheodoryMoment N ↔ 0 ≤ toeplitzPrincipalMinor N) :
    xi_jet_psd_equivalence_statement jet caratheodoryMoment toeplitzPrincipalMinor
      coefficientLocalization horizonToeplitzLMI := by
  classical
  have hRHCarath :
      xi_jet_psd_equivalence_rh jet ↔
        xi_jet_psd_equivalence_caratheodory_positive caratheodoryMoment := by
    simpa [xi_jet_psd_equivalence_rh, xi_jet_psd_equivalence_caratheodory_positive] using
      coefficientLocalization
  have hCarathToeplitz :
      xi_jet_psd_equivalence_caratheodory_positive caratheodoryMoment ↔
        xi_jet_psd_equivalence_all_level_toeplitz_psd toeplitzPrincipalMinor := by
    constructor
    · intro hcarath N
      exact (horizonToeplitzLMI N).mp (hcarath N)
    · intro htoeplitz N
      exact (horizonToeplitzLMI N).mpr (htoeplitz N)
  have hRHToeplitz :
      xi_jet_psd_equivalence_rh jet ↔
        xi_jet_psd_equivalence_all_level_toeplitz_psd toeplitzPrincipalMinor :=
    hRHCarath.trans hCarathToeplitz
  refine ⟨hRHCarath, hCarathToeplitz, hRHToeplitz, ?_⟩
  intro hnot
  rw [xi_jet_psd_equivalence_all_level_toeplitz_psd] at hnot
  push_neg at hnot
  rcases hnot with ⟨N, hN⟩
  have hN' : ¬ 0 ≤ toeplitzPrincipalMinor N := by
    simpa [xi_jet_psd_equivalence_horizon_toeplitz_psd] using hN
  exact ⟨N, lt_of_not_ge hN'⟩

end Omega.Zeta
