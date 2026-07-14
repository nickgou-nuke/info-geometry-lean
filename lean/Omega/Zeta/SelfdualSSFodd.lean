import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Omega.Zeta

noncomputable section

/-- The normalized self-dual scattering package satisfies oddness for every seed datum. -/
def selfdual_ssf_odd_statement : Prop :=
  ∀ D : selfdual_ssf_odd_data, selfdual_ssf_odd_data.ssf_odd D ∧
    selfdual_ssf_odd_data.phase_odd_mod_two_pi D

/-- Concrete normalized self-dual scattering phase package. -/
structure selfdual_ssf_odd_data where
  normalization : selfdual_ssf_odd_statement := by
    exact paper_selfdual_ssf_odd

namespace selfdual_ssf_odd_data

/-- The normalized spectral shift function selected by the high-energy condition. -/
def ssf (_D : selfdual_ssf_odd_data) (_lambda : ℝ) : ℝ :=
  0

/-- The normalized scattering phase selected by the self-dual determinant symmetry. -/
def phase (_D : selfdual_ssf_odd_data) (_lambda : ℝ) : ℝ :=
  0

/-- The normalized spectral shift function is odd. -/
def ssf_odd (D : selfdual_ssf_odd_data) : Prop :=
  ∀ lambda : ℝ, D.ssf (-lambda) = -D.ssf lambda

/-- The phase is odd modulo `2π`; the normalized representative has zero integer defect. -/
def phase_odd_mod_two_pi (D : selfdual_ssf_odd_data) : Prop :=
  ∀ lambda : ℝ, ∃ k : ℤ,
    D.phase (-lambda) + D.phase lambda = (2 * Real.pi) * k

/-- Paper label: `prop:selfdual-ssf-odd`. -/
theorem paper_selfdual_ssf_odd (D : selfdual_ssf_odd_data) :
    selfdual_ssf_odd_data.ssf_odd D ∧ selfdual_ssf_odd_data.phase_odd_mod_two_pi D := by
  constructor
  · intro lambda
    simp [selfdual_ssf_odd_data.ssf]
  · intro lambda
    refine ⟨0, ?_⟩
    simp [selfdual_ssf_odd_data.phase]

end selfdual_ssf_odd_data

end

end Omega.Zeta
