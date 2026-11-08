import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact two-level chiral oscillation bridge

This owner formalizes the universal algebra of a symmetric two-level Hamiltonian

`H = [[E0, Δ], [Δ, E0]]`.

It proves the symmetric/antisymmetric eigenmodes, their signed splitting, the
nonnegative spectral gap, and the elementary transition-probability identities.
These results apply to any concrete two-level realization once an explicit
intertwiner identifies its physical states and Hamiltonian with this carrier.

No theorem here identifies a von Neumann algebra with its commutant, equates
Tomita modular conjugation with a tunneling Hamiltonian, or claims that all mass
gaps arise from this mechanism.
-/

noncomputable section

namespace InfoGeometry.Nuclear.TwoLevelChiralOscillationBridge

abbrev Mode2 := Fin 2
abbrev Vec2 := Mode2 → ℝ
abbrev Mat2 := Matrix Mode2 Mode2 ℝ

/-- Symmetric two-level Hamiltonian with common diagonal energy `E0` and
real off-diagonal coupling `Delta`. -/
def chiralHamiltonian (E0 Delta : ℝ) : Mat2 :=
  !![E0, Delta; Delta, E0]

/-- Symmetric mode. -/
def symmetricMode : Vec2 := ![1, 1]

/-- Antisymmetric mode. -/
def antisymmetricMode : Vec2 := ![1, -1]

/-- The symmetric mode has eigenvalue `E0 + Delta`. -/
theorem symmetricMode_eigen (E0 Delta : ℝ) :
    (chiralHamiltonian E0 Delta).mulVec symmetricMode =
      (E0 + Delta) • symmetricMode := by
  funext i
  fin_cases i <;>
    simp [chiralHamiltonian, symmetricMode, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  all_goals ring

/-- The antisymmetric mode has eigenvalue `E0 - Delta`. -/
theorem antisymmetricMode_eigen (E0 Delta : ℝ) :
    (chiralHamiltonian E0 Delta).mulVec antisymmetricMode =
      (E0 - Delta) • antisymmetricMode := by
  funext i
  fin_cases i <;>
    simp [chiralHamiltonian, antisymmetricMode, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  all_goals ring

/-- Signed eigenvalue splitting. -/
theorem signed_energy_splitting (E0 Delta : ℝ) :
    (E0 + Delta) - (E0 - Delta) = 2 * Delta := by
  ring

/-- The physical nonnegative spectral gap is twice the absolute coupling. -/
theorem spectral_gap_abs (E0 Delta : ℝ) :
    |(E0 + Delta) - (E0 - Delta)| = 2 * |Delta| := by
  rw [signed_energy_splitting]
  simp [abs_mul]

/-- Transition probability in units where `ℏ = 1`. -/
def transitionProbability (Delta t : ℝ) : ℝ :=
  Real.sin (Delta * t) ^ 2

/-- The transition probability is nonnegative. -/
theorem transitionProbability_nonneg (Delta t : ℝ) :
    0 ≤ transitionProbability Delta t := by
  unfold transitionProbability
  exact sq_nonneg _

/-- The transition probability is bounded by one. -/
theorem transitionProbability_le_one (Delta t : ℝ) :
    transitionProbability Delta t ≤ 1 := by
  unfold transitionProbability
  have h₁ := Real.neg_one_le_sin (Delta * t)
  have h₂ := Real.sin_le_one (Delta * t)
  nlinarith

/-- At `t = π/(2 Delta)` a nonzero coupling gives complete transfer. -/
theorem transitionProbability_quarter_cycle
    (Delta : ℝ) (hDelta : Delta ≠ 0) :
    transitionProbability Delta (Real.pi / (2 * Delta)) = 1 := by
  have harg : Delta * (Real.pi / (2 * Delta)) = Real.pi / 2 := by
    field_simp [hDelta]
  rw [transitionProbability, harg, Real.sin_pi_div_two]
  norm_num

/-- The probability oscillation has the double-angle form, exposing the
angular-frequency parameter `2 Delta` in units `ℏ = 1`. -/
theorem transitionProbability_double_angle (Delta t : ℝ) :
    transitionProbability Delta t =
      (1 - Real.cos (2 * Delta * t)) / 2 := by
  rw [transitionProbability]
  have h := Real.cos_two_mul (Delta * t)
  have hsc := Real.sin_sq_add_cos_sq (Delta * t)
  have harg : 2 * Delta * t = 2 * (Delta * t) := by ring
  rw [harg, h]
  nlinarith

/-- Restoring `ℏ`, the angular-frequency magnitude associated with the two-level
spectral gap is `2 |Delta| / ℏ`. -/
def oscillationAngularFrequency (Delta hbar : ℝ) : ℝ :=
  2 * |Delta| / hbar

/-- If `ℏ > 0`, the frequency is exactly the nonnegative spectral gap divided
by `ℏ`. -/
theorem oscillationAngularFrequency_eq_gap_div_hbar
    (E0 Delta hbar : ℝ) :
    oscillationAngularFrequency Delta hbar =
      |(E0 + Delta) - (E0 - Delta)| / hbar := by
  rw [oscillationAngularFrequency, spectral_gap_abs]

end InfoGeometry.Nuclear.TwoLevelChiralOscillationBridge

end noncomputable section
