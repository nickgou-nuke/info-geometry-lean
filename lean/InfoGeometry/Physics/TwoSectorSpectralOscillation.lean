import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

open Matrix

namespace InfoGeometry.Physics.TwoSector

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev Vec2 := InfoGeometry.Algebra.FiniteSpin.Vec2R

/-!
# Exact Symmetric Two-Sector Spectral Splitting and Coherent Oscillation

This module formalizes the exact mathematical core of symmetric two-sector quantum systems:
1. **Generic Two-Sector Hamiltonian**:
   $H(E_0, \Delta) = \begin{pmatrix} E_0 & \Delta \\ \Delta & E_0 \end{pmatrix} = E_0 I_2 + \Delta \sigma_x$.
2. **Explicit Symmetric and Antisymmetric Eigenmodes**:
   - $|+\rangle = (1, 1)$ with eigenvalue $E_+ = E_0 + \Delta$,
   - $|-\rangle = (1, -1)$ with eigenvalue $E_- = E_0 - \Delta$.
3. **Signed Splitting & Nonnegative Physical Spectral Gap**:
   - Signed splitting: $E_+ - E_- = 2\Delta$,
   - Physical gap: $\Delta E = |E_+ - E_-| = 2|\Delta|$.
4. **Coherent Sector Transfer Channel**:
   $P_{L \to R}(t) = \sin^2(\Delta t) = \frac{1 - \cos(2\Delta t)}{2}$ (in natural units $\hbar = 1$),
   with angular frequency $\omega = 2|\Delta| = \Delta E$, and complete transfer at $t = \frac{\pi}{2\Delta}$ ($\Delta \ne 0$).

All proofs are complete in native Lean 4 with 0 `sorry`s and 0 axioms.
-/

/-! ### 1. The Generic Two-Sector Hamiltonian -/

/-- Symmetric two-sector Hamiltonian $H(E_0, \Delta) = \begin{pmatrix} E_0 & \Delta \\ \Delta & E_0 \end{pmatrix}$. -/
def twoSectorHamiltonian (E0 Delta : ℝ) : Mat2 :=
  !![E0, Delta; Delta, E0]

/-- **THE SECULAR CHARACTERISTIC DETERMINANT THEOREM**:
    $\det(H(E_0, \Delta) - E I_2) = (E - (E_0 - \Delta))(E - (E_0 + \Delta))$. -/
theorem secular_roots (E0 Delta E : ℝ) :
    det (twoSectorHamiltonian E0 Delta - E • (1 : Mat2)) =
    (E - (E0 - Delta)) * (E - (E0 + Delta)) := by
  dsimp [twoSectorHamiltonian]
  simp [det_fin_two]
  ring

/-! ### 2. Explicit Eigenmodes & Eigenvalues -/

/-- The symmetric eigenmode $|+\rangle = (1, 1)$. -/
def eigenPlus : Vec2 := ![1, 1]

/-- The antisymmetric eigenmode $|-\rangle = (1, -1)$. -/
def eigenMinus : Vec2 := ![1, -1]

/-- **THE SYMMETRIC EIGENVALUE THEOREM**:
    $H |+\rangle = (E_0 + \Delta) |+\rangle$. -/
theorem plus_eigenmode (E0 Delta : ℝ) :
    mulVec (twoSectorHamiltonian E0 Delta) eigenPlus =
    (E0 + Delta) • eigenPlus := by
  dsimp [twoSectorHamiltonian, eigenPlus, mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-- **THE ANTISYMMETRIC EIGENVALUE THEOREM**:
    $H |-\rangle = (E_0 - \Delta) |-\rangle$. -/
theorem minus_eigenmode (E0 Delta : ℝ) :
    mulVec (twoSectorHamiltonian E0 Delta) eigenMinus =
    (E0 - Delta) • eigenMinus := by
  dsimp [twoSectorHamiltonian, eigenMinus, mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-! ### 3. Spectral Splitting and Nonnegative Gap -/

/-- **THE SIGNED SPLITTING THEOREM**:
    $(E_0 + \Delta) - (E_0 - \Delta) = 2\Delta$. -/
theorem signed_splitting (E0 Delta : ℝ) :
    (E0 + Delta) - (E0 - Delta) = 2 * Delta := by
  ring

/-- **THE NONNEGATIVE PHYSICAL SPECTRAL GAP THEOREM**:
    $|(E_0 + \Delta) - (E_0 - \Delta)| = 2 |\Delta|$. -/
theorem physical_spectral_gap (E0 Delta : ℝ) :
    |(E0 + Delta) - (E0 - Delta)| = 2 * |Delta| := by
  have h_diff : (E0 + Delta) - (E0 - Delta) = 2 * Delta := signed_splitting E0 Delta
  rw [h_diff]
  have h_two : |(2 : ℝ) * Delta| = |(2 : ℝ)| * |Delta| := abs_mul 2 Delta
  have h_pos : |(2 : ℝ)| = 2 := by norm_num
  rw [h_two, h_pos]

/-! ### 4. Coherent Transition Probability & Oscillation Frequency -/

/-- Coherent transition probability between orthogonal sectors $P_{L \to R}(t) = \sin^2(\Delta t)$. -/
def transitionProb (Delta t : ℝ) : ℝ :=
  (Real.sin (Delta * t)) ^ 2

/-- **THE DOUBLE-ANGLE IDENTITY THEOREM**:
    $P_{L \to R}(t) = \frac{1 - \cos(2\Delta t)}{2}$, exhibiting angular frequency $2|\Delta|$. -/
theorem transition_double_angle (Delta t : ℝ) :
    transitionProb Delta t = (1 - Real.cos (2 * Delta * t)) / 2 := by
  dsimp [transitionProb]
  have h_cos : Real.cos (2 * (Delta * t)) = 1 - 2 * (Real.sin (Delta * t)) ^ 2 := by
    have h_double := Real.cos_two_mul (Delta * t)
    have h_sq : (Real.cos (Delta * t)) ^ 2 = 1 - (Real.sin (Delta * t)) ^ 2 := by
      have h_pyth := Real.sin_sq_add_cos_sq (Delta * t)
      linarith
    linarith
  have h_eq : 2 * Delta * t = 2 * (Delta * t) := by ring
  rw [h_eq, h_cos]
  ring

/-- **THE BOUNDED PROBABILITY THEOREM**:
    $0 \le P_{L \to R}(t) \le 1$. -/
theorem transition_prob_bounds (Delta t : ℝ) :
    0 ≤ transitionProb Delta t ∧ transitionProb Delta t ≤ 1 := by
  dsimp [transitionProb]
  have h_nonneg : 0 ≤ (Real.sin (Delta * t)) ^ 2 := sq_nonneg _
  have h_le_one : (Real.sin (Delta * t)) ^ 2 ≤ 1 := by
    have h_abs := Real.abs_sin_le_one (Delta * t)
    have h_sq : |Real.sin (Delta * t)| ^ 2 ≤ 1 ^ 2 := by
      have h_abs_nonneg := abs_nonneg (Real.sin (Delta * t))
      nlinarith [sq_nonneg (1 - |Real.sin (Delta * t)|)]
    rwa [sq_abs, one_pow] at h_sq
  exact ⟨h_nonneg, h_le_one⟩

/-- **THE COMPLETE TRANSFER QUARTER-PERIOD THEOREM**:
    At $t = \frac{\pi}{2\Delta}$ ($\Delta \ne 0$), complete sector transfer is achieved: $P_{L \to R} = 1$. -/
theorem complete_transfer_at_quarter_period (Delta : ℝ) (hD : Delta ≠ 0) :
    transitionProb Delta (Real.pi / (2 * Delta)) = 1 := by
  dsimp [transitionProb]
  have h_arg : Delta * (Real.pi / (2 * Delta)) = Real.pi / 2 := by
    calc
      Delta * (Real.pi / (2 * Delta)) = (Delta / Delta) * (Real.pi / 2) := by ring
      _ = 1 * (Real.pi / 2) := by rw [div_self hD]
      _ = Real.pi / 2 := by ring
  rw [h_arg, Real.sin_pi_div_two]
  ring

end InfoGeometry.Physics.TwoSector
