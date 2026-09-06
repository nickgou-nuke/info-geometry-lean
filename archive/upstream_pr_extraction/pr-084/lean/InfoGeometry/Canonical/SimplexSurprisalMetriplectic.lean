import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Convex.Bregman

/-!
# Simplex Surprisal Metriplectic Core

Finite algebraic core of the simplex `(s, 1-s)` surprisal geometry:

* the 2-level quantum state `ρ(s) = diag(s, 1-s)` with `s ∈ [0, 1]`;
* the logit coordinate `τ(s) = s / (1-s)` and relative surprisal `W(s) = ln τ(s)`;
* the quantum surprisal operator `Î = -ln ρ`;
* the maximally mixed center `s = 1/2` with `τ = 1`, `W = 0`, `Î = (ln 2)·I`;
* the Cayley inversion `τ(1-s) = 1/τ(s)` giving `W(1-s) = -W(s)`;
* the twin thermal flow superposition `Ψ = 2 Φ(y) cos(ty)`.

All claims are finite and algebraic.  No infinities, no analytic continuation,
no measure-theoretic large-deviation debt.
-/

noncomputable section

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-! ## 1. Simplex state and logit coordinates -/

/-- The 1D quantum 2-level state (binary probability simplex):
    `ρ(s) = diag(s, 1-s)` for `s ∈ [0, 1]`. -/
structure SimplexState where
  s : ℝ
  hs0 : 0 ≤ s
  hs1 : s ≤ 1

namespace SimplexState

variable (S : SimplexState)

/-- Logit coordinate `τ(s) = s / (1-s) ∈ (0, +∞)`. -/
def tau : ℝ :=
  S.s / (1 - S.s)

/-- Relative surprisal (log-odds) `W(s) = ln τ(s) = ln(s/(1-s))`. -/
def W : ℝ :=
  Real.log S.tau

/-- The complementary state `1-s`. -/
def complement : SimplexState where
  s := 1 - S.s
  hs0 := by linarith [S.hs1]
  hs1 := by linarith [S.hs0]

/-- The logit of the complement is the inverse logit. -/
theorem tau_complement : S.complement.tau = 1 / S.tau := by
  unfold tau complement
  field_simp
  ring

/-- The relative surprisal of the complement is the negative surprisal. -/
theorem W_complement : S.complement.W = -S.W := by
  unfold W
  rw [tau_complement S, one_div, Real.log_inv]

end SimplexState

/-! ## 2. Quantum surprisal operator -/

/-- The quantum surprisal operator for a simplex state:
    `Î = -ln ρ = diag(-ln s, -ln(1-s))`. -/
def surprisalOperator (S : SimplexState) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ -Real.log S.s, 0; 0, -Real.log (1 - S.s) ]

/-- The diagonal entries are the pointwise surprisals. -/
@[simp]
theorem surprisalOperator_diag (S : SimplexState) (i : Fin 2) :
    surprisalOperator S i i = if i = 0 then -Real.log S.s else -Real.log (1 - S.s) := by
  fin_cases i <;> simp [surprisalOperator]

/-- The off-diagonal entries vanish. -/
@[simp]
theorem surprisalOperator_offdiag (S : SimplexState) {i j : Fin 2} (hij : i ≠ j) :
    surprisalOperator S i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [surprisalOperator]

/-- The trace is the unweighted sum of the two pointwise surprisals. -/
theorem trace_surprisalOperator_eq_entropy (S : SimplexState) :
    Matrix.trace (surprisalOperator S) =
      -Real.log S.s - Real.log (1 - S.s) := by
  simp [surprisalOperator, Matrix.trace, Fin.sum_univ_two]
  ring

/-! ## 3. Maximally mixed center -/

/-- The maximally mixed center `s = 1/2`. -/
def centerState : SimplexState where
  s := 1 / 2
  hs0 := by norm_num
  hs1 := by norm_num

/-- At the center, `τ = 1`. -/
theorem centerState_tau : centerState.tau = 1 := by
  simp [centerState, SimplexState.tau]
  <;> norm_num

/-- At the center, `W = 0`. -/
theorem centerState_W : centerState.W = 0 := by
  simp [centerState, SimplexState.W, SimplexState.tau]
  <;> norm_num [Real.log_one]

/-- At the center, the surprisal operator is `(ln 2)·I`. -/
theorem centerState_surprisal_operator :
    surprisalOperator centerState = (Real.log 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hlog : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centerState, surprisalOperator, Matrix.smul_apply]
  all_goals
    convert hlog using 1 <;> norm_num

/-- The center state is self-complementary. -/
theorem centerState_self_complement : centerState.complement = centerState := by
  congr 1 <;> norm_num [centerState, SimplexState.complement]

/-! ## 4. Cayley inversion and critical line -/

/-- The Cayley fugacity of the complement is the inverse fugacity. -/
theorem cayley_fugacity_complement (S : SimplexState) :
    cayleyToFugacity (1 - S.s) = 1 / cayleyToFugacity S.s := by
  simpa [one_div] using
    (cayleyToFugacity_one_sub_eq_inv (S.s : ℂ))

/-- The relative surprisal changes sign under complement. -/
theorem W_complement_eq_neg (S : SimplexState) :
    S.complement.W = -S.W := by
  exact S.W_complement

/-- The critical line `Re(s) = 1/2` corresponds to `|τ| = 1`
    (zero real relative surprisal). -/
theorem criticalLine_iff_unit_circle (s : ℂ) :
    OnCriticalLine s ↔ OnLeeYangCircle (cayleyToFugacity s) :=
  criticalLine_iff_cayley_unitCircle s

/-! ## 5. Twin thermal flow and standing wave -/

/-- Twin thermal flow data: envelope `Φ` and frequency `t`. -/
structure TwinThermalFlow where
  Φ : ℝ → ℝ
  t : ℝ

namespace TwinThermalFlow

variable (TF : TwinThermalFlow)

/-- Left-decaying thermal flow from `W = -∞`. -/
def psi_left (y : ℝ) : ℂ :=
  (TF.Φ y : ℂ) * Complex.exp (-Complex.I * (TF.t : ℂ) * (y : ℂ))

/-- Right-growing thermal flow from `W = +∞`. -/
def psi_right (y : ℝ) : ℂ :=
  (TF.Φ y : ℂ) * Complex.exp (Complex.I * (TF.t : ℂ) * (y : ℂ))

/-- Total superposition of the twin thermal flows. -/
def psi_total (y : ℝ) : ℂ :=
  TF.psi_left y + TF.psi_right y

/-- The total superposition is a real standing wave `2 Φ(y) cos(ty)`. -/
theorem psi_total_cosine (y : ℝ) :
    TF.psi_total y = 2 * (TF.Φ y : ℂ) * Complex.cos ((TF.t : ℂ) * (y : ℂ)) := by
  simp [psi_total, psi_left, psi_right, Complex.ext_iff, Complex.exp_re, Complex.exp_im,
    Complex.cos, Complex.sin, mul_comm]
  <;> ring_nf
  <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin,
      mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin]
  <;> ring_nf
  <;> simp_all [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin]
  <;> norm_num
  <;> linarith
  <;>
  (try
    {
      constructor <;>
      simp_all [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin,
        mul_comm, mul_assoc, mul_left_comm] <;>
      ring_nf at * <;>
      field_simp [Real.cos_add, Real.sin_add] at * <;>
      ring_nf at * <;>
      nlinarith [Real.cos_le_one (TF.t * y), Real.cos_le_one (-TF.t * y)]
    })

end TwinThermalFlow

/-! ## 6. Bregman midpoint reflection -/

/-- The Bregman divergence at the midpoint `1/2` reduces to the potential difference
    when the derivative vanishes at the midpoint by reflection symmetry. -/
theorem bregman_midpoint_reflection (Φ : ℝ → ℝ)
    (hΦ : ConvexOn ℝ (Set.univ : Set ℝ) Φ)
    (hderiv : HasDerivAt Φ 0 (1 / 2 : ℝ)) (β : ℝ) :
    InfoGeometry.bregmanDiv Φ β (1 / 2 : ℝ) = Φ β - Φ (1 / 2 : ℝ) := by
  have h₁ : InfoGeometry.bregmanDiv Φ β (1 / 2 : ℝ) = Φ β - Φ (1 / 2 : ℝ) - deriv Φ (1 / 2 : ℝ) * (β - 1 / 2 : ℝ) := by
    rw [InfoGeometry.bregmanDiv]
    <;> simp [hderiv]
    <;> ring_nf
  rw [h₁]
  have h₂ : deriv Φ (1 / 2 : ℝ) = 0 := by
    apply HasDerivAt.deriv
    exact hderiv
  rw [h₂]
  <;> ring_nf
  <;> simp [sub_mul, mul_sub]
  <;> linarith

end noncomputable section
