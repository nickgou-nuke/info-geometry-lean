import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Physics.ThoriumHyperfineQEDSpacetimeBridge

Formalization of $^{229}\text{Th}$ Nuclear Hyperfine Multiplet Structure,
Electric Quadrupole Interactions ($E2$), Reduced Radiative Decay Rates $B(M1)/B(E2)$,
and Spacetime QED Radiative Corrections (Schwinger $g-2$).

## Mathematical Core:
1. **QED Radiative Corrections in Spacetime Algebra**:
   - Fine structure constant: $\alpha \approx 1/137.036$.
   - Schwinger anomalous magnetic moment: $a_e = \frac{\alpha}{2\pi} + \mathcal{O}(\alpha^2)$.
   - Strict positivity and empirical bounds: $0 < a_e < 0.0012$.

2. **Hyperfine Casimir Multiplet Decomposition in $^{229}\text{Th}$**:
   - Total angular momentum coupling $\mathbf{F} = \mathbf{J} + \mathbf{I}$.
   - Casimir coupling scalar: $K = F(F+1) - I(I+1) - J(J+1)$.
   - Magnetic dipole shift: $\Delta E_{M1} = \frac{1}{2} A K$.
   - Electric quadrupole shift: $\Delta E_{E2} = B \frac{\frac{3}{2}K(K+1) - 2 I(I+1) J(J+1)}{4 I(2I-1) J(2J-1)}$.
   - Total hyperfine shift: $\Delta E_{\text{HFS}} = \Delta E_{M1} + \Delta E_{E2}$.

3. **Reduced Transition Probabilities & Radiative Lifetime**:
   - Magnetic dipole rate: $\Gamma_{M1} = c_1 \omega^3 B(M1)$.
   - Electric quadrupole rate: $\Gamma_{E2} = c_2 \omega^5 B(E2)$.
   - Total decay width: $\Gamma_{\text{total}} = \Gamma_{M1} + \Gamma_{E2} > 0$.
   - Radiative lifetime: $\tau = 1 / \Gamma_{\text{total}} > 0$.

All theorems kernel-checked in Lean 4 with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Physics

namespace ThoriumHyperfineQED

/-! ### 1. Spacetime QED Radiative Corrections -/

/-- Fine structure constant $\alpha \approx 1/137.035999$. -/
def alpha_QED : ℝ := 1 / 137.035999

/-- Schwinger first-order radiative correction $(g - 2)/2 = \alpha / (2\pi)$. -/
def schwinger_correction (pi_approx : ℝ) : ℝ :=
  alpha_QED / (2 * pi_approx)

/-- **Theorem (Schwinger Correction Positivity & Bound)**:
    For $\pi \in [3.14, 3.15]$, $0 < a_e < 0.0012$. -/
theorem schwinger_correction_bounds (pi_val : ℝ)
    (h_pi_low : 3.14 ≤ pi_val) (_h_pi_high : pi_val ≤ 3.15) :
    0 < schwinger_correction pi_val ∧ schwinger_correction pi_val < 0.0012 := by
  dsimp [schwinger_correction, alpha_QED]
  constructor
  · have h1 : 0 < (1 : ℝ) / 137.035999 := by norm_num
    have h2 : 0 < 2 * pi_val := by linarith
    exact div_pos h1 h2
  · have h_pi : (2 * 3.14 : ℝ) ≤ 2 * pi_val := by linarith
    have h_pos : 0 < (2 * 3.14 : ℝ) := by norm_num
    have h_div : (1 / 137.035999) / (2 * pi_val) ≤ (1 / 137.035999) / (2 * 3.14) :=
      div_le_div_of_nonneg_left (by norm_num) h_pos h_pi
    have h_const : (1 / 137.035999) / (2 * 3.14 : ℝ) < (0.0012 : ℝ) := by norm_num
    exact lt_of_le_of_lt h_div h_const

/-! ### 2. Hyperfine Multiplet Structure in ²²⁹Th -/

/-- Nuclear Hyperfine State Parameters:
    - $J$: Electronic/Nuclear total spin
    - $I$: Coupled nuclear/atomic spin
    - $F$: Total coupled angular momentum $F$
    - $A$: Magnetic dipole hyperfine constant (eV)
    - $B$: Electric quadrupole hyperfine constant (eV)
-/
structure HyperfineState where
  J : ℝ
  I : ℝ
  F : ℝ
  A_const : ℝ
  B_const : ℝ
  h_J_pos : 0 < J
  h_I_pos : 0 < I
  h_F_nonneg : 0 ≤ F

/-- The Casimir coupling quantum number $K = F(F+1) - I(I+1) - J(J+1)$. -/
def casimir_K (H : HyperfineState) : ℝ :=
  H.F * (H.F + 1) - H.I * (H.I + 1) - H.J * (H.J + 1)

/-- Magnetic Dipole Hyperfine Energy Shift: $\Delta E_{M1} = \frac{1}{2} A K$. -/
def deltaE_M1 (H : HyperfineState) : ℝ :=
  (1 / 2) * H.A_const * casimir_K H

/-- Electric Quadrupole Factor:
    $$f_{E2}(K, I, J) = \frac{3}{2}K(K+1) - 2 I(I+1) J(J+1)$$
-/
def quad_numerator (H : HyperfineState) : ℝ :=
  (3 / 2) * (casimir_K H) * (casimir_K H + 1) - 2 * (H.I * (H.I + 1)) * (H.J * (H.J + 1))

/-- Electric Quadrupole Denominator:
    $$D_{E2}(I, J) = 4 I (2I - 1) J (2J - 1)$$
-/
def quad_denominator (H : HyperfineState) : ℝ :=
  4 * H.I * (2 * H.I - 1) * H.J * (2 * H.J - 1)

/-- Total Hyperfine Energy Shift: $\Delta E_{\text{HFS}} = \Delta E_{M1} + B \frac{f_{E2}}{D_{E2}}$. -/
def deltaE_HFS (H : HyperfineState) (_h_denom : quad_denominator H ≠ 0) : ℝ :=
  deltaE_M1 H + H.B_const * (quad_numerator H / quad_denominator H)

/-- **Theorem (Hyperfine Shift Decomposition)**:
    When $B = 0$ (pure dipole interaction), $\Delta E_{\text{HFS}} = \frac{1}{2} A K$.
-/
theorem hyperfine_pure_dipole (H : HyperfineState) (h_denom : quad_denominator H ≠ 0)
    (h_B_zero : H.B_const = 0) :
    deltaE_HFS H h_denom = (1 / 2) * H.A_const * casimir_K H := by
  dsimp [deltaE_HFS, deltaE_M1]
  rw [h_B_zero]
  ring

/-! ### 3. Reduced Radiative Transition Rates B(M1) and B(E2) -/

/-- Radiative Transition Rates Datum for ²²⁹Th:
    - $\omega$: transition frequency ($s^{-1}$)
    - $B_{M1}$: reduced magnetic dipole transition probability ($\mu_N^2$)
    - $B_{E2}$: reduced electric quadrupole transition probability ($e^2 \text{fm}^4$)
    - $c_1, c_2$: positive coupling constants
-/
structure RadiativeTransitionDatum where
  omega : ℝ
  B_M1 : ℝ
  B_E2 : ℝ
  c_M1 : ℝ
  c_E2 : ℝ
  h_omega_pos : 0 < omega
  h_BM1_pos : 0 < B_M1
  h_BE2_nonneg : 0 ≤ B_E2
  h_cM1_pos : 0 < c_M1
  h_cE2_pos : 0 < c_E2

/-- Partial M1 decay width: $\Gamma_{M1} = c_1 \omega^3 B(M1)$. -/
def gamma_M1 (D : RadiativeTransitionDatum) : ℝ :=
  D.c_M1 * D.omega ^ 3 * D.B_M1

/-- Partial E2 decay width: $\Gamma_{E2} = c_2 \omega^5 B(E2)$. -/
def gamma_E2 (D : RadiativeTransitionDatum) : ℝ :=
  D.c_E2 * D.omega ^ 5 * D.B_E2

/-- Total radiative decay width: $\Gamma_{\text{total}} = \Gamma_{M1} + \Gamma_{E2}$. -/
def gamma_total (D : RadiativeTransitionDatum) : ℝ :=
  gamma_M1 D + gamma_E2 D

/-- **Theorem (Total Radiative Width Strictly Positive)**:
    $\Gamma_{\text{total}} > 0$.
-/
theorem gamma_total_pos (D : RadiativeTransitionDatum) :
    0 < gamma_total D := by
  dsimp [gamma_total, gamma_M1, gamma_E2]
  have h_om : 0 < D.omega := D.h_omega_pos
  have h_om3 : 0 < D.omega ^ 3 := by positivity
  have h_om5 : 0 < D.omega ^ 5 := by positivity
  have h_M1 : 0 < D.c_M1 * D.omega ^ 3 * D.B_M1 := by
    have h1 := D.h_cM1_pos
    have h2 := D.h_BM1_pos
    exact mul_pos (mul_pos h1 h_om3) h2
  have h_E2 : 0 ≤ D.c_E2 * D.omega ^ 5 * D.B_E2 := by
    have h1 := le_of_lt D.h_cE2_pos
    have h2 := D.h_BE2_nonneg
    exact mul_nonneg (mul_nonneg h1 (le_of_lt h_om5)) h2
  linarith

/-- Radiative lifetime $\tau = 1 / \Gamma_{\text{total}}$. -/
def radiative_lifetime (D : RadiativeTransitionDatum) : ℝ :=
  1 / gamma_total D

/-- **Theorem (Radiative Lifetime Strictly Positive)**:
    $\tau > 0$.
-/
theorem radiative_lifetime_pos (D : RadiativeTransitionDatum) :
    0 < radiative_lifetime D := by
  dsimp [radiative_lifetime]
  have h := gamma_total_pos D
  exact one_div_pos.mpr h

end ThoriumHyperfineQED

end InfoGeometry.Physics
