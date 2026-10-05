import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rest-energy gap, Compton frequency, and an algebraic velocity ratio

This module records scalar formulas associated with the Dirac rest-energy gap.
It does not derive mass generation from Zitterbewegung, derive the dispersion
relation from a Zorn BdG operator, or establish a macroscopic dynamical drag law.

1. **Relativistic Dispersion Relation:**
   $E^2 = p^2 c^2 + m^2 c^4$, represented here by a scalar expression.
2. **Rest-Energy Mass Gap:**
   $\Delta E = E_+ - E_- = mc^2 - (-mc^2) = 2mc^2$.
3. **Compton Zitterbewegung Angular Frequency:**
   $\omega_Z = \frac{\Delta E}{\hbar} = \frac{2mc^2}{\hbar}$.
4. **Macroscopic Subluminal Deceleration:**
   The effective velocity ratio squared is:
   $$\left(\frac{v}{c}\right)^2 = \frac{p^2}{p^2 + m^2 c^2}$$
   For any non-zero mass $m \neq 0$ and speed of light $c \neq 0$, $(v/c)^2 < 1$,
   an algebraic property of the defined ratio, not a derived propagation law.
5. **Massless Luminal Limit:**
   When $m = 0$ (and $p \neq 0$), $(v/c)^2 = 1$, restoring lightcone propagation.
-/

namespace InfoGeometry.Canonical.ZitterbewegungMassEmergence

noncomputable section

/-- Relativistic mass-energy dispersion relation: E² = p²c² + m²c⁴. -/
def dispersionE2 (p m c : ℝ) : ℝ :=
  p ^ 2 * c ^ 2 + m ^ 2 * c ^ 4

/-- The rest energy gap between positive and negative energy states: ΔE = 2mc². -/
def restEnergyGap (m c : ℝ) : ℝ :=
  2 * m * c ^ 2

/-- Evaluation of the rest energy gap: mc² - (-mc²) = 2mc². -/
theorem restEnergyGap_eval (m c : ℝ) :
    (m * c ^ 2) - (- (m * c ^ 2)) = restEnergyGap m c := by
  simp [restEnergyGap]
  ring

/-- The Compton Zitterbewegung angular frequency: ω_Z = 2mc² / ħ. -/
def comptonFrequency (m c hbar : ℝ) : ℝ :=
  restEnergyGap m c / hbar

/-- Explicit expression for the Compton angular frequency. -/
theorem comptonFrequency_eq (m c hbar : ℝ) :
    comptonFrequency m c hbar = 2 * m * c ^ 2 / hbar := rfl

/-- Macroscopic velocity ratio squared: (v/c)² = p² / (p² + m²c²). -/
def velocityRatioSq (p m c : ℝ) : ℝ :=
  p ^ 2 / (p ^ 2 + m ^ 2 * c ^ 2)

/-- For nonzero m and c, the defined algebraic velocity ratio is strictly less than 1. -/
theorem velocity_strictly_subluminal (p m c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    velocityRatioSq p m c < 1 := by
  dsimp [velocityRatioSq]
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have h_denom_pos : 0 < p ^ 2 + m ^ 2 * c ^ 2 := by
    have h_prod : 0 < m ^ 2 * c ^ 2 := mul_pos hm2 hc2
    have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
    linarith
  rw [div_lt_iff₀ h_denom_pos]
  have h_prod : 0 < m ^ 2 * c ^ 2 := mul_pos hm2 hc2
  linarith

/-- In the massless limit m = 0 (with p ≠ 0), propagation is at the speed of light:
    (v/c)² = 1. -/
theorem velocity_massless_luminal (p c : ℝ) (hp : p ≠ 0) :
    velocityRatioSq p 0 c = 1 := by
  dsimp [velocityRatioSq]
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  simp [hp2]

end

end InfoGeometry.Canonical.ZitterbewegungMassEmergence
