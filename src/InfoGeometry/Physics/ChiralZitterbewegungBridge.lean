import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

open Matrix

namespace InfoGeometry.Physics.Zitterbewegung

/-!
# Two-Sector Chiral Hamiltonian and Coherent Oscillation Identities

This module formalizes a two-level Hamiltonian and its Rabi transition law:
1. **The Universal 2-Level Off-Diagonal Hamiltonian**:
   $\mathcal{H}_{\text{chiral}} = \begin{pmatrix} E_0 & \Delta \\ \Delta & E_0 \end{pmatrix}$,
   representing:
   - Dirac electron at rest ($E_0 = 0, \Delta = m c^2$),
   - Triaxial chiral nucleus ($E_0 = E_{\text{rot}}, \Delta = \text{tunneling matrix element}$),
   - Ammonia maser inversion ($E_0 = E_{\text{vib}}, \Delta = \text{inversion tunneling}$).
2. **Secular Energy Roots & Characteristic Determinant**:
   $\det(\mathcal{H} - E I_2) = (E - (E_0 - \Delta))(E - (E_0 + \Delta))$.
3. **Two-sector energy gap**:
   $\Delta E = E_+ - E_- = (E_0 + \Delta) - (E_0 - \Delta) = 2\Delta$.
4. **Coherent two-level transition probability**:
   $P_{L \to R}(t) = \sin^2(\Delta t)$, with maximum transition at $t = \frac{\pi}{2\Delta}$.

This two-level calculation is a Rabi-type model. It is a Zitterbewegung model
only when its states and observables are identified with the positive- and
negative-energy sectors of the Dirac equation. A generic chiral nucleus or
ammonia inversion system is not thereby Dirac Zitterbewegung.
-/

/-! ### 1. The Two-Sector Off-Diagonal Chiral Hamiltonian -/

/-- The Universal 2-Level Chiral/Commutant Hamiltonian: $\mathcal{H} = \begin{pmatrix} E_0 & \Delta \\ \Delta & E_0 \end{pmatrix}$. -/
def universalChiralHamiltonian (E0 Delta : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![E0, Delta; Delta, E0]

/-- **THE SECULAR ROOTS THEOREM**:
    $\det(\mathcal{H} - E I_2) = (E - (E_0 - \Delta))(E - (E_0 + \Delta))$. -/
theorem chiral_secular_roots (E0 Delta E : ℝ) :
    det (universalChiralHamiltonian E0 Delta -
      E • (1 : InfoGeometry.Algebra.FiniteSpin.Mat2R)) =
    (E - (E0 - Delta)) * (E - (E0 + Delta)) := by
  dsimp [universalChiralHamiltonian]
  simp [det_fin_two]
  ring

/-- The two-sector energy gap between the symmetric and anti-symmetric modes
is twice the off-diagonal coupling. This is a generic two-level identity; it
does not identify these modes with Dirac positive- and negative-energy sectors. -/
theorem universal_two_sector_energy_gap (E0 Delta : ℝ) :
    let E_plus := E0 + Delta
    let E_minus := E0 - Delta
    E_plus - E_minus = 2 * Delta := by
  dsimp
  ring

/-! ### 2. The Two-Level Rabi Time-Evolution -/

/-- The two-level transition probability: $P_{L \to R}(t) = \sin^2(\Delta t)$. -/
def transitionProbLR (Delta t : ℝ) : ℝ :=
  (Real.sin (Delta * t)) ^ 2

/-- **THE MAXIMAL TRANSITION QUARTER-PERIOD THEOREM**:
    At $t = \frac{\pi}{2\Delta}$, the transition probability to the commutant reaches strictly 1. -/
theorem transition_prob_max_at_quarter_period (Delta : ℝ) (hD : Delta ≠ 0) :
    let t_half := Real.pi / (2 * Delta)
    transitionProbLR Delta t_half = 1 := by
  dsimp [transitionProbLR]
  have h_arg : Delta * (Real.pi / (2 * Delta)) = Real.pi / 2 := by
    calc
      Delta * (Real.pi / (2 * Delta)) = (Delta / Delta) * (Real.pi / 2) := by ring
      _ = 1 * (Real.pi / 2) := by rw [div_self hD]
      _ = Real.pi / 2 := by ring
  rw [h_arg, Real.sin_pi_div_two]
  ring

/-- Averaged transition probability for the two-level Rabi model over one
probability period. For positive coupling, `sin²(Δ t)` has period `π/Δ` and
its exact interval average is `1/2`. This is a statement about this model's
transition probability, not an assertion about a physical Zitterbewegung
trajectory or a detector signal. -/
theorem transitionProbLR_average_one_period (Delta : ℝ) (hD : 0 < Delta) :
    (Delta / Real.pi) *
        (∫ t in (0 : ℝ)..(Real.pi / Delta), transitionProbLR Delta t) =
      1 / 2 := by
  have hD0 : Delta ≠ 0 := ne_of_gt hD
  have hscaled :
      Delta * (∫ t in (0 : ℝ)..(Real.pi / Delta),
          Real.sin (Delta * t) ^ 2) = Real.pi / 2 := by
    calc
      Delta * (∫ t in (0 : ℝ)..(Real.pi / Delta),
          Real.sin (Delta * t) ^ 2) =
          ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2 := by
            rw [intervalIntegral.mul_integral_comp_mul_left
              (f := fun x : ℝ => Real.sin x ^ 2)]
            have harg : Delta * (Real.pi / Delta) = Real.pi := by
              field_simp [hD0]
            rw [mul_zero, harg]
      _ = Real.pi / 2 := by simp [integral_sin_sq]
  change (Delta / Real.pi) *
      (∫ t in (0 : ℝ)..(Real.pi / Delta), Real.sin (Delta * t) ^ 2) = 1 / 2
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    (Delta / Real.pi) *
        (∫ t in (0 : ℝ)..(Real.pi / Delta), Real.sin (Delta * t) ^ 2) =
        (Delta / Real.pi) * (Real.pi / (2 * Delta)) := by
          congr 1
          field_simp [hD0] at hscaled ⊢
          nlinarith
    _ = 1 / 2 := by
      field_simp [hD0, hpi]


end InfoGeometry.Physics.Zitterbewegung
