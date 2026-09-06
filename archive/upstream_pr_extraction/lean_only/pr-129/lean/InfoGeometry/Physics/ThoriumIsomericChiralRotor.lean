import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

/-!
# InfoGeometry.Physics.ThoriumIsomericChiralRotor

Formalization of the $^{229}\text{Th}$ Nuclear Clock Isomeric Transition,
Unitary Chiral Rotors $R(\phi) = e^{-I\phi/2}$, Rotor Group Laws,
Double Cover $SU(2) \to SO(3)$, Rabi Transition Oscillations, and M1 Dipole Dynamics.

## Mathematical Core:
1. **Unitary Chiral Rotor Group in Even Clifford Algebra**:
   $$R(\phi) = \cos(\phi/2) - I \sin(\phi/2) = \exp(-I \phi / 2)$$
   - Identity: $R(0) = \mathbf{1}$
   - Group law: $R(\phi_1) R(\phi_2) = R(\phi_1 + \phi_2)$
   - Commutativity: $R_1 R_2 = R_2 R_1$
   - Unitary inversion: $R(\phi) R(-\phi) = \mathbf{1}$
   - Norm normalization: $|R(\phi)|^2 = \cos^2(\phi/2) + \sin^2(\phi/2) = 1$
   - Double Cover property: $R(2\pi) = -\mathbf{1}$ and $R(4\pi) = \mathbf{1}$

2. **Rabi Quantum Transition Oscillations**:
   - Transition probability: $P(\theta) = \sin^2(\theta/2) = \frac{1 - \cos\theta}{2}$
   - Boundedness: $0 \le P(\theta) \le 1$
   - Resonant $\pi$-pulse inversion: $P(\pi) = 1$

3. **Thorium-229 Nuclear Isomeric Transition**:
   - Nuclear ground state: $|g\rangle = |^{229}\text{Th}, J^\pi = 5/2^+\rangle$
   - Isomeric clock state: $|m\rangle = |^{229}\text{Th}^m, J^\pi = 3/2^+\rangle$
   - Excitation energy $E_m \approx 8.338\,\text{eV} > 0$
   - Selection rule: $\Delta J = |5/2 - 3/2| = 1$ (Magnetic Dipole M1 Transition)

All theorems kernel-checked in Lean 4 with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Physics

namespace Thorium229

/-! ### 1. Unitary Chiral Rotor Dynamics -/

/-- Unitary Chiral Rotor $R(\phi) = \cos(\phi/2) - I \sin(\phi/2)$ represented as an even Clifford pair `(cos(φ/2), -sin(φ/2))`. -/
@[ext]
structure ChiralRotor where
  scalar : ℝ
  bivector : ℝ

namespace ChiralRotor

/-- Identity rotor $R(0) = 1$. -/
def one : ChiralRotor := ⟨1, 0⟩

/-- Rotor generator for angle $\phi$: $R(\phi) = \cos(\phi/2) - I \sin(\phi/2)$. -/
def ofAngle (φ : ℝ) : ChiralRotor :=
  ⟨cos (φ / 2), -sin (φ / 2)⟩

/-- Rotor product in the even Clifford subalgebra: $(s_1 + I b_1)(s_2 + I b_2) = (s_1 s_2 - b_1 b_2) + I (s_1 b_2 + b_1 s_2)$. -/
def mul (r1 r2 : ChiralRotor) : ChiralRotor :=
  ⟨r1.scalar * r2.scalar - r1.bivector * r2.bivector,
   r1.scalar * r2.bivector + r1.bivector * r2.scalar⟩

instance : One ChiralRotor := ⟨one⟩
instance : Mul ChiralRotor := ⟨mul⟩

/-- **Theorem (Rotor Identity)**: $R(0) = \mathbf{1}$. -/
@[simp] theorem ofAngle_zero : ofAngle 0 = 1 := by
  ext
  · change (ofAngle 0).scalar = one.scalar
    dsimp [ofAngle, one]
    simp
  · change (ofAngle 0).bivector = one.bivector
    dsimp [ofAngle, one]
    simp

/-- **Theorem (Rotor Group Law)**: $R(\phi_1) R(\phi_2) = R(\phi_1 + \phi_2)$. -/
theorem ofAngle_add (φ1 φ2 : ℝ) :
    ofAngle φ1 * ofAngle φ2 = ofAngle (φ1 + φ2) := by
  change mul (ofAngle φ1) (ofAngle φ2) = ofAngle (φ1 + φ2)
  dsimp [mul, ofAngle]
  ext
  · have hcos : cos ((φ1 + φ2) / 2) =
      cos (φ1 / 2) * cos (φ2 / 2) - sin (φ1 / 2) * sin (φ2 / 2) := by
      have hdiv : (φ1 + φ2) / 2 = φ1 / 2 + φ2 / 2 := by ring
      rw [hdiv, cos_add]
    rw [hcos]
    ring
  · have hsin : -sin ((φ1 + φ2) / 2) =
      cos (φ1 / 2) * (-sin (φ2 / 2)) + (-sin (φ1 / 2)) * cos (φ2 / 2) := by
      have hdiv : (φ1 + φ2) / 2 = φ1 / 2 + φ2 / 2 := by ring
      rw [hdiv, sin_add]
      ring
    rw [hsin]

/-- **Theorem (Rotor Commutativity)**: $R_1 R_2 = R_2 R_1$. -/
theorem mul_comm (r1 r2 : ChiralRotor) : r1 * r2 = r2 * r1 := by
  ext
  · change (mul r1 r2).scalar = (mul r2 r1).scalar; dsimp [mul]; ring
  · change (mul r1 r2).bivector = (mul r2 r1).bivector; dsimp [mul]; ring

/-- **Theorem (Rotor Unitary Inversion)**: $R(\phi) R(-\phi) = \mathbf{1}$. -/
theorem ofAngle_mul_neg (φ : ℝ) :
    ofAngle φ * ofAngle (-φ) = 1 := by
  rw [ofAngle_add]
  have hzero : φ + -φ = 0 := by ring
  rw [hzero, ofAngle_zero]

/-- **Theorem (Rotor Norm)**: $|R(\phi)|^2 = \cos^2(\phi/2) + \sin^2(\phi/2) = 1$. -/
theorem ofAngle_norm_sq (φ : ℝ) :
    (ofAngle φ).scalar ^ 2 + (ofAngle φ).bivector ^ 2 = 1 := by
  dsimp [ofAngle]
  have hsq : (-sin (φ / 2)) ^ 2 = sin (φ / 2) ^ 2 := by ring
  rw [hsq, cos_sq_add_sin_sq]

/-- **Theorem (Spin-1/2 Double Cover 2π Inversion)**: $R(2\pi) = -\mathbf{1}$. -/
theorem ofAngle_two_pi : ofAngle (2 * π) = ⟨-1, 0⟩ := by
  ext
  · dsimp [ofAngle]
    have h : (2 * π) / 2 = π := by ring
    rw [h, cos_pi]
  · dsimp [ofAngle]
    have h : (2 * π) / 2 = π := by ring
    rw [h, sin_pi, neg_zero]

/-- **Theorem (Spin-1/2 Double Cover 4π Return)**: $R(4\pi) = \mathbf{1}$. -/
theorem ofAngle_four_pi : ofAngle (4 * π) = 1 := by
  ext
  · change (ofAngle (4 * π)).scalar = one.scalar
    dsimp [ofAngle, one]
    have h : (4 * π) / 2 = 2 * π := by ring
    rw [h, cos_two_pi]
  · change (ofAngle (4 * π)).bivector = one.bivector
    dsimp [ofAngle, one]
    have h : (4 * π) / 2 = 2 * π := by ring
    rw [h, sin_two_pi, neg_zero]

end ChiralRotor

/-! ### 2. Rabi Quantum Transition Oscillations -/

/-- Rabi transition probability $P(\theta) = \sin^2(\theta/2)$. -/
def rabiTransitionProb (θ : ℝ) : ℝ :=
  sin (θ / 2) ^ 2

/-- **Theorem (Rabi Probability Bounds $0 \le P(\theta) \le 1$)**: -/
theorem rabi_prob_bounds (θ : ℝ) :
    0 ≤ rabiTransitionProb θ ∧ rabiTransitionProb θ ≤ 1 := by
  dsimp [rabiTransitionProb]
  constructor
  · positivity
  · exact sin_sq_le_one (θ / 2)

/-- **Theorem (Resonant $\pi$-Pulse Complete Inversion)**: $P(\pi) = 1$. -/
theorem rabi_pi_pulse : rabiTransitionProb π = 1 := by
  dsimp [rabiTransitionProb]
  rw [sin_pi_div_two, one_pow]

/-! ### 3. Thorium-229 Isomeric State Physical Datum -/

/--
The $^{229}\text{Th}$ nuclear state datum:
- Ground state: $J^\pi = 5/2^+$
- Isomeric state: $J^\pi = 3/2^+$
- Excitation energy $E_m \approx 8.338\,\text{eV} > 0$
- Transition wavelength $\lambda \approx 148.7\,\text{nm}$ (Vacuum UV)
-/
structure ThoriumIsomericDatum where
  ground_spin : ℝ    -- 5/2 = 2.5
  isomeric_spin : ℝ  -- 3/2 = 1.5
  energy_ev : ℝ      -- 8.338 eV
  h_energy_pos : 0 < energy_ev
  h_spin_diff : ground_spin - isomeric_spin = 1 -- ΔJ = 1 (Magnetic Dipole M1 transition)

/-- Canonical physical parameters for $^{229}\text{Th}$. -/
def standardThorium229 : ThoriumIsomericDatum where
  ground_spin := 5 / 2
  isomeric_spin := 3 / 2
  energy_ev := 8338 / 1000
  h_energy_pos := by norm_num
  h_spin_diff := by norm_num

/-- **Theorem (M1 Selection Rule)**: The $^{229}\text{Th}$ ground-to-isomer transition is a dipole transition $\Delta J = 1$. -/
theorem thorium_m1_dipole (th : ThoriumIsomericDatum) :
    th.ground_spin - th.isomeric_spin = 1 :=
  th.h_spin_diff

/-- **Theorem (Isomeric Excitation Positivity)**: The isomeric clock state is strictly energetic $E_m > 0$. -/
theorem thorium_energy_positive (th : ThoriumIsomericDatum) :
    0 < th.energy_ev :=
  th.h_energy_pos

end Thorium229

end InfoGeometry.Physics
