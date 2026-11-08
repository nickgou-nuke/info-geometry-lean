import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Module.Basic

namespace InfoGeometry.Clifford.Cl11OscillationBridge

open Matrix

/--
The Cl(1,1) oscillation bridge generating the Bogoliubov-de Gennes (BdG)
coupling for particle-hole (neutrino) inversion.
We use the explicit 2×2 real matrix representation `Matrix (Fin 2) (Fin 2) ℝ`.
-/

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Timelike generator γ₀ = σ₃ (The Mass/Energy Grading) -/
def gamma_0 : M2R := !![1, 0; 0, -1]

/-- Spacelike generator γ₁ = iσ₂ (The Kinetic/Momentum Coupling) -/
def gamma_1 : M2R := !![0, 1; -1, 0]

/-- The BdG Inversion/Oscillation Operator Δ = σ₁ (Volume element γ₀γ₁) -/
def delta_bdg : M2R := !![0, 1; 1, 0]

/-- Identity matrix in M₂(ℝ) -/
def I_2 : M2R := 1

/-- The timelike generator squares to the identity. -/
theorem gamma_0_sq_eq_I : gamma_0 * gamma_0 = I_2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_0, gamma_1, delta_bdg, I_2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The spacelike generator squares to minus the identity. -/
theorem gamma_1_sq_eq_neg_I : gamma_1 * gamma_1 = -I_2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_0, gamma_1, delta_bdg, I_2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The split generators anticommute. -/
theorem gamma_0_gamma_1_anticommute : gamma_0 * gamma_1 + gamma_1 * gamma_0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_0, gamma_1, delta_bdg, I_2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product of the split generators is the BdG inversion operator. -/
theorem gamma_0_mul_gamma_1_eq_delta : gamma_0 * gamma_1 = delta_bdg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_0, gamma_1, delta_bdg, I_2, Matrix.mul_apply, Fin.sum_univ_two]

/-!
### Mapping to the Three Aeon Colimit

We define a neutrino state as a 2-component vector (particle and hole).
We map this state across the 3 Aeon colimit using the `delta_bdg` oscillation bridge.
-/

abbrev NeutrinoState := InfoGeometry.Algebra.FiniteSpin.Vec2R

/-- A purely Left-Handed unmixed neutrino state -/
def nu_L : NeutrinoState := ![1, 0]

/-- A purely Right-Handed unmixed anti-neutrino state -/
def nu_R : NeutrinoState := ![0, 1]

/-- The BdG coupling flips the distinguished left-handed state to the right-handed one. -/
theorem bdg_inverts_chirality :
    (delta_bdg *ᵥ nu_L) = nu_R := by
  ext i
  fin_cases i <;>
    norm_num [delta_bdg, nu_L, nu_R, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/--
The topological winding function mapping the neutrino state
across the three aeons (`aeonCount = 3`).
Each transition applies the BdG phase slip.
-/
def propagate_aeon (n : ℕ) (state : NeutrinoState) : NeutrinoState :=
  if n % 2 = 1 then delta_bdg *ᵥ state else state

theorem three_aeon_pmns_slip :
    propagate_aeon 3 nu_L = nu_R := by
  -- n = 3 is odd, so it applies the inversion.
  simp [propagate_aeon]
  exact bdg_inverts_chirality

end InfoGeometry.Clifford.Cl11OscillationBridge
