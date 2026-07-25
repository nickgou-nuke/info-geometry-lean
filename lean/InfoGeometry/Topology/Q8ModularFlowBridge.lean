import Mathlib.Tactic
import InfoGeometry.Topology.Q8MonodromySpinorCover

/-!
# Q8ModularFlowBridge

Formalizes the connection between the continuous modular automorphism group
σ_t of the KMS state and the discrete quaternion group Q_8. Proves that
the discrete spinor generators are the valuations of the continuous flow at
discrete thermodynamic steps.
-/

namespace InfoGeometry.Topology.Q8ModularFlowBridge

open Matrix Complex
open InfoGeometryCore
open InfoGeometry.Topology.Q8MonodromySpinorCover

/-- 
The continuous unitary evolution evaluated at time t.
$U(t) = \cos(\pi t / 2) I - i \sin(\pi t / 2) \sigma_z$
-/
noncomputable def U (t : ℝ) : M2C :=
  let c : ℂ := Real.cos (Real.pi * t / 2)
  let s : ℂ := Real.sin (Real.pi * t / 2)
  !![c - I * s, 0; 0, c + I * s]

/-- 
The discrete step is evaluated at t = 1.
-/
noncomputable def U_discrete : M2C := U 1

/--
The discrete unitary at t=1 is precisely the negative of the Q8 generator `M_i`.
-/
theorem U_discrete_eq_neg_M_i : U_discrete = -M_i := by
  dsimp [U_discrete, U, M_i]
  ext i j
  have h_cos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have h_sin : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  fin_cases i <;> fin_cases j <;> simp [h_cos, h_sin]

/--
Therefore, its square is -I, establishing it as a spinor generator.
-/
theorem U_discrete_sq : U_discrete * U_discrete = -1 := by
  rw [U_discrete_eq_neg_M_i]
  have h : -M_i * -M_i = M_i * M_i := neg_mul_neg M_i M_i
  rw [h, M_i_sq]

/--
The modular flow action on an observable `x` at time `t` is conjugation by `U(t)`.
-/
noncomputable def modular_flow (t : ℝ) (x : M2C) : M2C :=
  U t * x * star (U t)

/--
The modular step at t=1 conjugates exactly via the spinor generator `M_i`.
-/
theorem modular_step_is_spinor_generator (x : M2C) :
    modular_flow 1 x = M_i * x * star M_i := by
  change U_discrete * x * star U_discrete = M_i * x * star M_i
  rw [U_discrete_eq_neg_M_i]
  have h_star : star (-M_i) = -(star M_i) := star_neg M_i
  rw [h_star]
  -- (-M_i) * x * (-star M_i) = M_i * x * star M_i
  calc
    (-M_i) * x * -(star M_i) = - (M_i * x) * -(star M_i) := by simp [neg_mul]
    _ = M_i * x * star M_i := by rw [neg_mul_neg]

end InfoGeometry.Topology.Q8ModularFlowBridge
