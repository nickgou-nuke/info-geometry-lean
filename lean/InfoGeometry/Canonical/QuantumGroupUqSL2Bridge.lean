import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

namespace QuantumGroupUqSL2Bridge

/-- Quantum Group U_q(sl₂) Generator System in an Algebra R over ℂ. -/
structure QuantumGroupUqSL2System (q : ℂ) (R : Type*) [Ring R] [Algebra ℂ R] where
  E : R
  F : R
  K : R
  K_inv : R
  left_inv : K_inv * K = 1
  right_inv : K * K_inv = 1
  comm_KE : K * E * K_inv = (q ^ 2) • E
  comm_KF : K * F * K_inv = (q ^ (-2 : ℤ)) • F
  comm_EF : E * F - F * E = ((q - q⁻¹)⁻¹) • (K - K_inv)

variable {q : ℂ} {R : Type*} [Ring R] [Algebra ℂ R] (sys : QuantumGroupUqSL2System q R)

/-- **Theorem**: Quantum Group U_q(sl₂) Fundamental Commutator [E, F]:
    E F - F E = (K - K⁻¹) / (q - q⁻¹). -/
theorem uq_sl2_ef_commutator_eq :
    sys.E * sys.F - sys.F * sys.E = ((q - q⁻¹)⁻¹) • (sys.K - sys.K_inv) :=
  sys.comm_EF

/-- **Theorem**: Quantum Group U_q(sl₂) K-Action on E:
    K E = q² E K. -/
theorem uq_sl2_ke_comm_eq :
    sys.K * sys.E = (q ^ 2) • (sys.E * sys.K) := by
  have h := sys.comm_KE
  calc sys.K * sys.E
    _ = sys.K * sys.E * 1 := by rw [mul_one]
    _ = sys.K * sys.E * (sys.K_inv * sys.K) := by rw [sys.left_inv]
    _ = (sys.K * sys.E * sys.K_inv) * sys.K := by rw [← mul_assoc]
    _ = ((q ^ 2) • sys.E) * sys.K := by rw [h]
    _ = (q ^ 2) • (sys.E * sys.K) := by rw [smul_mul_assoc]

/-- **Theorem**: Quantum Group U_q(sl₂) K-Action on F:
    K F = q⁻² F K. -/
theorem uq_sl2_kf_comm_eq :
    sys.K * sys.F = (q ^ (-2 : ℤ)) • (sys.F * sys.K) := by
  have h := sys.comm_KF
  calc sys.K * sys.F
    _ = sys.K * sys.F * 1 := by rw [mul_one]
    _ = sys.K * sys.F * (sys.K_inv * sys.K) := by rw [sys.left_inv]
    _ = (sys.K * sys.F * sys.K_inv) * sys.K := by rw [← mul_assoc]
    _ = ((q ^ (-2 : ℤ)) • sys.F) * sys.K := by rw [h]
    _ = (q ^ (-2 : ℤ)) • (sys.F * sys.K) := by rw [smul_mul_assoc]

end QuantumGroupUqSL2Bridge
