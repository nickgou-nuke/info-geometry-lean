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
  /-- The Cartan generator, stored as a unit so its inverse is native. -/
  K : Rˣ
  comm_KE : (K : R) * E * (↑(K⁻¹) : R) = (q ^ 2) • E
  comm_KF : (K : R) * F * (↑(K⁻¹) : R) = (q ^ (-2 : ℤ)) • F
  comm_EF : E * F - F * E =
    ((q - q⁻¹)⁻¹) • ((K : R) - (↑(K⁻¹) : R))

variable {q : ℂ} {R : Type*} [Ring R] [Algebra ℂ R] (sys : QuantumGroupUqSL2System q R)

/-- **Theorem**: Quantum Group U_q(sl₂) Fundamental Commutator [E, F]:
    E F - F E = (K - K⁻¹) / (q - q⁻¹). -/
theorem uq_sl2_ef_commutator_eq :
    sys.E * sys.F - sys.F * sys.E =
      ((q - q⁻¹)⁻¹) • ((sys.K : R) - (↑(sys.K⁻¹) : R)) :=
  sys.comm_EF

/-- **Theorem**: Quantum Group U_q(sl₂) K-Action on E:
    K E = q² E K. -/
theorem uq_sl2_ke_comm_eq :
    (sys.K : R) * sys.E = (q ^ 2) • (sys.E * (sys.K : R)) := by
  have h := sys.comm_KE
  calc (sys.K : R) * sys.E
    _ = (sys.K : R) * sys.E * 1 := by rw [mul_one]
    _ = (sys.K : R) * sys.E * ((↑(sys.K⁻¹) : R) * (sys.K : R)) := by
      simp
    _ = ((sys.K : R) * sys.E * (↑(sys.K⁻¹) : R)) * (sys.K : R) := by
      simp only [mul_assoc]
    _ = ((q ^ 2) • sys.E) * (sys.K : R) := by rw [h]
    _ = (q ^ 2) • (sys.E * (sys.K : R)) := by rw [smul_mul_assoc]

/-- **Theorem**: Quantum Group U_q(sl₂) K-Action on F:
    K F = q⁻² F K. -/
theorem uq_sl2_kf_comm_eq :
    (sys.K : R) * sys.F =
      (q ^ (-2 : ℤ)) • (sys.F * (sys.K : R)) := by
  have h := sys.comm_KF
  calc (sys.K : R) * sys.F
    _ = (sys.K : R) * sys.F * 1 := by rw [mul_one]
    _ = (sys.K : R) * sys.F * ((↑(sys.K⁻¹) : R) * (sys.K : R)) := by
      simp
    _ = ((sys.K : R) * sys.F * (↑(sys.K⁻¹) : R)) * (sys.K : R) := by
      simp only [mul_assoc]
    _ = ((q ^ (-2 : ℤ)) • sys.F) * (sys.K : R) := by rw [h]
    _ = (q ^ (-2 : ℤ)) • (sys.F * (sys.K : R)) := by rw [smul_mul_assoc]

end QuantumGroupUqSL2Bridge
