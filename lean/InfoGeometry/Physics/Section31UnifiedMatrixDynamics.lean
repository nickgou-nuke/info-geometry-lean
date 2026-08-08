import Mathlib.Tactic
import InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

/-!
# Section 31 repaired: finite unified-matrix dynamics layer

Section 31 substantially repeats the Pauli/Bloch/Minkowski matrix framework that
is already formalized in
`InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite`.  This file uses that
owner as a stepping stone and adds only the missing theorem-safe finite dynamics
socket:

* matrix commutator and Jacobi/curvature action identity;
* constant-connection covariant derivative `D_Γ X = [Γ,X]`;
* constant curvature `[Γ_μ,Γ_ν]` acting by commutator;
* flat zero connection gives zero curvature/action;
* constant gauge conjugation covariance under an explicitly supplied inverse.

No smooth gauge-bundle theorem, local `SU(2)` connection transformation law,
Einstein-equation derivation, gravity-from-entanglement theorem, or spacetime
emergence theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.Section31UnifiedMatrixDynamics

open Matrix Complex
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

/-- Matrix commutator `[A,B] = AB - BA` on the existing Pauli `2 × 2` carrier. -/
def commutator (A B : Mat2) : Mat2 :=
  A * B - B * A

/-- Constant-connection finite covariant derivative `D_Γ X = [Γ,X]`. -/
def covDerivConst (Γ X : Mat2) : Mat2 :=
  commutator Γ X

/-- Constant finite curvature `F(Γ,Λ) = [Γ,Λ]`. -/
def curvatureConst (Γ Λ : Mat2) : Mat2 :=
  commutator Γ Λ

/-- Jacobi form: commutator covariant derivatives act by curvature. -/
theorem covDerivConst_commutator_eq_curvature_action (Γ Λ X : Mat2) :
    covDerivConst Γ (covDerivConst Λ X) -
      covDerivConst Λ (covDerivConst Γ X) =
        commutator (curvatureConst Γ Λ) X := by
  ext i j
  simp [covDerivConst, curvatureConst, commutator, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The zero constant connection has zero curvature. -/
theorem curvatureConst_zero_left (Γ : Mat2) :
    curvatureConst 0 Γ = 0 := by
  simp [curvatureConst, commutator]

/-- The zero constant connection acts trivially. -/
theorem covDerivConst_zero (X : Mat2) :
    covDerivConst 0 X = 0 := by
  simp [covDerivConst, commutator]

/-- If two constant connections commute, their curvature action is zero. -/
theorem curvature_action_zero_of_commuting {Γ Λ X : Mat2}
    (hcomm : commutator Γ Λ = 0) :
    commutator (curvatureConst Γ Λ) X = 0 := by
  unfold curvatureConst
  rw [hcomm]
  simp [commutator]

/-- Constant gauge conjugation preserves commutators, with an explicit inverse property. -/
theorem commutator_conjugation_covariant (U V Γ X : Mat2)
    (hVU : V * U = 1) :
    commutator (U * Γ * V) (U * X * V) = U * commutator Γ X * V := by
  calc
    commutator (U * Γ * V) (U * X * V)
        = (U * Γ * (V * U) * X * V) - (U * X * (V * U) * Γ * V) := by
            simp [commutator, mul_assoc]
    _ = (U * Γ * X * V) - (U * X * Γ * V) := by simp [hVU]
    _ = U * commutator Γ X * V := by simp [commutator, mul_assoc, sub_mul, mul_sub]

/-- Constant gauge conjugation preserves the constant covariant derivative action. -/
theorem covDerivConst_conjugation_covariant (U V Γ X : Mat2)
    (hVU : V * U = 1) :
    covDerivConst (U * Γ * V) (U * X * V) = U * covDerivConst Γ X * V := by
  simpa [covDerivConst] using commutator_conjugation_covariant U V Γ X hVU

/-- Repaired Section 31 finite packet combining precession and curvature-action sockets. -/
theorem repaired_section31_dynamics_packet
    (ω1 ω2 ω3 n1 n2 n3 : ℂ) (Γ Λ X : Mat2) :
    vonNeumannRHS ω1 ω2 ω3 n1 n2 n3 =
      (1 / 2 : ℂ) •
        (blochCross1 ω1 ω2 ω3 n1 n2 n3 • σ1 +
          blochCross2 ω1 ω2 ω3 n1 n2 n3 • σ2 +
          blochCross3 ω1 ω2 ω3 n1 n2 n3 • σ3) ∧
    covDerivConst Γ (covDerivConst Λ X) -
      covDerivConst Λ (covDerivConst Γ X) =
        commutator (curvatureConst Γ Λ) X := by
  refine ⟨?_, ?_⟩
  · exact vonNeumannRHS_eq_bloch_precession ω1 ω2 ω3 n1 n2 n3
  · exact covDerivConst_commutator_eq_curvature_action Γ Λ X

end InfoGeometry.Physics.Section31UnifiedMatrixDynamics

end noncomputable section
