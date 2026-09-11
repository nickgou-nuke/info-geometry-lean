import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.ZornOctonionAnyonGellMannBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex ZornOctonionAnyon

namespace ZornSupercharge

/-- Boundary Supersymmetric Supercharge Operator Q = (0, Q_+; Q_-, 0) with nilpotent chiral charges. -/
structure BoundarySupercharge (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  Q_plus : Matrix (Fin n) (Fin n) ℂ
  Q_minus : Matrix (Fin n) (Fin n) ℂ
  h_nilpotent_plus : Q_plus * Q_plus = 0
  h_nilpotent_minus : Q_minus * Q_minus = 0

namespace BoundarySupercharge

variable (Q : BoundarySupercharge n)

/-- Supersymmetric Wedge Hamiltonian Component H_+ = Q_+ Q_+† + Q_-† Q_-. -/
def hamiltonianPlus : Matrix (Fin n) (Fin n) ℂ :=
  Q.Q_plus * Q.Q_plus.conjTranspose + Q.Q_minus.conjTranspose * Q.Q_minus

/-- Supersymmetric Wedge Hamiltonian Component H_- = Q_- Q_-† + Q_+† Q_+. -/
def hamiltonianMinus : Matrix (Fin n) (Fin n) ℂ :=
  Q.Q_minus * Q.Q_minus.conjTranspose + Q.Q_plus.conjTranspose * Q.Q_plus

/-- **Theorem**: Supersymmetric Partner Hamiltonians Trace Equality: Tr(H_+) = Tr(H_-). -/
theorem susy_partner_hamiltonian_trace_eq :
    trace Q.hamiltonianPlus = trace Q.hamiltonianMinus := by
  dsimp [hamiltonianPlus, hamiltonianMinus]
  rw [trace_add, trace_add]
  have h1 : trace (Q.Q_plus * Q.Q_plus.conjTranspose) = trace (Q.Q_plus.conjTranspose * Q.Q_plus) := trace_mul_comm Q.Q_plus Q.Q_plus.conjTranspose
  have h2 : trace (Q.Q_minus.conjTranspose * Q.Q_minus) = trace (Q.Q_minus * Q.Q_minus.conjTranspose) := trace_mul_comm Q.Q_minus.conjTranspose Q.Q_minus
  rw [h1, h2, add_comm]

/-- **Theorem**: Möbius Boundary Quadric Scalar Square Root Duality:
    If det(Z) = a * b - v • w = 0, then a * b = v • w. -/
theorem moebius_boundary_scalar_product_eq_dot (a b : ℂ) (v w : Fin 3 → ℂ)
    (h_null : ZornCell.detZ ⟨a, w, v, b⟩ = 0) :
    a * b = ZornCell.colorDot v w := by
  dsimp [ZornCell.detZ] at h_null
  have h_pair := sub_eq_zero.mp h_null
  simpa [ZornCell.colorDot, InfoGeometry.Physics.SplitOctonionBraidSU3.dot3,
    mul_comm, add_comm, add_left_comm] using h_pair

/-- **Theorem**: Supercharge Nilpotent Trace Vanishing: Tr(Q_+²) = 0 and Tr(Q_-²) = 0. -/
theorem supercharge_nilpotent_trace_zero :
    trace (Q.Q_plus * Q.Q_plus) = 0 ∧ trace (Q.Q_minus * Q.Q_minus) = 0 := by
  rw [Q.h_nilpotent_plus, Q.h_nilpotent_minus, trace_zero, and_self]

end BoundarySupercharge

end ZornSupercharge
