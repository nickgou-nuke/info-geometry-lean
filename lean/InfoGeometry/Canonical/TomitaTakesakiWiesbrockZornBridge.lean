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

namespace TomitaTakesakiWiesbrock

/-- Tomita-Takesaki Wiesbrock Zorn Modular Structure with Left Wedge KM, Right Commutant KN, and Cross-Horizon Vector v, w. -/
structure TomitaZornWiesbrock (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  K_M : ℂ
  K_N : ℂ
  v : Fin 3 → ℂ
  w : Fin 3 → ℂ
  P_plus : ℂ
  h_wiesbrock : ZornCell.colorDot v w = 2 * P_plus

namespace TomitaZornWiesbrock

variable (sys : TomitaZornWiesbrock n)

/-- Boundary Zorn Matrix Representation Z = (K_M, K_N, v, w). -/
def zornBoundary : ZornCell where
  a := sys.K_M
  u := sys.w
  v := sys.v
  b := sys.K_N

/-- **Theorem**: Wiesbrock HSMI Zorn Determinant Expansion:
    det(Z_boundary) = K_M * K_N - 2 P_+. -/
theorem wiesbrock_zorn_det_expansion :
    ZornCell.detZ sys.zornBoundary = sys.K_M * sys.K_N - 2 * sys.P_plus := by
  dsimp [zornBoundary, ZornCell.detZ]
  change sys.K_M * sys.K_N - ZornCell.colorDot sys.w sys.v =
    sys.K_M * sys.K_N - 2 * sys.P_plus
  have h_pair : ZornCell.colorDot sys.w sys.v = 2 * sys.P_plus := by
    simpa [ZornCell.colorDot,
      InfoGeometry.Physics.SplitOctonionBraidSU3.dot3,
      mul_comm, add_comm, add_left_comm] using sys.h_wiesbrock
  rw [h_pair]

/-- **Theorem**: Wiesbrock Null Boundary Condition (det(Z_boundary) = 0):
    K_M * K_N = 2 P_+. -/
theorem wiesbrock_null_boundary_eq (h_null : ZornCell.detZ sys.zornBoundary = 0) :
    sys.K_M * sys.K_N = 2 * sys.P_plus := by
  have h_exp := sys.wiesbrock_zorn_det_expansion
  rw [h_null] at h_exp
  exact sub_eq_zero.mp h_exp.symm

/-- **Theorem**: Tomita Modular Conjugation J J† = 1 Trace Conservation:
    Tr(J * J†) = n. -/
theorem tomita_j_trace_conservation (J : Matrix (Fin n) (Fin n) ℂ) (h_J_unitary : J * J.conjTranspose = 1) :
    trace (J * J.conjTranspose) = (n : ℂ) := by
  rw [h_J_unitary, trace_one, Fintype.card_fin]

end TomitaZornWiesbrock

end TomitaTakesakiWiesbrock
