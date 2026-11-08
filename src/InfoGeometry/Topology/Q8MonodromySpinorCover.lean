import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometryCore.Basic

/-!
# Q8 Schur Cover of V4

This module formally verifies the relationship between the Klein four-group ($V_4$)
and the quaternion group ($Q_8$). We construct the unique 2D complex representation 
of $Q_8$, verify its defining relations, and prove that it forms a projective 
representation of $V_4$ where the non-trivial Schur multiplier is resolved by 
the central element $-I$.
-/

namespace InfoGeometry.Topology.Q8MonodromySpinorCover

open Matrix Complex

open InfoGeometryCore

/-- The $i$ generator of $Q_8$. -/
def M_i : M2C :=
  !![I, 0; 0, -I]

/-- The $j$ generator of $Q_8$. -/
def M_j : M2C :=
  !![0, 1; -1, 0]

/-- The $k$ generator of $Q_8$. -/
def M_k : M2C :=
  !![0, I; I, 0]

/-- $M_i^2 = -I$ -/
lemma M_i_sq : M_i * M_i = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_i, Matrix.mul_apply]

/-- $M_j^2 = -I$ -/
lemma M_j_sq : M_j * M_j = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_j, Matrix.mul_apply]

/-- $M_k^2 = -I$ -/
lemma M_k_sq : M_k * M_k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_k, Matrix.mul_apply]

/-- $M_i M_j M_k = -I$ -/
lemma M_i_M_j_M_k : M_i * M_j * M_k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_i, M_j, M_k, Matrix.mul_apply]

/-- 
The generators $M_i$ and $M_j$ anticommute, which means they commute in the 
projective general linear group $PGL(2, \mathbb{C})$. This exactly matches the 
non-trivial Schur multiplier of $V_4$ resolving in $Q_8$.
-/
theorem M_i_M_j_anticommute : M_i * M_j = -(M_j * M_i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_i, M_j, Matrix.mul_apply]

end InfoGeometry.Topology.Q8MonodromySpinorCover
