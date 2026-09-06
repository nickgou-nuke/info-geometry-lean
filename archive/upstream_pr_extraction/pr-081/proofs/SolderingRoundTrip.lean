import Mathlib

open Matrix

/-!
# Reversible Soldering Round Trips

The four real coordinates can be read as a vector, a quaternion-coordinate
tuple, or a real split Pauli matrix.  The maps are algebraic inverses.
-/

@[ext]
structure Vec4 where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

@[ext]
structure Quat4 where
  scalar : ℝ
  i : ℝ
  j : ℝ
  k : ℝ

def vecToQuat (v : Vec4) : Quat4 where
  scalar := v.t
  i := v.x
  j := v.y
  k := v.z

def quatToVec (q : Quat4) : Vec4 where
  t := q.scalar
  x := q.i
  y := q.j
  z := q.k

def vecToMatrix (v : Vec4) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v.t + v.z, v.x + v.y; v.x - v.y, v.t - v.z]

noncomputable def matrixToVec (M : Matrix (Fin 2) (Fin 2) ℝ) : Vec4 where
  t := (M 0 0 + M 1 1) / 2
  x := (M 0 1 + M 1 0) / 2
  y := (M 0 1 - M 1 0) / 2
  z := (M 0 0 - M 1 1) / 2

def quatToMatrix (q : Quat4) : Matrix (Fin 2) (Fin 2) ℝ :=
  vecToMatrix (quatToVec q)

noncomputable def matrixToQuat (M : Matrix (Fin 2) (Fin 2) ℝ) : Quat4 :=
  vecToQuat (matrixToVec M)

theorem quat_vec_roundtrip (q : Quat4) : vecToQuat (quatToVec q) = q := by
  cases q
  rfl

theorem vec_quat_roundtrip (v : Vec4) : quatToVec (vecToQuat v) = v := by
  cases v
  rfl

theorem matrix_vec_roundtrip (M : Matrix (Fin 2) (Fin 2) ℝ) :
    vecToMatrix (matrixToVec M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecToMatrix, matrixToVec] <;> ring

theorem vec_matrix_roundtrip (v : Vec4) :
    matrixToVec (vecToMatrix v) = v := by
  cases v
  ext <;> simp [vecToMatrix, matrixToVec]

theorem quat_matrix_roundtrip (q : Quat4) :
    matrixToQuat (quatToMatrix q) = q := by
  cases q
  ext <;> simp [matrixToQuat, quatToMatrix, vecToQuat, quatToVec, vecToMatrix, matrixToVec]

theorem matrix_quat_roundtrip (M : Matrix (Fin 2) (Fin 2) ℝ) :
    quatToMatrix (matrixToQuat M) = M := by
  rw [matrixToQuat, quatToMatrix]
  exact matrix_vec_roundtrip M

theorem det_vecToMatrix (v : Vec4) :
    (vecToMatrix v).det = v.t ^ 2 - v.x ^ 2 + v.y ^ 2 - v.z ^ 2 := by
  cases v
  rw [Matrix.det_fin_two]
  simp [vecToMatrix]
  ring

/-- Vector, quaternion-coordinate, and matrix soldering maps are mutually reversible,
    and the matrix determinant is the quadratic form. -/
theorem soldering_roundtrip_theorem :
    (∀ v, quatToVec (vecToQuat v) = v) ∧
    (∀ q, vecToQuat (quatToVec q) = q) ∧
    (∀ v, matrixToVec (vecToMatrix v) = v) ∧
    (∀ M, vecToMatrix (matrixToVec M) = M) ∧
    (∀ q, matrixToQuat (quatToMatrix q) = q) ∧
    (∀ M, quatToMatrix (matrixToQuat M) = M) ∧
    (∀ v, (vecToMatrix v).det = v.t ^ 2 - v.x ^ 2 + v.y ^ 2 - v.z ^ 2) := by
  exact ⟨vec_quat_roundtrip, quat_vec_roundtrip, vec_matrix_roundtrip,
    matrix_vec_roundtrip, quat_matrix_roundtrip, matrix_quat_roundtrip,
    det_vecToMatrix⟩
