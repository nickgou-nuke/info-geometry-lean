import Mathlib.Tactic

set_option autoImplicit false

/-! # Split-quaternion (coquaternion) concrete algebra

Provides a concrete `SplitQuaternion` structure with explicit 2×2 matrix
representation and proofs of algebraic homomorphism properties including
the group isomorphism to GL(2,ℝ).
-/

open Matrix

/-- Split-quaternion (coquaternion) associative algebra over ℝ with basis (1,i,j,k)
    where i² = -1, j² = 1, k² = 1, ij = k = -ji, jk = -i, ki = j. -/
@[ext]
structure SplitQuaternion where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

instance : Add SplitQuaternion where
  add q1 q2 := ⟨q1.w + q2.w, q1.x + q2.x, q1.y + q2.y, q1.z + q2.z⟩

instance : Mul SplitQuaternion where
  mul q1 q2 := ⟨
    q1.w * q2.w - q1.x * q2.x + q1.y * q2.y + q1.z * q2.z,
    q1.w * q2.x + q1.x * q2.w - q1.y * q2.z + q1.z * q2.y,
    q1.w * q2.y + q1.y * q2.w - q1.x * q2.z + q1.z * q2.x,
    q1.w * q2.z + q1.z * q2.w + q1.x * q2.y - q1.y * q2.x
  ⟩

instance : One SplitQuaternion where
  one := ⟨1, 0, 0, 0⟩

instance : Zero SplitQuaternion where
  zero := ⟨0, 0, 0, 0⟩

@[simp]
theorem add_def (q1 q2 : SplitQuaternion) :
    q1 + q2 = ⟨q1.w + q2.w, q1.x + q2.x, q1.y + q2.y, q1.z + q2.z⟩ := rfl

@[simp]
theorem mul_def (q1 q2 : SplitQuaternion) : q1 * q2 = ⟨
    q1.w * q2.w - q1.x * q2.x + q1.y * q2.y + q1.z * q2.z,
    q1.w * q2.x + q1.x * q2.w - q1.y * q2.z + q1.z * q2.y,
    q1.w * q2.y + q1.y * q2.w - q1.x * q2.z + q1.z * q2.x,
    q1.w * q2.z + q1.z * q2.w + q1.x * q2.y - q1.y * q2.x
  ⟩ := rfl

@[simp]
theorem one_def : (1 : SplitQuaternion) = ⟨1, 0, 0, 0⟩ := rfl

@[simp]
theorem zero_def : (0 : SplitQuaternion) = ⟨0, 0, 0, 0⟩ := rfl

/-- Conjugate: q* = w - xi - yj - zk. -/
def conjugate (q : SplitQuaternion) : SplitQuaternion :=
  ⟨q.w, -q.x, -q.y, -q.z⟩

/-- Isotropic norm: N(q) = w² + x² - y² - z². -/
def norm (q : SplitQuaternion) : ℝ :=
  q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z

/-- 2×2 real matrix representation (algebra isomorphism). -/
def toMatrix (q : SplitQuaternion) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ q.w + q.z, q.x + q.y ;
     -q.x + q.y, q.w - q.z ]

/-- Inverse of `toMatrix`: reconstruct split-quaternion from any 2×2 matrix.
    Solves w+z = a₁₁, w-z = a₂₂, x+y = a₁₂, -x+y = a₂₁. -/
noncomputable def fromMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : SplitQuaternion :=
  ⟨(A 0 0 + A 1 1) / 2, (A 0 1 - A 1 0) / 2,
   (A 0 1 + A 1 0) / 2, (A 0 0 - A 1 1) / 2⟩

/-- Explicit 2×2 matrix multiplication. -/
def mat_mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1 ;
      A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1 ]

/-- Explicit 2×2 matrix addition. -/
def mat_add_2x2 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ A 0 0 + B 0 0, A 0 1 + B 0 1 ;
      A 1 0 + B 1 0, A 1 1 + B 1 1 ]

/-- Explicit 2×2 determinant. -/
def det_2x2 (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0


/- #### BUCKET 1: CLOSED FINITE THEOREMS -/

theorem toMatrix_one : toMatrix 1 = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [toMatrix, one_def]

theorem toMatrix_add (q1 q2 : SplitQuaternion) :
    toMatrix (q1 + q2) = mat_add_2x2 (toMatrix q1) (toMatrix q2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [toMatrix, add_def, mat_add_2x2]
    ring

theorem toMatrix_mul (q1 q2 : SplitQuaternion) :
    toMatrix (q1 * q2) = mat_mul_2x2 (toMatrix q1) (toMatrix q2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [toMatrix, mul_def, mat_mul_2x2]
    ring

/-- Explicit 2×2 multiplication matches matrix multiplication. -/
theorem mat_mul_2x2_eq_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    mat_mul_2x2 A B = A * B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [mat_mul_2x2, Matrix.mul_apply]

/-- The `toMatrix` map is multiplicative for the actual matrix product. -/
theorem toMatrix_mul_matrix (q1 q2 : SplitQuaternion) :
    toMatrix (q1 * q2) = toMatrix q1 * toMatrix q2 := by
  rw [toMatrix_mul, mat_mul_2x2_eq_mul]

theorem mul_conjugate (q : SplitQuaternion) :
    q * conjugate q = ⟨norm q, 0, 0, 0⟩ := by
  ext <;> dsimp [conjugate, _root_.norm, mul_def] <;> ring

theorem norm_eq_det (q : SplitQuaternion) :
    norm q = det_2x2 (toMatrix q) := by
  dsimp [_root_.norm, toMatrix, det_2x2]
  ring

theorem fromMatrix_toMatrix (q : SplitQuaternion) : fromMatrix (toMatrix q) = q := by
  ext <;> simp [fromMatrix, toMatrix] <;> ring

theorem toMatrix_fromMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : toMatrix (fromMatrix A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [toMatrix, fromMatrix]
    ring

/-- Explicit equivalence between split-quaternions and real 2×2 matrices. -/
noncomputable def splitQuaternionMatrixEquiv :
    SplitQuaternion ≃ Matrix (Fin 2) (Fin 2) ℝ where
  toFun := toMatrix
  invFun := fromMatrix
  left_inv := fromMatrix_toMatrix
  right_inv := toMatrix_fromMatrix

/-- Multiplicative equivalence between split-quaternions and real 2×2 matrices. -/
noncomputable def splitQuaternionMatrixMulEquiv :
    SplitQuaternion ≃* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := toMatrix
  invFun := fromMatrix
  left_inv := fromMatrix_toMatrix
  right_inv := toMatrix_fromMatrix
  map_mul' := toMatrix_mul_matrix

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro q1 q2 h
  calc
    q1 = fromMatrix (toMatrix q1) := by symm; exact fromMatrix_toMatrix q1
    _ = fromMatrix (toMatrix q2) := by simpa using congrArg fromMatrix h
    _ = q2 := by exact fromMatrix_toMatrix q2

theorem det_2x2_eq_det (A : Matrix (Fin 2) (Fin 2) ℝ) : det_2x2 A = A.det := by
  simp [det_2x2, Matrix.det_fin_two]

/-- The norm is multiplicative. -/
theorem splitQuaternion_norm_mul (q1 q2 : SplitQuaternion) :
    norm (q1 * q2) = norm q1 * norm q2 := by
  calc
    norm (q1 * q2) = det_2x2 (toMatrix (q1 * q2)) := by rw [norm_eq_det]
    _ = det_2x2 (toMatrix q1 * toMatrix q2) := by rw [toMatrix_mul_matrix]
    _ = (toMatrix q1 * toMatrix q2).det := by rw [det_2x2_eq_det]
    _ = (toMatrix q1).det * (toMatrix q2).det := by rw [Matrix.det_mul]
    _ = det_2x2 (toMatrix q1) * det_2x2 (toMatrix q2) := by rw [← det_2x2_eq_det, ← det_2x2_eq_det]
    _ = norm q1 * norm q2 := by rw [← norm_eq_det, ← norm_eq_det]

theorem norm_eq_zero_iff (q : SplitQuaternion) : norm q = 0 ↔ (toMatrix q).det = 0 := by
  rw [norm_eq_det, det_2x2_eq_det]

theorem norm_nonzero_iff_isUnit (q : SplitQuaternion) : norm q ≠ 0 ↔ IsUnit (toMatrix q) := by
  rw [ne_eq, norm_eq_zero_iff, Matrix.isUnit_iff_isUnit_det]
  by_cases h : (toMatrix q).det = 0
  · simp [h, isUnit_iff_ne_zero]
  · simp [h, isUnit_iff_ne_zero]

/-- The `toMatrix` map restricts to a multiplicative bijection between the set of
    split-quaternions with nonzero norm and GL(2,ℝ). -/
theorem split_quaternion_gl2_isomorphism :
    let S : Set SplitQuaternion := {q | norm q ≠ 0}
    ∃ (φ₁ : S → GL (Fin 2) ℝ) (φ₂ : GL (Fin 2) ℝ → S),
      (∀ x, φ₂ (φ₁ x) = x) ∧ (∀ y, φ₁ (φ₂ y) = y) := by
  intro S
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro qh
    let q := qh.1
    let hq := qh.2
    have hu : IsUnit (toMatrix q) := ((norm_nonzero_iff_isUnit q).mp hq)
    exact hu.unit
  · intro A
    let q := fromMatrix (A.val)
    have hnorm : norm q ≠ 0 := by
      intro h_zero
      rw [norm_eq_zero_iff] at h_zero
      rw [toMatrix_fromMatrix] at h_zero
      have hdet : A.val.det = 0 := h_zero
      have := A.isUnit
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
      exact this hdet
    exact ⟨q, hnorm⟩
  · intro x
    apply Subtype.ext
    dsimp
    exact fromMatrix_toMatrix x.val
  · intro y
    ext i j
    dsimp
    rw [toMatrix_fromMatrix]

instance : Mul {q : SplitQuaternion // norm q ≠ 0} where
  mul a b :=
    ⟨a.1 * b.1, by
      intro hzero
      have hmul : norm a.1 * norm b.1 = 0 := by
        rw [← splitQuaternion_norm_mul, hzero]
      rcases mul_eq_zero.mp hmul with ha | hb
      · exact a.2 ha
      · exact b.2 hb⟩

/-- A concrete multiplicative equivalence between the nonzero-norm split-quaternions and GL(2,ℝ). -/
noncomputable def splitQuaternionGL2Equiv :
    {q : SplitQuaternion // norm q ≠ 0} ≃* GL (Fin 2) ℝ where
  toFun := fun qh =>
    let q := qh.1
    let hq := qh.2
    have hu : IsUnit (toMatrix q) := ((norm_nonzero_iff_isUnit q).mp hq)
    hu.unit
  invFun := fun A =>
    ⟨fromMatrix A.val, by
      intro h_zero
      rw [norm_eq_zero_iff] at h_zero
      rw [toMatrix_fromMatrix] at h_zero
      have hdet : A.val.det = 0 := h_zero
      have := A.isUnit
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
      exact this hdet⟩
  left_inv := by
    intro qh
    apply Subtype.ext
    exact fromMatrix_toMatrix qh.1
  right_inv := by
    intro A
    apply Units.ext
    ext i j
    simp [toMatrix_fromMatrix]
  map_mul' := by
    intro a b
    apply Units.ext
    simpa [IsUnit.unit_spec] using toMatrix_mul_matrix a.1 b.1

/- #### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES -/

class SpecialLinearEquivalence (G : Type*) [Group G] where
  embed : G → SplitQuaternion
  norm_one : ∀ g : G, norm (embed g) = 1


/- #### BUCKET 3: OPEN CLOSURE DEBT -/
