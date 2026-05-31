import Mathlib

set_option autoImplicit false

namespace InfoGeometry.Clifford

structure SplitQuaternion where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

@[ext]
lemma SplitQuaternion.ext {q1 q2 : SplitQuaternion}
    (hw : q1.w = q2.w) (hx : q1.x = q2.x) (hy : q1.y = q2.y) (hz : q1.z = q2.z) :
    q1 = q2 := by
  cases q1
  cases q2
  congr

def sqAdd (q1 q2 : SplitQuaternion) : SplitQuaternion :=
  ⟨q1.w + q2.w, q1.x + q2.x, q1.y + q2.y, q1.z + q2.z⟩

def sqMul (q1 q2 : SplitQuaternion) : SplitQuaternion :=
  ⟨q1.w * q2.w - q1.x * q2.x + q1.y * q2.y + q1.z * q2.z,
   q1.w * q2.x + q1.x * q2.w - q1.y * q2.z + q1.z * q2.y,
   q1.w * q2.y + q1.y * q2.w - q1.x * q2.z + q1.z * q2.x,
   q1.w * q2.z + q1.z * q2.w + q1.x * q2.y - q1.y * q2.x⟩

def sqOne : SplitQuaternion :=
  ⟨1, 0, 0, 0⟩

def sqZero : SplitQuaternion :=
  ⟨0, 0, 0, 0⟩

instance : Add SplitQuaternion where
  add := sqAdd

instance : Mul SplitQuaternion where
  mul := sqMul

instance : One SplitQuaternion where
  one := sqOne

instance : Zero SplitQuaternion where
  zero := sqZero

theorem mul_assoc (q1 q2 q3 : SplitQuaternion) :
    (q1 * q2) * q3 = q1 * (q2 * q3) := by
  change sqMul (sqMul q1 q2) q3 = sqMul q1 (sqMul q2 q3)
  ext <;> simp [sqMul] <;> ring

theorem one_mul (q : SplitQuaternion) :
    1 * q = q := by
  change sqMul sqOne q = q
  ext <;> simp [sqMul, sqOne]

theorem mul_one (q : SplitQuaternion) :
    q * 1 = q := by
  change sqMul q sqOne = q
  ext <;> simp [sqMul, sqOne]

def conjugate (q : SplitQuaternion) : SplitQuaternion :=
  ⟨q.w, -q.x, -q.y, -q.z⟩

def norm (q : SplitQuaternion) : ℝ :=
  q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z

theorem norm_mul (q1 q2 : SplitQuaternion) :
    norm (q1 * q2) = norm q1 * norm q2 := by
  change norm (sqMul q1 q2) = norm q1 * norm q2
  simp [norm, sqMul]
  ring

theorem conjugate_mul (q : SplitQuaternion) :
    conjugate q * q = ⟨norm q, 0, 0, 0⟩ := by
  change sqMul (conjugate q) q = ⟨norm q, 0, 0, 0⟩
  ext <;> simp [sqMul, conjugate, norm] <;> ring

def toMatrix (q : SplitQuaternion) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q.w + q.z, q.x + q.y;
     -q.x + q.y, q.w - q.z]

def mat_mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1;
     A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1]

def mat_add_2x2 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0 + B 0 0, A 0 1 + B 0 1;
     A 1 0 + B 1 0, A 1 1 + B 1 1]

def det_2x2 (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/- #### BUCKET 1: CLOSED FINITE THEOREMS -/
-- [Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

theorem toMatrix_one :
    toMatrix 1 = !![1, 0; 0, 1] := by
  change toMatrix sqOne = !![1, 0; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, sqOne]

theorem toMatrix_add (q1 q2 : SplitQuaternion) :
    toMatrix (q1 + q2) = mat_add_2x2 (toMatrix q1) (toMatrix q2) := by
  change toMatrix (sqAdd q1 q2) = mat_add_2x2 (toMatrix q1) (toMatrix q2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, mat_add_2x2, sqAdd] <;> ring

theorem toMatrix_mul (q1 q2 : SplitQuaternion) :
    toMatrix (q1 * q2) = mat_mul_2x2 (toMatrix q1) (toMatrix q2) := by
  change toMatrix (sqMul q1 q2) = mat_mul_2x2 (toMatrix q1) (toMatrix q2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, mat_mul_2x2, sqMul] <;> ring

theorem mul_conjugate (q : SplitQuaternion) :
    q * conjugate q = ⟨norm q, 0, 0, 0⟩ := by
  change sqMul q (conjugate q) = ⟨norm q, 0, 0, 0⟩
  ext <;> simp [sqMul, conjugate, norm] <;> ring

theorem norm_eq_det (q : SplitQuaternion) :
    norm q = det_2x2 (toMatrix q) := by
  simp [norm, toMatrix, det_2x2]
  ring_nf

structure NormOneCoq where
  val : SplitQuaternion
  property : norm val = 1

@[ext]
lemma NormOneCoq.ext {q1 q2 : NormOneCoq} (h : q1.val = q2.val) : q1 = q2 := by
  cases q1
  cases q2
  congr

instance : Mul NormOneCoq where
  mul q1 q2 := ⟨q1.val * q2.val, by
    rw [norm_mul, q1.property, q2.property]
    norm_num⟩

instance : One NormOneCoq where
  one := ⟨1, by
    change norm sqOne = 1
    simp [norm, sqOne]⟩

instance : Inv NormOneCoq where
  inv q := ⟨conjugate q.val, by
    have h : norm (conjugate q.val) = norm q.val := by
      simp [conjugate, norm]
    rw [h, q.property]⟩

instance : Group NormOneCoq where
  mul_assoc q1 q2 q3 := by
    apply NormOneCoq.ext
    exact mul_assoc q1.val q2.val q3.val
  one_mul q := by
    apply NormOneCoq.ext
    exact one_mul q.val
  mul_one q := by
    apply NormOneCoq.ext
    exact mul_one q.val
  inv_mul_cancel q := by
    apply NormOneCoq.ext
    change conjugate q.val * q.val = (1 : SplitQuaternion)
    rw [conjugate_mul q.val, q.property]
    rfl

structure SL2R where
  val : Matrix (Fin 2) (Fin 2) ℝ
  property : det_2x2 val = 1

@[ext]
lemma SL2R.ext {A B : SL2R} (h : A.val = B.val) : A = B := by
  cases A
  cases B
  congr

theorem det_2x2_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    det_2x2 (mat_mul_2x2 A B) = det_2x2 A * det_2x2 B := by
  simp [det_2x2, mat_mul_2x2]
  ring_nf

instance : Mul SL2R where
  mul A B := ⟨mat_mul_2x2 A.val B.val, by
    rw [det_2x2_mul, A.property, B.property]
    norm_num⟩

def toSL2R (q : NormOneCoq) : SL2R where
  val := toMatrix q.val
  property := by
    rw [← norm_eq_det]
    exact q.property

theorem toSL2R_mul (q1 q2 : NormOneCoq) :
    toSL2R (q1 * q2) = toSL2R q1 * toSL2R q2 := by
  apply SL2R.ext
  exact toMatrix_mul q1.val q2.val

structure NonZeroCoq where
  val : SplitQuaternion
  property : norm val ≠ 0

structure GL2R where
  val : Matrix (Fin 2) (Fin 2) ℝ
  property : det_2x2 val ≠ 0

instance : Mul NonZeroCoq where
  mul q1 q2 := ⟨q1.val * q2.val, by
    rw [norm_mul]
    exact mul_ne_zero q1.property q2.property⟩

def toGL2R (q : NonZeroCoq) : GL2R where
  val := toMatrix q.val
  property := by
    rw [← norm_eq_det]
    exact q.property

theorem toGL2R_mul (q1 q2 : NonZeroCoq) :
    (toGL2R (q1 * q2)).val = mat_mul_2x2 (toGL2R q1).val (toGL2R q2).val := by
  exact toMatrix_mul q1.val q2.val

/- #### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES -/
-- [No conditional theorem in this module.]

/- #### BUCKET 3: OPEN CLOSURE DEBT -/
-- [No open closure debt in this module.]

end InfoGeometry.Clifford
