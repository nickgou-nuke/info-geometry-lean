import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.ZornMatrixSU3.Vector3

set_option linter.unusedSimpArgs false
namespace InfoGeometry.Physics.ZornMatrixSU3

/-!
## 2. Zorn Matrix Type
-/

/-- A Zorn matrix representing a split octonion -/
structure ZornMatrix where
  /-- Upper-left scalar -/
  a : ℝ
  /-- Lower-right scalar -/
  b : ℝ
  /-- Upper-right vector (color triplet) -/
  x : Fin 3 → ℝ
  /-- Lower-left vector (color antitriplet) -/
  y : Fin 3 → ℝ

/-- Zero Zorn matrix -/
def zero : ZornMatrix :=
  ⟨0, 0, fun _ => 0, fun _ => 0⟩

/-- Unit Zorn matrix -/
def one : ZornMatrix :=
  ⟨1, 1, fun _ => 0, fun _ => 0⟩

/-- Zorn matrix addition -/
def add (M N : ZornMatrix) : ZornMatrix :=
  ⟨M.a + N.a, M.b + N.b, M.x + N.x, M.y + N.y⟩

/-- Zorn matrix negation -/
def neg (M : ZornMatrix) : ZornMatrix :=
  ⟨-M.a, -M.b, -M.x, -M.y⟩

/-- Zorn matrix multiplication (Günaydin-Gürsey rule) -/
def mul (M N : ZornMatrix) : ZornMatrix :=
  ⟨M.a * N.a + dotProduct M.x N.y,
   M.b * N.b + dotProduct M.y N.x,
   M.a • N.x + N.b • M.x - crossProduct M.y N.y,
   M.b • N.y + N.a • M.y + crossProduct M.x N.x⟩

instance : Zero ZornMatrix := ⟨zero⟩
instance : One ZornMatrix := ⟨one⟩
instance : Add ZornMatrix := ⟨add⟩
instance : Neg ZornMatrix := ⟨neg⟩
instance : Mul ZornMatrix := ⟨mul⟩

@[simp] theorem mul_a (M N : ZornMatrix) : (M * N).a = M.a * N.a + dotProduct M.x N.y := rfl
@[simp] theorem mul_b (M N : ZornMatrix) : (M * N).b = M.b * N.b + dotProduct M.y N.x := rfl
@[simp] theorem mul_x (M N : ZornMatrix) : (M * N).x = M.a • N.x + N.b • M.x - crossProduct M.y N.y := rfl
@[simp] theorem mul_y (M N : ZornMatrix) : (M * N).y = M.b • N.y + N.a • M.y + crossProduct M.x N.x := rfl

@[simp] theorem zero_a : (0 : ZornMatrix).a = 0 := rfl
@[simp] theorem zero_b : (0 : ZornMatrix).b = 0 := rfl
@[simp] theorem zero_x : (0 : ZornMatrix).x = (0 : Fin 3 → ℝ) := by rfl
@[simp] theorem zero_y : (0 : ZornMatrix).y = (0 : Fin 3 → ℝ) := by rfl

@[simp] theorem one_a : (1 : ZornMatrix).a = 1 := rfl
@[simp] theorem one_b : (1 : ZornMatrix).b = 1 := rfl
@[simp] theorem one_x : (1 : ZornMatrix).x = (0 : Fin 3 → ℝ) := rfl
@[simp] theorem one_y : (1 : ZornMatrix).y = (0 : Fin 3 → ℝ) := rfl

@[simp] theorem neg_a (M : ZornMatrix) : (-M).a = -M.a := rfl
@[simp] theorem neg_b (M : ZornMatrix) : (-M).b = -M.b := rfl
@[simp] theorem neg_x (M : ZornMatrix) : (-M).x = -M.x := rfl
@[simp] theorem neg_y (M : ZornMatrix) : (-M).y = -M.y := rfl

@[simp] theorem add_a (M N : ZornMatrix) : (M + N).a = M.a + N.a := rfl
@[simp] theorem add_b (M N : ZornMatrix) : (M + N).b = M.b + N.b := rfl
@[simp] theorem add_x (M N : ZornMatrix) : (M + N).x = M.x + N.x := rfl
@[simp] theorem add_y (M N : ZornMatrix) : (M + N).y = M.y + N.y := rfl

@[ext] theorem ext (M N : ZornMatrix)
    (ha : M.a = N.a) (hb : M.b = N.b) (hx : M.x = N.x) (hy : M.y = N.y) : M = N := by
  cases M; cases N; cases ha; cases hb; cases hx; cases hy; rfl

def smul (r : ℝ) (M : ZornMatrix) : ZornMatrix :=
  ⟨r * M.a, r * M.b, r • M.x, r • M.y⟩

instance : SMul ℝ ZornMatrix := ⟨smul⟩

@[simp] theorem smul_a (r : ℝ) (M : ZornMatrix) : (r • M).a = r * M.a := rfl
@[simp] theorem smul_b (r : ℝ) (M : ZornMatrix) : (r • M).b = r * M.b := rfl
@[simp] theorem smul_x (r : ℝ) (M : ZornMatrix) : (r • M).x = r • M.x := rfl
@[simp] theorem smul_y (r : ℝ) (M : ZornMatrix) : (r • M).y = r • M.y := rfl

instance : AddCommGroup ZornMatrix where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc M N P := by
    ext i <;> simp [add, add_assoc]
  zero_add M := by
    ext i <;> simp [zero, add]
  add_zero M := by
    ext i <;> simp [zero, add]
  neg_add_cancel M := by
    ext i <;> simp [zero, add, neg]
  add_comm M N := by
    ext i <;> simp [add, add_comm]

instance : Module ℝ ZornMatrix where
  one_smul M := by
    ext i <;> simp [smul]
  mul_smul r s M := by
    ext i <;> simp [smul, mul_assoc]
  smul_zero r := by
    ext i <;> simp [smul, zero]
  smul_add r M N := by
    ext i <;> simp [smul, add, mul_add]
  add_smul r s M := by
    ext i <;> simp [smul, add_mul]
  zero_smul M := by
    ext i <;> simp [smul]

/-!
## 3. Split Octonion Norm and Conjugation
-/

/-- Split octonion norm: N(M) = ab - x⃗·y⃗ -/
def norm (M : ZornMatrix) : ℝ :=
  M.a * M.b - dotProduct M.x M.y

/-- Zorn matrix conjugation -/
def conjugate (M : ZornMatrix) : ZornMatrix :=
  ⟨M.b, M.a, -M.x, -M.y⟩

theorem norm_conjugate (M : ZornMatrix) :
    norm (conjugate M) = norm M := by
  simpa [norm, conjugate, dotProduct] using
    (ZornVectorMatrixExplicit.zornNorm_conj (M.a, M.b, M.x, M.y))

theorem norm_mul (M N : ZornMatrix) :
    norm (M * N) = norm M * norm N := by
  change
    ZornVectorMatrixExplicit.zornNorm
      (ZornVectorMatrixExplicit.zornMul
        (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y)) =
      ZornVectorMatrixExplicit.zornNorm (M.a, M.b, M.x, M.y) *
      ZornVectorMatrixExplicit.zornNorm (N.a, N.b, N.x, N.y)
  simpa [norm, dotProduct, crossProduct,
    ZornVectorMatrixExplicit.zornNorm,
    ZornVectorMatrixExplicit.zornMul] using
    (ZornVectorMatrixExplicit.zornNorm_mul
      (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y))

@[simp] theorem zero_mul_zorn (M : ZornMatrix) : (0 : ZornMatrix) * M = 0 := by
  ext i <;>
    simp [dotProduct, crossProduct,
      ZornVectorMatrixExplicit.dot3,
      ZornVectorMatrixExplicit.cross3]
  all_goals fin_cases i <;> norm_num

@[simp] theorem mul_zero_zorn (M : ZornMatrix) : M * (0 : ZornMatrix) = 0 := by
  ext i <;>
    simp [dotProduct, crossProduct,
      ZornVectorMatrixExplicit.dot3,
      ZornVectorMatrixExplicit.cross3]
  all_goals fin_cases i <;> norm_num

theorem add_mul_zorn (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by
  ext
  · simp [dotProduct, add_mul, mul_add, ZornVectorMatrixExplicit.dot3]; ring
  · simp [dotProduct, add_mul, mul_add, ZornVectorMatrixExplicit.dot3]; ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, ZornVectorMatrixExplicit.cross3] <;> ring

theorem mul_add_zorn (M N P : ZornMatrix) : M * (N + P) = M * N + M * P := by
  ext
  · simp [dotProduct, add_mul, mul_add, ZornVectorMatrixExplicit.dot3]; ring
  · simp [dotProduct, add_mul, mul_add, ZornVectorMatrixExplicit.dot3]; ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, ZornVectorMatrixExplicit.cross3] <;> ring

theorem smul_mul_zorn (r : ℝ) (M N : ZornMatrix) : (r • M) * N = r • (M * N) := by
  ext
  · simp [dotProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, ZornVectorMatrixExplicit.dot3]; try ring
  · simp [dotProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, ZornVectorMatrixExplicit.dot3]; try ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, ZornVectorMatrixExplicit.cross3] <;> try ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, ZornVectorMatrixExplicit.cross3] <;> try ring

theorem mul_smul_zorn (r : ℝ) (M N : ZornMatrix) : M * (r • N) = r • (M * N) := by
  ext
  · simp [dotProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, mul_comm, mul_left_comm, ZornVectorMatrixExplicit.dot3]; try ring
  · simp [dotProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, mul_comm, mul_left_comm, ZornVectorMatrixExplicit.dot3]; try ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, mul_comm, mul_left_comm, ZornVectorMatrixExplicit.cross3] <;> try ring
  · rename_i i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, smul_assoc, mul_assoc, mul_comm, mul_left_comm, ZornVectorMatrixExplicit.cross3] <;> try ring

@[simp] theorem one_mul_zorn (M : ZornMatrix) : (1 : ZornMatrix) * M = M := by
  ext i <;>
    simp [dotProduct, crossProduct,
      ZornVectorMatrixExplicit.dot3,
      ZornVectorMatrixExplicit.cross3]
  all_goals try fin_cases i <;> norm_num

@[simp] theorem mul_one_zorn (M : ZornMatrix) : M * (1 : ZornMatrix) = M := by
  ext i <;>
    simp [dotProduct, crossProduct,
      ZornVectorMatrixExplicit.dot3,
      ZornVectorMatrixExplicit.cross3]
  all_goals try fin_cases i <;> norm_num

end InfoGeometry.Physics.ZornMatrixSU3
