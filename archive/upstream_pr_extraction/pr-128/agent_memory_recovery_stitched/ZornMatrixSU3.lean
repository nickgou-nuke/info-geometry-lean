import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Clifford.Cl11CoordinateAlgebra
import InfoGeometry.Clifford.GammaMatrices

open Matrix

/-!
# InfoGeometry.Physics.ZornMatrixSU3

**Zorn Matrices, Split Octonions, and SU(3) Color Symmetry**

This file formalizes the Günaydin-Gürsey construction connecting:
1. Zorn's vector-matrix representation of octonions
2. Split octonions O_s with signature (4,4)
3. SU(3) as the stabilizer subgroup of G₂
4. Color triplet/antitriplet representations from off-diagonal vectors

## Mathematical Structure

A Zorn matrix has the form:
```
    [a   x⃗ ]
M = [       ]    where a,b ∈ ℝ, x⃗,y⃗ ∈ ℝ³
    [y⃗   b ]
```

Multiplication rule:
```
[a   x⃗ ] [a'  x⃗']   [aa' + x⃗·y⃗'    ax⃗' + a'x⃗ - y⃗×y⃗']
[y⃗   b ] [y⃗'  b'] = [ya' + b'y⃗ - x⃗×x⃗'    bb' + y⃗·x⃗'  ]
```

The split octonion norm is:
```
N(M) = ab - x⃗·y⃗
```

## Connection to Cl(1,1) and SU(3)

The diagonal projectors:
```
OP₁ = [1  0]    OP₂ = [0  0]
      [0  0]          [0  1]
```

Sandwiching isolates color modes:
```
OP₁ · M · OP₂ = [0  x⃗]    (color triplet 3)
                [0  0 ]

OP₂ · M · OP₁ = [0  0 ]    (color antitriplet 3̄)
                [y⃗ 0 ]
```

The G₂ automorphism group preserves this structure, with SU(3) ⊂ G₂
being the subgroup that fixes OP₁ and OP₂.

## Tripotent Eigenvalues and Anyonic Braiding

The grading operator χ from Cl(1,1) extends to the octonionic structure:
- Eigenvalue +1: quarks (fundamental 3)
- Eigenvalue -1: antiquarks (antifundamental 3̄)
- Eigenvalue 0: diagonal scalars (color singlets)

This Z₃ grading governs anyonic braiding in the color space.
-/

namespace InfoGeometry.Physics.ZornMatrixSU3

/-!
## 1. Vector Cross Product in ℝ³
-/

/-- Cross product in ℝ³ -/
def crossProduct (x y : Fin 3 → ℝ) : Fin 3 → ℝ := InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3 x y

/-- Dot product in ℝ³ -/
def dotProduct (x y : Fin 3 → ℝ) : ℝ := InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3 x y

theorem dotProduct_comm (x y : Fin 3 → ℝ) :
    dotProduct x y = dotProduct y x := by
  simpa [dotProduct] using
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3_comm x y

@[simp] theorem dotProduct_zero_left (x : Fin 3 → ℝ) :
    dotProduct (fun _ : Fin 3 => 0) x = 0 := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

@[simp] theorem dotProduct_zero_right (x : Fin 3 → ℝ) :
    dotProduct x (fun _ : Fin 3 => 0) = 0 := by
  simpa [dotProduct_comm] using dotProduct_zero_left x

@[simp] theorem dotProduct_zero_zero :
    dotProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = 0 := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

theorem dotProduct_add_left (x y z : Fin 3 → ℝ) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_add_right (x y z : Fin 3 → ℝ) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct (r • x) y = r * dotProduct x y := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct x (r • y) = r * dotProduct x y := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

@[simp] theorem crossProduct_zero_left (x : Fin 3 → ℝ) :
    crossProduct (fun _ : Fin 3 => 0) x = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_zero :
    crossProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_right (x : Fin 3 → ℝ) :
    crossProduct x (fun _ : Fin 3 => 0) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

theorem crossProduct_add_left (x y z : Fin 3 → ℝ) :
    crossProduct (x + y) z = crossProduct x z + crossProduct y z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_add_right (x y z : Fin 3 → ℝ) :
    crossProduct x (y + z) = crossProduct x y + crossProduct x z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct (r • x) y = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct x (r • y) = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_anticomm (x y : Fin 3 → ℝ) :
    crossProduct x y = -(crossProduct y x) := by
  ext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

@[simp] theorem crossProduct_self (x : Fin 3 → ℝ) :
    crossProduct x x = (0 : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

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
@[simp] theorem zero_x : (0 : ZornMatrix).x = (0 : Fin 3 → ℝ) := by
  rfl
@[simp] theorem zero_y : (0 : ZornMatrix).y = (0 : Fin 3 → ℝ) := by
  rfl

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
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_conj (M.a, M.b, M.x, M.y))

theorem norm_mul (M N : ZornMatrix) :
    norm (M * N) = norm M * norm N := by
  change
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm
      (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul
        (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y)) =
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (M.a, M.b, M.x, M.y) *
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (N.a, N.b, N.x, N.y)
  simpa [norm, dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul] using
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_mul
      (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y))


/-!
## 4. Diagonal Projectors and Color Decomposition
-/

/-- First diagonal projector (selects upper block) -/
def projector1 : ZornMatrix :=
  ⟨1, 0, fun _ => 0, fun _ => 0⟩

/-- Second diagonal projector (selects lower block) -/
def projector2 : ZornMatrix :=
  ⟨0, 1, fun _ => 0, fun _ => 0⟩

@[simp] lemma mul_projector1 (M : ZornMatrix) :
    projector1 * M = ⟨M.a, 0, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, dotProduct_zero_left, crossProduct_zero_left]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma mul_projector2 (M : ZornMatrix) :
    projector2 * M = ⟨0, M.b, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] lemma projector1_mul (M : ZornMatrix) :
    M * projector1 = ⟨M.a, 0, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, crossProduct_self]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma projector2_mul (M : ZornMatrix) :
    M * projector2 = ⟨0, M.b, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] theorem projector1_sq : projector1 * projector1 = projector1 := by
  ext
  · simp [projector1, mul]
  · simp [projector1, mul]
  · simp [projector1, mul, crossProduct_self]
  · simp [projector1, mul, crossProduct_self]

@[simp] theorem projector2_sq : projector2 * projector2 = projector2 := by
  ext
  · simp [projector2, mul]
  · simp [projector2, mul]
  · simp [projector2, mul, crossProduct_self]
  · simp [projector2, mul, crossProduct_self]

theorem projector1_projector2_orthogonal :
    projector1 * projector2 = zero ∧ projector2 * projector1 = zero := by
  constructor
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, dotProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]

theorem projector1_add_projector2 : projector1 + projector2 = one := by
  ext i <;> simp [projector1, projector2, one, add]

@[simp] theorem zero_mul_zorn (M : ZornMatrix) : (0 : ZornMatrix) * M = 0 := by
  cases M with
  | mk a b x y =>
      apply ext
      · simpa [zero, mul] using dotProduct_zero_left y
      · simpa [zero, mul] using dotProduct_zero_left x
      · simpa [zero, mul] using crossProduct_zero_left y
      · simpa [zero, mul] using crossProduct_zero_left x

@[simp] theorem mul_zero_zorn (M : ZornMatrix) : M * (0 : ZornMatrix) = 0 := by
  cases M with
  | mk a b x y =>
      apply ext
      · simpa [zero, mul] using dotProduct_zero_right x
      · simpa [zero, mul] using dotProduct_zero_right y
      · simpa [zero, mul] using crossProduct_zero_right y
      · simpa [zero, mul] using crossProduct_zero_right x

theorem add_mul_zorn (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by
  cases M <;> cases N <;> cases P <;>
  apply ext
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem mul_add_zorn (M N P : ZornMatrix) : M * (N + P) = M * N + M * P := by
  cases M <;> cases N <;> cases P <;>
  apply ext
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem smul_mul_zorn (r : ℝ) (M N : ZornMatrix) : (r • M) * N = r • (M * N) := by
  cases M <;> cases N <;>
  apply ext
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem mul_smul_zorn (r : ℝ) (M N : ZornMatrix) : M * (r • N) = r • (M * N) := by
  cases M <;> cases N <;>
  apply ext
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

@[simp] theorem one_mul_zorn (M : ZornMatrix) : (1 : ZornMatrix) * M = M := by
  cases M with
  | mk a b x y =>
      apply ext
      · simp [one, mul]
      · simp [one, mul]
      · simp [one, mul]
      · simp [one, mul]

@[simp] theorem mul_one_zorn (M : ZornMatrix) : M * (1 : ZornMatrix) = M := by
  cases M with
  | mk a b x y =>
      apply ext
      · simp [one, mul]
      · simp [one, mul]
      · simp [one, mul]
      · simp [one, mul]

/-- Color triplet extraction: OP₁ · M · OP₂ -/
def extractTriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector1 * M * projector2).x

/-- Color antitriplet extraction: OP₂ · M · OP₁ -/
def extractAntitriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector2 * M * projector1).y

/-- Diagonal scalar extraction -/
def extractScalars (M : ZornMatrix) : ℝ × ℝ :=
  ((projector1 * M * projector1).a, (projector2 * M * projector2).b)

theorem decomposition_theorem (M : ZornMatrix) :
    M = ⟨M.a, M.b, extractTriplet M, extractAntitriplet M⟩ := by
  have hx : extractTriplet M = M.x := by
    simpa [extractTriplet, mul_projector1, mul_projector2, projector2_mul]
  have hy : extractAntitriplet M = M.y := by
    simpa [extractAntitriplet, mul_projector2, projector1_mul]
  simp [hx, hy]

/-!
## 5. Real cross-product stabilizer
-/

/-- 
A real linear map on `ℝ³` that preserves both the dot product and the cross
product. This is the exact finite real stabilizer property used by the Zorn
multiplication proofs below; it is not a complex `SU(3)` formalization.
-/
def IsRealCrossProductStabilizer (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) : Prop :=
  (∀ x y, dotProduct (R x) (R y) = dotProduct x y) ∧
  (∀ x y, R (crossProduct x y) = crossProduct (R x) (R y))

/-- 
Action of a real cross-product stabilizer on a Zorn matrix.
The transformation rotates the color triplet and antitriplet
while leaving the diagonal scalars invariant.
-/
def realCrossProductStabilizerAction
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (M : ZornMatrix) : ZornMatrix :=
  ⟨M.a, M.b, R M.x, R M.y⟩

theorem realCrossProductStabilizerAction_preserves_norm
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hR : IsRealCrossProductStabilizer R) (M : ZornMatrix) :
    norm (realCrossProductStabilizerAction R M) = norm M := by
  simp [realCrossProductStabilizerAction, norm, dotProduct]
  exact hR.1 M.x M.y

theorem realCrossProductStabilizerAction_preserves_multiplication
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hR : IsRealCrossProductStabilizer R) (M N : ZornMatrix) :
    realCrossProductStabilizerAction R (M * N) =
      (realCrossProductStabilizerAction R M) *
        (realCrossProductStabilizerAction R N) := by
  cases M with
  | mk a b x y =>
  cases N with
  | mk a' b' x' y' =>
      ext
      · simp [realCrossProductStabilizerAction, mul, hR.1]
      · simp [realCrossProductStabilizerAction, mul, hR.1]
      · simp [realCrossProductStabilizerAction, mul, hR.2]
      · simp [realCrossProductStabilizerAction, mul, hR.2]

/-!
## 6. Connection to Cl(1,1) Grading
-/

/-- 
Tripotent grading operator on Zorn matrices.
Extends the Cl(1,1) grading χ to the octonionic structure.
-/
def gradingOperator (M : ZornMatrix) : ZornMatrix :=
  ⟨0, 0, M.x, -M.y⟩

@[simp] theorem grading_sq (M : ZornMatrix) :
    gradingOperator (gradingOperator M) = ⟨0, 0, M.x, M.y⟩ := by
  simp [gradingOperator]

theorem grading_tripotent (M : ZornMatrix) :
    gradingOperator (gradingOperator (gradingOperator M)) = gradingOperator M := by
  ext <;> simp [gradingOperator, grading_sq]

/-- Eigenvalue +1 subspace: color triplets -/
def gradingEigenPlus : Set ZornMatrix := {M | gradingOperator M = M}

/-- Eigenvalue -1 subspace: color antitriplets -/
def gradingEigenMinus : Set ZornMatrix := {M | gradingOperator M = -M}

/-- Eigenvalue 0 subspace: diagonal scalars -/
def gradingEigenZero : Set ZornMatrix := {M | gradingOperator M = 0}

theorem eigenspace_decomposition (M : ZornMatrix) :
    ∃ (Mplus : ZornMatrix) (Mminus : ZornMatrix) (Mzero : ZornMatrix),
    Mplus ∈ gradingEigenPlus ∧ Mminus ∈ gradingEigenMinus ∧ Mzero ∈ gradingEigenZero ∧
    M = Mplus + Mminus + Mzero := by
  cases M with
  | mk a b x y =>
    refine
      ⟨⟨0, 0, x, fun _ : Fin 3 => 0⟩,
        ⟨0, 0, fun _ : Fin 3 => 0, y⟩,
        ⟨a, b, fun _ : Fin 3 => 0, fun _ : Fin 3 => 0⟩, ?_, ?_, ?_, ?_⟩
    · ext <;> simp [gradingOperator]
    · ext <;> simp [gradingOperator]
    · ext <;> simp [gradingOperator]
    · ext <;> simp [add, zero, Pi.add_apply, add_assoc, add_left_comm, add_comm]

/-!
## 7. Mersenne Hierarchy Connection (TODO)
-/

/-- 
Associate Cl(n,n) tower levels with Mersenne primes:
- n=1: M₂ = 3 (dimension of color space)
- n=2: ???
- n=3: M₃ = 7 (dimension of imaginary octonions)
- n=7: M₇ = 127 (??? )

This connects the discrete arithmetic hierarchy to the continuous
geometric representation structure.
-/
def mersenneDimension (n : ℕ) : ℕ :=
  2^n - 1

-- TODO: Prove connections between mersenneDimension and:
-- - dim(SU(3)) = 8
-- - dim(G₂) = 14
-- - 137 = 3 + 7 + 127 decomposition

end InfoGeometry.Physics.ZornMatrixSU3

-- [STITCHER: MISSING OVERLAP] --
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Clifford.Cl11CoordinateAlgebra
import InfoGeometry.Clifford.GammaMatrices

open Matrix

/-!
# InfoGeometry.Physics.ZornMatrixSU3

**Zorn Matrices, Split Octonions, and SU(3) Color Symmetry**

This file formalizes the Günaydin-Gürsey construction connecting:
1. Zorn's vector-matrix representation of octonions
2. Split octonions O_s with signature (4,4)
3. SU(3) as the stabilizer subgroup of G₂
4. Color triplet/antitriplet representations from off-diagonal vectors

## Mathematical Structure

A Zorn matrix has the form:
```
    [a   x⃗ ]
M = [       ]    where a,b ∈ ℝ, x⃗,y⃗ ∈ ℝ³
    [y⃗   b ]
```

Multiplication rule:
```
[a   x⃗ ] [a'  x⃗']   [aa' + x⃗·y⃗'    ax⃗' + a'x⃗ - y⃗×y⃗']
[y⃗   b ] [y⃗'  b'] = [ya' + b'y⃗ - x⃗×x⃗'    bb' + y⃗·x⃗'  ]
```

The split octonion norm is:
```
N(M) = ab - x⃗·y⃗
```

## Connection to Cl(1,1) and SU(3)

The diagonal projectors:
```
OP₁ = [1  0]    OP₂ = [0  0]
      [0  0]          [0  1]
```

Sandwiching isolates color modes:
```
OP₁ · M · OP₂ = [0  x⃗]    (color triplet 3)
                [0  0 ]

OP₂ · M · OP₁ = [0  0 ]    (color antitriplet 3̄)
                [y⃗ 0 ]
```

The G₂ automorphism group preserves this structure, with SU(3) ⊂ G₂
being the subgroup that fixes OP₁ and OP₂.

## Tripotent Eigenvalues and Anyonic Braiding

The grading operator χ from Cl(1,1) extends to the octonionic structure:
- Eigenvalue +1: quarks (fundamental 3)
- Eigenvalue -1: antiquarks (antifundamental 3̄)
- Eigenvalue 0: diagonal scalars (color singlets)

This Z₃ grading governs anyonic braiding in the color space.
-/

namespace InfoGeometry.Physics.ZornMatrixSU3

/-!
## 1. Vector Cross Product in ℝ³
-/

/-- Cross product in ℝ³ -/
def crossProduct (x y : Fin 3 → ℝ) : Fin 3 → ℝ := InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3 x y

/-- Dot product in ℝ³ -/
def dotProduct (x y : Fin 3 → ℝ) : ℝ := InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3 x y

theorem dotProduct_comm (x y : Fin 3 → ℝ) :
    dotProduct x y = dotProduct y x := by
  simpa [dotProduct] using
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3_comm x y

@[simp] theorem dotProduct_zero_left (x : Fin 3 → ℝ) :
    dotProduct (fun _ : Fin 3 => 0) x = 0 := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

@[simp] theorem dotProduct_zero_right (x : Fin 3 → ℝ) :
    dotProduct x (fun _ : Fin 3 => 0) = 0 := by
  simpa [dotProduct_comm] using dotProduct_zero_left x

@[simp] theorem dotProduct_zero_zero :
    dotProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = 0 := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

theorem dotProduct_add_left (x y z : Fin 3 → ℝ) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_add_right (x y z : Fin 3 → ℝ) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct (r • x) y = r * dotProduct x y := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct x (r • y) = r * dotProduct x y := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

@[simp] theorem crossProduct_zero_left (x : Fin 3 → ℝ) :
    crossProduct (fun _ : Fin 3 => 0) x = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_zero :
    crossProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_right (x : Fin 3 → ℝ) :
    crossProduct x (fun _ : Fin 3 => 0) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

theorem crossProduct_add_left (x y z : Fin 3 → ℝ) :
    crossProduct (x + y) z = crossProduct x z + crossProduct y z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_add_right (x y z : Fin 3 → ℝ) :
    crossProduct x (y + z) = crossProduct x y + crossProduct x z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct (r • x) y = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct x (r • y) = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_anticomm (x y : Fin 3 → ℝ) :
    crossProduct x y = -(crossProduct y x) := by
  ext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

@[simp] theorem crossProduct_self (x : Fin 3 → ℝ) :
    crossProduct x x = (0 : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

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
@[simp] theorem zero_x : (0 : ZornMatrix).x = (0 : Fin 3 → ℝ) := by
  rfl
@[simp] theorem zero_y : (0 : ZornMatrix).y = (0 : Fin 3 → ℝ) := by
  rfl

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
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_conj (M.a, M.b, M.x, M.y))

theorem norm_mul (M N : ZornMatrix) :
    norm (M * N) = norm M * norm N := by
  change
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm
      (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul
        (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y)) =
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (M.a, M.b, M.x, M.y) *
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (N.a, N.b, N.x, N.y)
  simpa [norm, dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul] using
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_mul
      (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y))


/-!
## 4. Diagonal Projectors and Color Decomposition
-/

/-- First diagonal projector (selects upper block) -/
def projector1 : ZornMatrix :=
  ⟨1, 0, fun _ => 0, fun _ => 0⟩

/-- Second diagonal projector (selects lower block) -/
def projector2 : ZornMatrix :=
  ⟨0, 1, fun _ => 0, fun _ => 0⟩

@[simp] lemma mul_projector1 (M : ZornMatrix) :
    projector1 * M = ⟨M.a, 0, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, dotProduct_zero_left, crossProduct_zero_left]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma mul_projector2 (M : ZornMatrix) :
    projector2 * M = ⟨0, M.b, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] lemma projector1_mul (M : ZornMatrix) :
    M * projector1 = ⟨M.a, 0, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, crossProduct_self]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma projector2_mul (M : ZornMatrix) :
    M * projector2 = ⟨0, M.b, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] theorem projector1_sq : projector1 * projector1 = projector1 := by
  ext
  · simp [projector1, mul]
  · simp [projector1, mul]
  · simp [projector1, mul, crossProduct_self]
  · simp [projector1, mul, crossProduct_self]

@[simp] theorem projector2_sq : projector2 * projector2 = projector2 := by
  ext
  · simp [projector2, mul]
  · simp [projector2, mul]
  · simp [projector2, mul, crossProduct_self]
  · simp [projector2, mul, crossProduct_self]

theorem projector1_projector2_orthogonal :
    projector1 * projector2 = zero ∧ projector2 * projector1 = zero := by
  constructor
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, dotProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]

theorem projector1_add_projector2 : projector1 + projector2 = one := by
  ext i <;> simp [projector1, projector2, one, add]

@[simp] theorem zero_mul_zorn (M : ZornMatrix) : (0 : ZornMatrix) * M = 0 := by
  cases M with
  | mk a b x y =>
      apply ext
      · change dotProduct (fun _ : Fin 3 => 0) y = 0
        exact dotProduct_zero_left y
      · change dotProduct (fun _ : Fin 3 => 0) x = 0
        exact dotProduct_zero_left x
      · change crossProduct (fun _ : Fin 3 => 0) y = 0
        exact crossProduct_zero_left y
      · change crossProduct (fun _ : Fin 3 => 0) x = 0
        exact crossProduct_zero_left x

@[simp] theorem mul_zero_zorn (M : ZornMatrix) : M * (0 : ZornMatrix) = 0 := by
  cases M with
  | mk a b x y =>
      apply ext
      · change dotProduct x (fun _ : Fin 3 => 0) = 0
        exact dotProduct_zero_right x
      · change dotProduct y (fun _ : Fin 3 => 0) = 0
        exact dotProduct_zero_right y
      · change crossProduct y (fun _ : Fin 3 => 0) = 0
        exact crossProduct_zero_right y
      · change crossProduct x (fun _ : Fin 3 => 0) = 0
        exact crossProduct_zero_right x

theorem add_mul_zorn (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by
  cases M <;> cases N <;> cases P <;>
  apply ext
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · funext i
    fin_cases i <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · funext i
    fin_cases i <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem mul_add_zorn (M N P : ZornMatrix) : M * (N + P) = M * N + M * P := by
  cases M <;> cases N <;> cases P <;>
  apply ext
  · funext i
    fin_cases i <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · funext i
    fin_cases i <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left, crossProduct_add_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem smul_mul_zorn (r : ℝ) (M N : ZornMatrix) : (r • M) * N = r • (M * N) := by
  cases M <;> cases N <;>
  apply ext
  · funext i
    fin_cases i <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · funext i
    fin_cases i <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem mul_smul_zorn (r : ℝ) (M N : ZornMatrix) : M * (r • N) = r • (M * N) := by
  cases M <;> cases N <;>
  apply ext
  · funext i
    fin_cases i <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring
  · funext i
    fin_cases i <;>
  apply ext <;>
  simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left, crossProduct_smul_right,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
  ring

@[simp] theorem one_mul_zorn (M : ZornMatrix) : (1 : ZornMatrix) * M = M := by
  cases M with
  | mk a b x y =>
      apply ext <;> simp [mul]

@[simp] theorem mul_one_zorn (M : ZornMatrix) : M * (1 : ZornMatrix) = M := by
  cases M with
  | mk a b x y =>
      · simp [mul]

/-- Color triplet extraction: OP₁ · M · OP₂ -/
def extractTriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector1 * M * projector2).x

/-- Color antitriplet extraction: OP₂ · M · OP₁ -/
def extractAntitriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector2 * M * projector1).y

/-- Diagonal scalar extraction -/
def extractScalars (M : ZornMatrix) : ℝ × ℝ :=
  ((projector1 * M * projector1).a, (projector2 * M * projector2).b)

theorem decomposition_theorem (M : ZornMatrix) :
    M = ⟨M.a, M.b, extractTriplet M, extractAntitriplet M⟩ := by
  have hx : extractTriplet M = M.x := by
    simp [extractTriplet, mul_projector1, mul_projector2, projector2_mul]
  have hy : extractAntitriplet M = M.y := by
    simp [extractAntitriplet, mul_projector2, projector1_mul]
  simp [hx, hy]

/-!
## 5. Real cross-product stabilizer
-/

/-- 
A real linear map on `ℝ³` that preserves both the dot product and the cross
product. This is the exact finite real stabilizer property used by the Zorn
multiplication proofs below; it is not a complex `SU(3)` formalization.
-/
def IsRealCrossProductStabilizer (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) : Prop :=
  (∀ x y, dotProduct (R x) (R y) = dotProduct x y) ∧
  (∀ x y, R (crossProduct x y) = crossProduct (R x) (R y))

/-- 
Action of a real cross-product stabilizer on a Zorn matrix.
The transformation rotates the color triplet and antitriplet
while leaving the diagonal scalars invariant.
-/
def realCrossProductStabilizerAction
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (M : ZornMatrix) : ZornMatrix :=
  ⟨M.a, M.b, R M.x, R M.y⟩

theorem realCrossProductStabilizerAction_preserves_norm
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hR : IsRealCrossProductStabilizer R) (M : ZornMatrix) :
    norm (realCrossProductStabilizerAction R M) = norm M := by
  simp [realCrossProductStabilizerAction, norm, dotProduct]
  exact hR.1 M.x M.y

theorem realCrossProductStabilizerAction_preserves_multiplication
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hR : IsRealCrossProductStabilizer R) (M N : ZornMatrix) :
    realCrossProductStabilizerAction R (M * N) =
      (realCrossProductStabilizerAction R M) *
        (realCrossProductStabilizerAction R N) := by
  cases M with
  | mk a b x y =>
  cases N with
  | mk a' b' x' y' =>
      ext
      · simp [realCrossProductStabilizerAction, hR.1]
      · simp [realCrossProductStabilizerAction, hR.1]
      · simp [realCrossProductStabilizerAction, hR.2]
      · simp [realCrossProductStabilizerAction, hR.2]

/-!
## 6. Connection to Cl(1,1) Grading
-/

/-- 
Tripotent grading operator on Zorn matrices.
Extends the Cl(1,1) grading χ to the octonionic structure.
-/
def gradingOperator (M : ZornMatrix) : ZornMatrix :=
  ⟨0, 0, M.x, -M.y⟩

@[simp] theorem grading_sq (M : ZornMatrix) :
    gradingOperator (gradingOperator M) = ⟨0, 0, M.x, M.y⟩ := by
  simp [gradingOperator]

theorem grading_tripotent (M : ZornMatrix) :
    gradingOperator (gradingOperator (gradingOperator M)) = gradingOperator M := by
  ext <;> simp [gradingOperator]

/-- Eigenvalue +1 subspace: color triplets -/
def gradingEigenPlus : Set ZornMatrix := {M | gradingOperator M = M}

/-- Eigenvalue -1 subspace: color antitriplets -/
def gradingEigenMinus : Set ZornMatrix := {M | gradingOperator M = -M}

/-- Eigenvalue 0 subspace: diagonal scalars -/
def gradingEigenZero : Set ZornMatrix := {M | gradingOperator M = 0}

theorem eigenspace_decomposition (M : ZornMatrix) :
    ∃ (Mplus : ZornMatrix) (Mminus : ZornMatrix) (Mzero : ZornMatrix),
    Mplus ∈ gradingEigenPlus ∧ Mminus ∈ gradingEigenMinus ∧ Mzero ∈ gradingEigenZero ∧
    M = Mplus + Mminus + Mzero := by
  cases M with
  | mk a b x y =>
    refine
      ⟨⟨0, 0, x, fun _ : Fin 3 => 0⟩,
        ⟨0, 0, fun _ : Fin 3 => 0, y⟩,
        ⟨a, b, fun _ : Fin 3 => 0, fun _ : Fin 3 => 0⟩, ?_, ?_, ?_, ?_⟩
    · ext <;> simp [gradingOperator]
    · ext <;> simp [gradingOperator]
    · ext <;> simp [gradingOperator]
    · ext <;> simp [Pi.add_apply, add_comm]

/-!
## 7. Mersenne Hierarchy Connection (TODO)
-/

/-- 
Associate Cl(n,n) tower levels with Mersenne primes:
- n=1: M₂ = 3 (dimension of color space)
- n=2: ???
- n=3: M₃ = 7 (dimension of imaginary octonions)
- n=7: M₇ = 127 (??? )

This connects the discrete arithmetic hierarchy to the continuous
geometric representation structure.
-/
def mersenneDimension (n : ℕ) : ℕ :=
  2^n - 1

-- TODO: Prove connections between mersenneDimension and:
-- - dim(SU(3)) = 8
-- - dim(G₂) = 14
-- - 137 = 3 + 7 + 127 decomposition

end InfoGeometry.Physics.ZornMatrixSU3

-- [STITCHER: MISSING OVERLAP] --
  simpa [norm, conjugate, dotProduct] using
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_conj (M.a, M.b, M.x, M.y))

theorem norm_mul (M N : ZornMatrix) :
    norm (M * N) = norm M * norm N := by
  change
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm
      (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul
        (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y)) =
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (M.a, M.b, M.x, M.y) *
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (N.a, N.b, N.x, N.y)
  simpa [norm, dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul] using
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_mul
      (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y))


/-!
## 4. Diagonal Projectors and Color Decomposition
-/

/-- First diagonal projector (selects upper block) -/
def projector1 : ZornMatrix :=
  ⟨1, 0, fun _ => 0, fun _ => 0⟩

/-- Second diagonal projector (selects lower block) -/
def projector2 : ZornMatrix :=
  ⟨0, 1, fun _ => 0, fun _ => 0⟩

@[simp] lemma mul_projector1 (M : ZornMatrix) :
    projector1 * M = ⟨M.a, 0, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, dotProduct_zero_left, crossProduct_zero_left]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma mul_projector2 (M : ZornMatrix) :
    projector2 * M = ⟨0, M.b, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] lemma projector1_mul (M : ZornMatrix) :
    M * projector1 = ⟨M.a, 0, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, crossProduct_self]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma projector2_mul (M : ZornMatrix) :
    M * projector2 = ⟨0, M.b, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] theorem projector1_sq : projector1 * projector1 = projector1 := by
  ext
  · simp [projector1, mul]
  · simp [projector1, mul]
  · simp [projector1, mul, crossProduct_self]
  · simp [projector1, mul, crossProduct_self]

@[simp] theorem projector2_sq : projector2 * projector2 = projector2 := by
  ext
  · simp [projector2, mul]
  · simp [projector2, mul]
  · simp [projector2, mul, crossProduct_self]
  · simp [projector2, mul, crossProduct_self]

theorem projector1_projector2_orthogonal :
    projector1 * projector2 = zero ∧ projector2 * projector1 = zero := by
  constructor
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, dotProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]

theorem projector1_add_projector2 : projector1 + projector2 = one := by
  ext i <;> simp [projector1, projector2, one, add]

@[simp] theorem zero_mul_zorn (M : ZornMatrix) : (0 : ZornMatrix) * M = 0 := by
  cases M <;> ext <;> simp [mul, zero, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

@[simp] theorem mul_zero_zorn (M : ZornMatrix) : M * (0 : ZornMatrix) = 0 := by
  cases M <;> ext <;> simp [mul, zero, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

theorem add_mul_zorn (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by
  cases M <;> cases N <;> cases P <;> ext <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left,
      crossProduct_add_right, dotProduct_comm] <;> ring

theorem mul_add_zorn (M N P : ZornMatrix) : M * (N + P) = M * N + M * P := by
  cases M <;> cases N <;> cases P <;> ext <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left,
      crossProduct_add_right, dotProduct_comm] <;> ring

theorem smul_mul_zorn (r : ℝ) (M N : ZornMatrix) : (r • M) * N = r • (M * N) := by
  cases M <;> cases N <;> ext <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left,
      crossProduct_smul_right] <;> ring

theorem mul_smul_zorn (r : ℝ) (M N : ZornMatrix) : M * (r • N) = r • (M * N) := by
  cases M <;> cases N <;> ext <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left,
      crossProduct_smul_right] <;> ring

@[simp] theorem one_mul_zorn (M : ZornMatrix) : (1 : ZornMatrix) * M = M := by
  cases M <;> ext <;> simp [mul, one, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

@[simp] theorem mul_one_zorn (M : ZornMatrix) : M * (1 : ZornMatrix) = M := by
  cases M <;> ext <;> simp [mul, one, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

/-- Color triplet extraction: OP₁ · M · OP₂ -/
def extractTriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector1 * M * projector2).x

/-- Color antitriplet extraction: OP₂ · M · OP₁ -/
def extractAntitriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector2 * M * projector1).y

/-- Diagonal scalar extraction -/
def extractScalars (M : ZornMatrix) : ℝ × ℝ :=
  ((projector1 * M * projector1).a, (projector2 * M * projector2).b)

@[simp] theorem extractTriplet_eq (M : ZornMatrix) : extractTriplet M = M.x := by
  cases M <;> simp [extractTriplet, mul, projector1, projector2]