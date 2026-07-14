import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Explicit Zorn vector matrices

This file gives a coordinate-only real Zorn vector-matrix model.  The carrier is
the product type

`Real × Real × (Fin 3 → Real) × (Fin 3 → Real)`.

The reduced norm is `a*b - x·y`.  The central checked identity is the quadratic
rank equation

`X*X - Tr(X) X + N(X) 1 = 0`.

This is the finite algebraic readout behind the split-octonion light-cone
language.  It is not ordinary associative matrix multiplication.
-/

namespace ZornVectorMatrixExplicit

abbrev Vec3 : Type :=
  Fin 3 → ℝ

abbrev ZornCoord : Type :=
  ℝ × ℝ × Vec3 × Vec3

def zornA (z : ZornCoord) : ℝ :=
  z.1

def zornB (z : ZornCoord) : ℝ :=
  z.2.1

def zornX (z : ZornCoord) : Vec3 :=
  z.2.2.1

def zornY (z : ZornCoord) : Vec3 :=
  z.2.2.2

def dot3 (u v : Vec3) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross3 (u v : Vec3) : Vec3 :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

def zornMk (a b : ℝ) (x y : Vec3) : ZornCoord :=
  (a, b, x, y)

def zornOne : ZornCoord :=
  zornMk 1 1 0 0

def zornTrace (z : ZornCoord) : ℝ :=
  zornA z + zornB z

def zornNorm (z : ZornCoord) : ℝ :=
  zornA z * zornB z - dot3 (zornX z) (zornY z)

def zornConj (z : ZornCoord) : ZornCoord :=
  zornMk (zornB z) (zornA z) (-(zornX z)) (-(zornY z))

def zornMul (p q : ZornCoord) : ZornCoord :=
  zornMk
    (zornA p * zornA q + dot3 (zornX p) (zornY q))
    (zornB p * zornB q + dot3 (zornY p) (zornX q))
    (zornA p • zornX q + zornB q • zornX p - cross3 (zornY p) (zornY q))
    (zornB p • zornY q + zornA q • zornY p + cross3 (zornX p) (zornX q))

/-- Diagonal scalar copy inside the Zorn vector-matrix carrier. -/
def scalarZorn (a : ℝ) : ZornCoord :=
  zornMk a a 0 0

/--
Paravector-style real slice inside the Zorn vector-matrix carrier.

The sign convention `y = -x` makes this four-dimensional slice closed under
the coordinate Zorn product below.
-/
def paravectorZorn (a : ℝ) (x : Vec3) : ZornCoord :=
  zornMk a a x (-x)

/-- Upper off-diagonal vector block. -/
def upperVectorZorn (x : Vec3) : ZornCoord :=
  zornMk 0 0 x 0

/-- Lower off-diagonal vector block. -/
def lowerVectorZorn (y : Vec3) : ZornCoord :=
  zornMk 0 0 0 y

def IsZornNull (z : ZornCoord) : Prop :=
  zornNorm z = 0

@[simp] theorem zornA_mk (a b : ℝ) (x y : Vec3) :
    zornA (zornMk a b x y) = a := by
  rfl

@[simp] theorem zornA_tuple (a b : ℝ) (x y : Vec3) :
    zornA (a, b, x, y) = a := by
  rfl

@[simp] theorem zornB_mk (a b : ℝ) (x y : Vec3) :
    zornB (zornMk a b x y) = b := by
  rfl

@[simp] theorem zornB_tuple (a b : ℝ) (x y : Vec3) :
    zornB (a, b, x, y) = b := by
  rfl

@[simp] theorem zornX_mk (a b : ℝ) (x y : Vec3) :
    zornX (zornMk a b x y) = x := by
  rfl

@[simp] theorem zornX_tuple (a b : ℝ) (x y : Vec3) :
    zornX (a, b, x, y) = x := by
  rfl

@[simp] theorem zornY_mk (a b : ℝ) (x y : Vec3) :
    zornY (zornMk a b x y) = y := by
  rfl

@[simp] theorem zornY_tuple (a b : ℝ) (x y : Vec3) :
    zornY (a, b, x, y) = y := by
  rfl

theorem dot3_comm (u v : Vec3) :
    dot3 u v = dot3 v u := by
  unfold dot3
  ring

theorem cross3_self (u : Vec3) :
    cross3 u u = 0 := by
  funext i
  fin_cases i <;> simp [cross3] <;> ring

@[simp] theorem vecHead_eq (v : Vec3) : Matrix.vecHead v = v 0 := by
  rfl

@[simp] theorem vecHead_tail_eq (v : Vec3) :
    Matrix.vecHead (Matrix.vecTail v) = v 1 := by
  rfl

@[simp] theorem vecHead_tail_tail_eq (v : Vec3) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) = v 2 := by
  rfl

@[simp] theorem vecHead_smul (a : ℝ) (v : Vec3) :
    Matrix.vecHead (a • v) = a * Matrix.vecHead v := by
  rfl

@[simp] theorem vecHead_tail_smul (a : ℝ) (v : Vec3) :
    Matrix.vecHead (Matrix.vecTail (a • v)) =
      a * Matrix.vecHead (Matrix.vecTail v) := by
  rfl

@[simp] theorem vecHead_tail_tail_smul (a : ℝ) (v : Vec3) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (a • v))) =
      a * Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) := by
  rfl

theorem scalarZorn_eq_paravectorZorn_zero (a : ℝ) :
    scalarZorn a = paravectorZorn a 0 := by
  ext i <;> simp [scalarZorn, paravectorZorn, zornMk]

theorem zornOne_eq_scalarZorn_one :
    zornOne = scalarZorn 1 := by
  rfl

theorem zornOne_eq_paravectorZorn_one_zero :
    zornOne = paravectorZorn 1 0 := by
  ext i <;> simp [zornOne, paravectorZorn, zornMk]

/--
The paravector slice is closed under the coordinate Zorn product.

This is a finite algebraic statement about the chosen real slice.  It is not a
Frobenius classification theorem and it is not a slice-regularity theorem.
-/
theorem zornMul_paravectorZorn
    (a b : ℝ) (x y : Vec3) :
    zornMul (paravectorZorn a x) (paravectorZorn b y) =
      paravectorZorn (a * b - dot3 x y) (a • y + b • x - cross3 x y) := by
  ext i <;>
    simp [zornMul, paravectorZorn, zornMk, zornA, zornB, zornX, zornY, dot3, cross3]
  · ring
  · ring
  · fin_cases i <;> simp <;> ring_nf

theorem upperVectorZorn_square_zero (x : Vec3) :
    zornMul (upperVectorZorn x) (upperVectorZorn x) = 0 := by
  ext <;>
    simp [upperVectorZorn, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3,
      cross3_self]

theorem lowerVectorZorn_square_zero (y : Vec3) :
    zornMul (lowerVectorZorn y) (lowerVectorZorn y) = 0 := by
  ext <;>
    simp [lowerVectorZorn, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3,
      cross3_self]

theorem upperVectorZorn_mul_lowerVectorZorn (x y : Vec3) :
    zornMul (upperVectorZorn x) (lowerVectorZorn y) =
      zornMk (dot3 x y) 0 0 0 := by
  ext i <;>
    simp [upperVectorZorn, lowerVectorZorn, zornMul, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3] <;>
    try fin_cases i <;>
    simp

theorem lowerVectorZorn_mul_upperVectorZorn (x y : Vec3) :
    zornMul (lowerVectorZorn y) (upperVectorZorn x) =
      zornMk 0 (dot3 y x) 0 0 := by
  ext i <;>
    simp [upperVectorZorn, lowerVectorZorn, zornMul, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3] <;>
    try fin_cases i <;>
    simp

/--
The upper/lower rank-one blocks have scalar anticommutator: this is the explicit
finite Zorn analogue of the contraction readback.
-/
theorem upperLower_add_lowerUpper_scalar (x y : Vec3) :
    zornMul (upperVectorZorn x) (lowerVectorZorn y) +
      zornMul (lowerVectorZorn y) (upperVectorZorn x) =
    scalarZorn (dot3 x y) := by
  rw [upperVectorZorn_mul_lowerVectorZorn, lowerVectorZorn_mul_upperVectorZorn]
  ext i <;> simp [scalarZorn, zornMk, dot3_comm]

/--
The upper/lower rank-one block commutator is diagonal with opposite scalar
entries `± dot3 x y`.
-/
theorem upperLower_sub_lowerUpper_diag (x y : Vec3) :
    zornMul (upperVectorZorn x) (lowerVectorZorn y) -
      zornMul (lowerVectorZorn y) (upperVectorZorn x) =
    zornMk (dot3 x y) (-(dot3 x y)) 0 0 := by
  rw [upperVectorZorn_mul_lowerVectorZorn, lowerVectorZorn_mul_upperVectorZorn]
  ext i <;> simp [zornMk, dot3_comm]

theorem zornTrace_conj (z : ZornCoord) :
    zornTrace (zornConj z) = zornTrace z := by
  rcases z with ⟨a, b, x, y⟩
  simp [zornConj, zornTrace, zornMk, zornA, zornB]
  ring

theorem zornNorm_conj (z : ZornCoord) :
    zornNorm (zornConj z) = zornNorm z := by
  rcases z with ⟨a, b, x, y⟩
  simp [zornConj, zornNorm, zornMk, zornA, zornB, zornX, zornY, dot3]
  ring

theorem isZornNull_iff_norm_eq_zero (z : ZornCoord) :
    IsZornNull z ↔ zornNorm z = 0 := by
  rfl

theorem zornMul_self_quadratic_rank (z : ZornCoord) :
    zornMul z z - zornTrace z • z + zornNorm z • zornOne = 0 := by
  rcases z with ⟨a, b, x, y⟩
  ext <;>
    simp [zornMul, zornOne, zornTrace, zornNorm, zornMk, zornA, zornB, zornX,
      zornY, dot3, cross3_self] <;>
    ring

/--
The reduced Zorn norm is multiplicative on the explicit coordinate carrier.

This is the local composition law for the split-octonion shadow.
-/
theorem zornNorm_mul (p q : ZornCoord) :
    zornNorm (zornMul p q) = zornNorm p * zornNorm q := by
  rcases p with ⟨a, b, x, y⟩
  rcases q with ⟨c, d, u, v⟩
  unfold zornMul zornNorm zornA zornB zornX zornY zornMk
  simp [dot3, cross3]
  ring_nf

/-- The positive diagonal projector in the Zorn carrier. -/
def pPlus : ZornCoord :=
  zornMk 1 0 0 0

/-- The negative diagonal projector in the Zorn carrier. -/
def pMinus : ZornCoord :=
  zornMk 0 1 0 0

@[simp] theorem pPlus_isNull : IsZornNull pPlus := by
  change 1 * 0 - (0 * 0 + 0 * 0 + 0 * 0) = 0
  ring

@[simp] theorem pMinus_isNull : IsZornNull pMinus := by
  change 0 * 1 - (0 * 0 + 0 * 0 + 0 * 0) = 0
  ring

theorem pPlus_ne_zero : pPlus ≠ 0 := by
  intro h
  have h' := congrArg (fun z : ZornCoord => z.1) h
  simp [pPlus, zornMk] at h'

theorem pMinus_ne_zero : pMinus ≠ 0 := by
  intro h
  have h' := congrArg (fun z : ZornCoord => z.2.1) h
  simp [pMinus, zornMk] at h'

@[simp] theorem zornNorm_pPlus : zornNorm pPlus = 0 :=
  pPlus_isNull

@[simp] theorem zornNorm_pMinus : zornNorm pMinus = 0 :=
  pMinus_isNull

/-- The explicit Zorn coordinate carrier has a nonzero split-null element. -/
theorem exists_nonzero_zorn_null_coord : ∃ z : ZornCoord, z ≠ 0 ∧ IsZornNull z :=
  ⟨pPlus, pPlus_ne_zero, pPlus_isNull⟩

theorem pPlus_add_pMinus : pPlus + pMinus = zornOne := by
  ext <;> simp [pPlus, pMinus, zornOne, zornMk]

theorem pPlus_mul_pMinus : zornMul pPlus pMinus = 0 := by
  ext <;>
    simp [pPlus, pMinus, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3]
  · rename_i i
    fin_cases i <;> simp
  · rename_i i
    fin_cases i <;> simp

theorem pMinus_mul_pPlus : zornMul pMinus pPlus = 0 := by
  ext <;>
    simp [pPlus, pMinus, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3]
  · rename_i i
    fin_cases i <;> simp
  · rename_i i
    fin_cases i <;> simp

/--
The two diagonal Zorn idempotents give an explicit split-null pair: each is nonzero,
each has reduced norm zero, and together they resolve the Zorn unit.
-/
theorem split_null_projector_pair :
    pPlus ≠ 0 ∧ pMinus ≠ 0 ∧ IsZornNull pPlus ∧ IsZornNull pMinus ∧
      pPlus + pMinus = zornOne :=
  ⟨pPlus_ne_zero, pMinus_ne_zero, pPlus_isNull, pMinus_isNull, pPlus_add_pMinus⟩

end ZornVectorMatrixExplicit
