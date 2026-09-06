import Mathlib.Tactic

/-!
# ℚ-based split-octonion carrier (Zorn coordinates)

Lightweight 8-coordinate carrier over ℚ for the Lane 1 Jordan-Cayley
inversion of `J₂(𝕆ₛ)`.  Provides only `norm` (the Zorn split-determinant),
`neg`, and `conj`; full nonassociative multiplication is intentionally
excluded so that the Lane 1 file follows the same minimal pattern as the
Cs and Hs files.

The norm `a·b - (x₀·y₀ + x₁·y₁ + x₂·y₂)` is the split (4,4) quadratic
form.  Combined with the Hermitian 2×2 determinant `ξ₊·ξ₋ - ‖Z‖²`, this
yields a coordinate model for a (5,5) quadratic form.

This file does **not** prove an analytic conformality theorem, a CCC
theorem, a global `Spin(5,5)` isomorphism, or an octonionic matrix
inverse theorem.
-/

namespace InfoGeometry.Algebra.SplitOctonionQ

/-- Eight-coordinate Zorn split-octonion cell over ℚ. -/
structure SplitO where
  a  : ℚ
  b  : ℚ
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  y0 : ℚ
  y1 : ℚ
  y2 : ℚ
  deriving DecidableEq, Repr

namespace SplitO

/-- Coordinatewise negation. -/
def neg (z : SplitO) : SplitO :=
  ⟨-z.a, -z.b, -z.x0, -z.x1, -z.x2, -z.y0, -z.y1, -z.y2⟩

def zero : SplitO := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

instance : Zero SplitO := ⟨zero⟩

def add (X Y : SplitO) : SplitO :=
    ⟨X.a + Y.a, X.b + Y.b, X.x0 + Y.x0, X.x1 + Y.x1, X.x2 + Y.x2,
      X.y0 + Y.y0, X.y1 + Y.y1, X.y2 + Y.y2⟩

instance : Add SplitO := ⟨add⟩

instance : Neg SplitO := ⟨neg⟩

def smul (c : ℚ) (X : SplitO) : SplitO :=
    ⟨c * X.a, c * X.b, c * X.x0, c * X.x1, c * X.x2,
      c * X.y0, c * X.y1, c * X.y2⟩

instance : SMul ℚ SplitO := ⟨smul⟩

@[simp] theorem zero_apply : (0 : SplitO) = zero := rfl
@[simp] theorem add_apply (X Y : SplitO) : X + Y = add X Y := rfl
@[simp] theorem smul_apply (c : ℚ) (X : SplitO) : c • X = smul c X := rfl

@[simp] theorem neg_eq_existing_neg (X : SplitO) : -X = neg X := rfl

@[ext] theorem ext {X Y : SplitO}
    (ha : X.a = Y.a) (hb : X.b = Y.b)
    (hx0 : X.x0 = Y.x0) (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2)
    (hy0 : X.y0 = Y.y0) (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) : X = Y := by
  cases X
  cases Y
  simp_all

instance : AddCommGroup SplitO where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc X Y Z := by ext <;> simp [add, add_assoc]
  zero_add X := by ext <;> simp [SplitO.zero, add]
  add_zero X := by ext <;> simp [SplitO.zero, add]
  neg_add_cancel X := by
    cases X
    simp [SplitO.zero, add, neg]
  add_comm X Y := by ext <;> simp [add, add_comm]

instance : Module ℚ SplitO where
  one_smul X := by ext <;> simp [smul]
  mul_smul c d X := by ext <;> simp [smul, mul_assoc]
  smul_zero c := by ext <;> simp [smul, zero]
  smul_add c X Y := by ext <;> simp [smul, add, mul_add]
  add_smul c d X := by ext <;> simp [smul, add, add_mul]
  zero_smul X := by ext <;> simp [smul, SplitO.zero]

/--
Correct split-octonion conjugation `conj(a, x; y, b) = (b, -x; -y, a)`.

This satisfies the alternative property `Z·conj(Z) = ‖Z‖²·1`.
-/
def conj (z : SplitO) : SplitO :=
  ⟨z.b, z.a, -z.x0, -z.x1, -z.x2, -z.y0, -z.y1, -z.y2⟩

@[simp] theorem conj_add (X Y : SplitO) :
    conj (X + Y) = conj X + conj Y := by
  cases X
  cases Y
  simp [conj, add, add_comm]

@[simp] theorem conj_smul (c : ℚ) (X : SplitO) :
    conj (c • X) = c • conj X := by
  cases X
  simp [conj, smul]

/-- Zorn split-norm: the (4,4) quadratic form. -/
def norm (z : SplitO) : ℚ :=
  z.a * z.b - (z.x0 * z.y0 + z.x1 * z.y1 + z.x2 * z.y2)

/-! ## Explicit `(4,4)` coordinates -/

/-- Null-to-orthogonal coordinates for the split-octonion Zorn block. -/
def toVec44 (z : SplitO) : Fin 8 → ℚ :=
  ![(z.a + z.b) / 2,
    (z.x0 + z.y0) / 2,
    (z.x1 + z.y1) / 2,
    (z.x2 + z.y2) / 2,
    (z.a - z.b) / 2,
    (z.x0 - z.y0) / 2,
    (z.x1 - z.y1) / 2,
    (z.x2 - z.y2) / 2]

/-- Inverse coordinate map for the null-to-orthogonal `(4,4)` coordinates. -/
def ofVec44 (v : Fin 8 → ℚ) : SplitO :=
  { a := v 0 + v 4
    b := v 0 - v 4
    x0 := v 1 + v 5
    y0 := v 1 - v 5
    x1 := v 2 + v 6
    y1 := v 2 - v 6
    x2 := v 3 + v 7
    y2 := v 3 - v 7 }

@[simp] theorem ofVec44_toVec44 (z : SplitO) :
    ofVec44 (toVec44 z) = z := by
  cases z
  apply SplitO.ext <;>
    simp [ofVec44, toVec44] <;>
    ring

@[simp] theorem toVec44_ofVec44 (v : Fin 8 → ℚ) :
    toVec44 (ofVec44 v) = v := by
  funext i
  fin_cases i <;>
    simp [ofVec44, toVec44]

def vec44Equiv : SplitO ≃ (Fin 8 → ℚ) where
  toFun := toVec44
  invFun := ofVec44
  left_inv := ofVec44_toVec44
  right_inv := toVec44_ofVec44

/-- The diagonal `(4,4)` quadratic form on the Zorn coordinates. -/
def q44 (v : Fin 8 → ℚ) : ℚ :=
  v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 -
    v 4 ^ 2 + v 5 ^ 2 + v 6 ^ 2 + v 7 ^ 2

theorem norm_eq_q44_toVec44 (z : SplitO) :
    norm z = q44 (toVec44 z) := by
  simp [norm, q44, toVec44]
  ring

@[simp] theorem norm_ofVec44 (v : Fin 8 → ℚ) :
    norm (ofVec44 v) = q44 v := by
  rw [norm_eq_q44_toVec44]
  simp

theorem norm_smul (c : ℚ) (X : SplitO) :
    norm (c • X) = c ^ 2 * norm X := by
  simp [norm, smul]
  ring

/-- Conjugation is an involution. -/
theorem conj_conj (z : SplitO) : conj (conj z) = z := by
  cases z; simp [conj]

/-- The norm is invariant under conjugation. -/
theorem norm_conj (z : SplitO) : norm (conj z) = norm z := by
  cases z; simp [conj, norm]; ring

/-- The norm equals the (4,4) quadratic form in diagonal coordinates. -/
theorem norm_eq_quadratic (z : SplitO) (p q u0 u1 u2 v0 v1 v2 : ℚ)
    (ha : z.a = q + v0) (hb : z.b = q - v0)
    (hx0 : z.x0 = u0 + v1) (hy0 : z.y0 = u0 - v1)
    (hx1 : z.x1 = u1 + v2) (hy1 : z.y1 = u1 - v2)
    (hx2 : z.x2 = u2 + p) (hy2 : z.y2 = u2 - p) :
    z.norm = q ^ 2 + p ^ 2 + v1 ^ 2 + v2 ^ 2 - v0 ^ 2 - u0 ^ 2 - u1 ^ 2 - u2 ^ 2 := by
  simp [norm, ha, hb, hx0, hy0, hx1, hy1, hx2, hy2]; ring_nf

end SplitO

end InfoGeometry.Algebra.SplitOctonionQ
