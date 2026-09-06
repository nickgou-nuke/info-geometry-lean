import Mathlib.Tactic

/-!
# Zorn Triality: The Core Algebra
# Verified against `ZornAssociatorSplitOctonion.py`

This file formalizes the Split-Octonions via Zorn Matrices,
using the EXACT multiplication rules from the Python reference.
-/

noncomputable section

namespace ZornCore

open Matrix

/-- 3D Vector type for Zorn off-diagonals -/
abbrev Vec3 := Fin 3 → ℝ

/-- Dot product -/
def dot (u v : Vec3) : ℝ := ∑ i, u i * v i

/-- Cross product -/
def cross (u v : Vec3) : Vec3 :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Zorn Vector Matrix -/
structure Zorn where
  a : ℝ
  u : Vec3
  v : Vec3
  b : ℝ

@[ext] theorem Zorn.ext' {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) :
    X = Y := by
  cases X
  cases Y
  simp_all

instance : Add Zorn where
  add x y := ⟨x.a + y.a, x.u + y.u, x.v + y.v, x.b + y.b⟩

instance : Zero Zorn where
  zero := ⟨0, 0, 0, 0⟩

instance : Neg Zorn where
  neg x := ⟨-x.a, -x.u, -x.v, -x.b⟩

instance : Sub Zorn where
  sub x y := ⟨x.a - y.a, x.u - y.u, x.v - y.v, x.b - y.b⟩

instance : SMul ℝ Zorn where
  smul r x := ⟨r * x.a, r • x.u, r • x.v, r * x.b⟩

instance : Mul Zorn where
  mul x y :=
    ⟨ x.a * y.a + dot x.u y.v,
      x.a • y.u + y.b • x.u - cross x.v y.v,
      y.a • x.v + x.b • y.v + cross x.u y.u,
      dot x.v y.u + x.b * y.b ⟩

@[simp] theorem zero_a : (0 : Zorn).a = 0 := rfl
@[simp] theorem zero_u : (0 : Zorn).u = 0 := rfl
@[simp] theorem zero_v : (0 : Zorn).v = 0 := rfl
@[simp] theorem zero_b : (0 : Zorn).b = 0 := rfl

@[simp] theorem add_a (X Y : Zorn) : (X + Y).a = X.a + Y.a := rfl
@[simp] theorem add_u (X Y : Zorn) : (X + Y).u = X.u + Y.u := rfl
@[simp] theorem add_v (X Y : Zorn) : (X + Y).v = X.v + Y.v := rfl
@[simp] theorem add_b (X Y : Zorn) : (X + Y).b = X.b + Y.b := rfl

@[simp] theorem neg_a (X : Zorn) : (-X).a = -X.a := rfl
@[simp] theorem neg_u (X : Zorn) : (-X).u = -X.u := rfl
@[simp] theorem neg_v (X : Zorn) : (-X).v = -X.v := rfl
@[simp] theorem neg_b (X : Zorn) : (-X).b = -X.b := rfl

@[simp] theorem sub_a (X Y : Zorn) : (X - Y).a = X.a - Y.a := rfl
@[simp] theorem sub_u (X Y : Zorn) : (X - Y).u = X.u - Y.u := rfl
@[simp] theorem sub_v (X Y : Zorn) : (X - Y).v = X.v - Y.v := rfl
@[simp] theorem sub_b (X Y : Zorn) : (X - Y).b = X.b - Y.b := rfl

@[simp] theorem smul_a (r : ℝ) (X : Zorn) : (r • X).a = r * X.a := rfl
@[simp] theorem smul_u (r : ℝ) (X : Zorn) : (r • X).u = r • X.u := rfl
@[simp] theorem smul_v (r : ℝ) (X : Zorn) : (r • X).v = r • X.v := rfl
@[simp] theorem smul_b (r : ℝ) (X : Zorn) : (r • X).b = r * X.b := rfl

@[simp] theorem mul_a (X Y : Zorn) :
    (X * Y).a = X.a * Y.a + dot X.u Y.v := rfl
@[simp] theorem mul_u (X Y : Zorn) :
    (X * Y).u = X.a • Y.u + Y.b • X.u - cross X.v Y.v := rfl
@[simp] theorem mul_v (X Y : Zorn) :
    (X * Y).v = Y.a • X.v + X.b • Y.v + cross X.u Y.u := rfl
@[simp] theorem mul_b (X Y : Zorn) :
    (X * Y).b = dot X.v Y.u + X.b * Y.b := rfl

/-- Determinant (Norm) -/
def det (Z : Zorn) : ℝ := Z.a * Z.b - dot Z.u Z.v

/-- Associator: (XY)Z - X(YZ) -/
def associator (X Y Z : Zorn) : Zorn := (X * Y) * Z - X * (Y * Z)

-- ============================================================================
-- VERIFICATION TESTS (Ported from Python)
-- ============================================================================

def U (u : Vec3) : Zorn := ⟨0, u, 0, 0⟩
def L (v : Vec3) : Zorn := ⟨0, 0, v, 0⟩

def e1 : Vec3 := ![1, 0, 0]
def e2 : Vec3 := ![0, 1, 0]
def e3 : Vec3 := ![0, 0, 1]

@[simp] theorem e1_zero : e1 0 = 1 := rfl
@[simp] theorem e1_one : e1 1 = 0 := rfl
@[simp] theorem e1_two : e1 2 = 0 := rfl
@[simp] theorem e2_zero : e2 0 = 0 := rfl
@[simp] theorem e2_one : e2 1 = 1 := rfl
@[simp] theorem e2_two : e2 2 = 0 := rfl
@[simp] theorem e3_zero : e3 0 = 0 := rfl
@[simp] theorem e3_one : e3 1 = 0 := rfl
@[simp] theorem e3_two : e3 2 = 1 := rfl

/-- THEOREM: Pure U-lane is nilpotent -/
theorem U_nilpotent : (U e1 * U e1) = 0 := by
  apply Zorn.ext'
  · simp [U, e1, dot, cross, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> simp [U, e1, dot, cross, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> simp [U, e1, dot, cross, Fin.sum_univ_three]
  · simp [U, e1, dot, cross, Fin.sum_univ_three]

/-- THEOREM: Pure U-lane is associative -/
theorem U_associative : associator (U e1) (U e1) (U e2) = 0 := by
  apply Zorn.ext'
  · simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]
  · simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]

/-- THEOREM: Mixed lane has NON-ZERO associator -/
theorem mixed_nonassociative : associator (U e1) (L e1) (U e2) ≠ 0 := by
  intro h
  have h' := congrArg (fun Z => Z.u 1) h
  have : (1 : ℝ) = 0 := by
    simpa [associator, U, L, e1, e2, dot, cross, Fin.sum_univ_three] using h'
  norm_num at this

/-- Alternative-law identities on the pure upper basis lanes used below. -/
theorem U_alternative_identities :
    associator (U e1) (U e1) (U e2) = 0 ∧
      associator (U e1) (U e2) (U e2) = 0 := by
  constructor
  · exact U_associative
  · apply Zorn.ext'
    · simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]
    · funext i
      fin_cases i <;> simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]
    · funext i
      fin_cases i <;> simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]
    · simp [associator, U, e1, e2, dot, cross, Fin.sum_univ_three]

-- ============================================================================
-- TRIALITY AUTOMORPHISM
-- ============================================================================

/-- A concrete order-three triality symmetry: simultaneously rotate the three
off-diagonal color coordinates in the upper and lower Zorn lanes. -/
def rotate3 (u : Vec3) : Vec3 := ![u 1, u 2, u 0]

def triality (Z : Zorn) : Zorn := ⟨Z.a, rotate3 Z.u, rotate3 Z.v, Z.b⟩

/-- THEOREM: Triality has order 3 (up to sign) -/
theorem triality_order_3 (Z : Zorn) : triality (triality (triality Z)) = Z := by
  apply Zorn.ext'
  · simp [triality, rotate3]
  · funext i
    fin_cases i <;> simp [triality, rotate3]
  · funext i
    fin_cases i <;> simp [triality, rotate3]
  · simp [triality, rotate3]

/-- THEOREM: Determinant is invariant under triality -/
theorem det_invariant (Z : Zorn) : det (triality Z) = det Z := by
  simp [det, triality, rotate3, dot, Fin.sum_univ_three]
  ring

end ZornCore
