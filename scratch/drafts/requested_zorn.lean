/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
<USER_REQUEST>
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Noncommutative Operator Zorn Algebra, Functorial Inductive Towers, and the Riccati Cocycle

This file formalizes Archetypes I–VII over an arbitrary noncommutative unital ring `A`:
1. `OpVec3 A`: 3-component operator vectors with noncommutative left/right scalar actions,
   inner dot pairing, and noncommutative cross product.
2. `OpZornMatrix A`: The non-associative Zorn matrix algebra over a noncommutative ring `A`.
3. Functoriality (`OpVec3.map`, `OpZornMatrix.map`) under ring homomorphisms `A →+* B` and
   inductive tower composition (`InductiveRingSystem`).
4. The noncommutative Zorn–Riccati operator `opZornRiccati`, its origin as the `(1,2)`-Peirce
   component of the moving frame `(U₊(-q) * X) * U₊(q)`, the exact Bruhat trifactor fixed point,
   the second-order Taylor cocycle expansion, and projective spinor ket/bra pairing invariance.
-/

universe u v w

namespace NoncommutativeZornAlgebra

/-! ## Archetype I: Noncommutative 3-Vector Space & Bilinear Operations -/

/-- A 3-vector with entries in an arbitrary (generally noncommutative) ring `A`. -/
@[ext]
structure OpVec3 (A : Type u) where
  x : A
  y : A
  z : A
  deriving DecidableEq, Repr

namespace OpVec3

variable {A : Type u} [Ring A]

instance : Zero (OpVec3 A) := ⟨⟨0, 0, 0⟩⟩
instance : Add (OpVec3 A) := ⟨fun v w => ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩⟩
instance : Neg (OpVec3 A) := ⟨fun v => ⟨-v.x, -v.y, -v.z⟩⟩
instance : Sub (OpVec3 A) := ⟨fun v w => ⟨v.x - w.x, v.y - w.y, v.z - w.z⟩⟩

@[simp] theorem zero_x : (0 : OpVec3 A).x = 0 := rfl
@[simp] theorem zero_y : (0 : OpVec3 A).y = 0 := rfl
@[simp] theorem zero_z : (0 : OpVec3 A).z = 0 := rfl

@[simp] theorem add_x (v w : OpVec3 A) : (v + w).x = v.x + w.x := rfl
@[simp] theorem add_y (v w : OpVec3 A) : (v + w).y = v.y + w.y := rfl
@[simp] theorem add_z (v w : OpVec3 A) : (v + w).z = v.z + w.z := rfl

@[simp] theorem neg_x (v : OpVec3 A) : (-v).x = -v.x := rfl
@[simp] theorem neg_y (v : OpVec3 A) : (-v).y = -v.y := rfl
@[simp] theorem neg_z (v : OpVec3 A) : (-v).z = -v.z := rfl

@[simp] theorem sub_x (v w : OpVec3 A) : (v - w).x = v.x - w.x := rfl
@[simp] theorem sub_y (v w : OpVec3 A) : (v - w).y = v.y - w.y := rfl
@[simp] theorem sub_z (v : OpVec3 A) (w : OpVec3 A) : (v - w).z = v.z - w.z := rfl

instance : AddCommGroup (OpVec3 A) where
  add_assoc a b c := by ext <;> exact add_assoc _ _ _
  zero_add a := by ext <;> exact zero_add _
  add_zero a := by ext <;> exact add_zero _
  neg_add_cancel a := by ext <;> exact neg_add_cancel _
  add_comm a b := by ext <;> exact add_comm _ _
  sub_eq_add_neg a b := by ext <;> exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Left scalar multiplication of an operator `a : A` on `v : OpVec3 A`. -/
def smulLeft (a : A) (v : OpVec3 A) : OpVec3 A :=
  ⟨a * v.x, a * v.y, a * v.z⟩

/-- Right scalar multiplication of an operator `b : A` on `v : OpVec3 A`. -/
def smulRight (v : OpVec3 A) (b : A) : OpVec3 A :=
  ⟨v.x * b, v.y * b, v.z * b⟩

/-- Noncommutative inner dot product `v · w = v.x * w.x + v.y * w.y + v.z * w.z`. -/
def dot (v w : OpVec3 A) : A :=
  v.x * w.x + v.y * w.y + v.z * w.z

/-- Noncommutative 3D cross product `v × w`. -/
def cross (v w : OpVec3 A) : OpVec3 A :=
  ⟨v.y * w.z - v.z * w.y,
   v.z * w.x - v.x * w.z,
   v.x * w.y - v.y * w.x⟩

@[simp] theorem dot_zero_left (v : OpVec3 A) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (v : OpVec3 A) : dot v 0 = 0 := by
  simp [dot]

@[simp] theorem cross_zero_left (v : OpVec3 A) : cross 0 v = 0 := by
  ext <;> simp [cross]

@[simp] theorem cross_zero_right (v : OpVec3 A) : cross v 0 = 0 := by
  ext <;> simp [cross]

@[simp] theorem smulLeft_zero (v : OpVec3 A) : smulLeft 0 v = 0 := by
  ext <;> simp [smulLeft]

@[simp] theorem smulRight_zero (v : OpVec3 A) : smulRight v 0 = 0 := by
  ext <;> simp [smulRight]

@[simp] theorem smulLeft_one (v : OpVec3 A) : smulLeft 1 v = v := by
  ext <;> simp [smulLeft]

@[simp] theorem smulRight_one (v : OpVec3 A) : smulRight v 1 = v := by
  ext <;> simp [smulRight]

theorem dot_add_left (u v w : OpVec3 A) :
    dot (u + v) w = dot u w + dot v w := by
  simp only [dot, add_x, add_y, add_z, right_distrib]
  abel

theorem dot_add_right (u v w : OpVec3 A) :
    dot u (v + w) = dot u v + dot u w := by
  simp only [dot, add_x, add_y, add_z, left_distrib]
  abel

theorem smulLeft_add (a : A) (v w : OpVec3 A) :
    smulLeft a (v + w) = smulLeft a v + smulLeft a w := by
  ext <;> simp [smulLeft, left_distrib]

theorem smulRight_add (v w : OpVec3 A) (b : A) :
    smulRight (v + w) b = smulRight v b + smulRight w b := by
  ext <;> simp [smulRight, right_distrib]

theorem add_smulRight (v : OpVec3 A) (a b : A) :
    smulRight v (a + b) = smulRight v a + smulRight v b := by
  ext <;> simp [smulRight, left_distrib]

theorem dot_smulRight_assoc (w v : OpVec3 A) (b : A) :
    dot w (smulRight v b) = dot w v * b := by
  simp only [dot, smulRight, right_distrib, mul_assoc]

theorem smulLeft_dot_assoc (a : A) (v w : OpVec3 A) :
    dot (smulLeft a v) w = a * dot v w := by
  simp only [dot, smulLeft, left_distrib, mul_assoc]

/-- Functorial lift of a ring homomorphism `f : A →+* B` to `OpVec3`. -/
def map {B : Type v} [Ring B] (f : A →+* B) (v : OpVec3 A) : OpVec3 B :=
  ⟨f v.x, f v.y, f v.z⟩

@[simp] theorem map_id (v : OpVec3 A) : map (RingHom.id A) v = v := by
  ext <;> rfl

theorem map_comp {B : Type v} {C : Type w} [Ring B] [Ring C]
    (g : B →+* C) (f : A →+* B) (v : OpVec3 A) :
    map (g.comp f) v = map g (map f v) := by
  ext <;> rfl

@[simp] theorem map_zero {B : Type v} [Ring B] (f : A →+* B) :
    map f (0 : OpVec3 A) = 0 := by
  ext <;> simp [map]

@[simp] theorem map_add {B : Type v} [Ring B] (f : A →+* B) (v w : OpVec3 A) :
    map f (v + w) = map f v + map f w := by
  ext <;> simp [map]

@[simp] theorem map_neg {B : Type v} [Ring B] (f : A →+* B) (v : OpVec3 A) :
    map f (-v) = -map f v := by
  ext <;> simp [map]

@[simp] theorem map_sub {B : Type v} [Ring B] (f : A →+* B) (v w : OpVec3 A) :
    map f (v - w) = map f v - map f w := by
  ext <;> simp [map]

@[simp] theorem map_smulLeft {B : Type v} [Ring B] (f : A →+* B) (a : A) (v : OpVec3 A) :
    map f (smulLeft a v) = smulLeft (f a) (map f v) := by
  ext <;> simp [map, smulLeft]

@[simp] theorem map_smulRight {B : Type v} [Ring B] (f : A →+* B) (v : OpVec3 A) (b : A) :
    map f (smulRight v b) = smulRight (map f v) (f b) := by
  ext <;> simp [map, smulRight]

@[simp] theorem map_dot {B : Type v} [Ring B] (f : A →+* B) (v w : OpVec3 A) :
    f (dot v w) = dot (map f v) (map f w) := by
  simp [map, dot]

@[simp] theorem map_cross {B : Type v} [Ring B] (f : A →+* B) (v w : OpVec3 A) :
    map f (cross v w) = cross (map f v) (map f w) := by
  ext <;> simp [map, cross]

end OpVec3

/-! ## Archetype II: The Non-Associative Operator Zorn Algebra `OpZornMatrix A` -/

/-- The 8-component Operator Zorn Matrix over a noncommutative ring `A`:
`[[a, v], [w, b]]` where `a, b : A` and `v, w : OpVec3 A`. -/
@[ext]
structure OpZornMatrix (A : Type u) where
  a : A
  v : OpVec3 A
  w : OpVec3 A
  b : A
  deriving DecidableEq, Repr

namespace OpZornMatrix

variable {A : Type u} [Ring A]

instance : Zero (OpZornMatrix A) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (OpZornMatrix A) := ⟨⟨1, 0, 0, 1⟩⟩
instance : Add (OpZornMatrix A) := ⟨fun X Y => ⟨X.a + Y.a, X.v + Y.v, X.w + Y.w, X.b + Y.b⟩⟩
instance : Neg (OpZornMatrix A) := ⟨fun X => ⟨-X.a, -X.v, -X.w, -X.b⟩⟩
instance : Sub (OpZornMatrix A) := ⟨fun X Y => ⟨X.a - Y.a, X.v - Y.v, X.w - Y.w, X.b - Y.b⟩⟩

/-- Non-associative Zorn matrix multiplication over a noncommutative ring `A`. -/
instance : Mul (OpZornMatrix A) := ⟨fun X Y =>
  ⟨X.a * Y.a + OpVec3.dot X.v Y.w,
   OpVec3.smulLeft X.a Y.v + OpVec3.smulRight X.v Y.b - OpVec3.cross X.w Y.w,
   OpVec3.smulRight X.w Y.a + OpVec3.smulLeft X.b Y.w + OpVec3.cross X.v Y.v,
   OpVec3.dot X.w Y.v + X.b * Y.b⟩⟩

@[simp] theorem mul_a (X Y : OpZornMatrix A) :
    (X * Y).a = X.a * Y.a + OpVec3.dot X.v Y.w := rfl
@[simp] theorem mul_v (X Y : OpZornMatrix A) :
    (X * Y).v = OpVec3.smulLeft X.a Y.v + OpVec3.smulRight X.v Y.b - OpVec3.cross X.w Y.w := rfl
@[simp] theorem mul_w (X Y : OpZornMatrix A) :
    (X * Y).w = OpVec3.smulRight X.w Y.a + OpVec3.smulLeft X.b Y.w + OpVec3.cross X.v Y.v := rfl
@[simp] theorem mul_b (X Y : OpZornMatrix A) :
    (X * Y).b = OpVec3.dot X.w Y.v + X.b * Y.b := rfl

instance : AddCommGroup (OpZornMatrix A) where
  add_assoc X Y Z := by ext <;> exact add_assoc _ _ _
  zero_add X := by ext <;> exact zero_add _
  add_zero X := by ext <;> exact add_zero _
  neg_add_cancel X := by ext <;> exact neg_add_cancel _
  add_comm X Y := by ext <;> exact add_comm _ _
  sub_eq_add_neg X Y := by ext <;> exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem one_mul (X : OpZornMatrix A) : (1 : OpZornMatrix A) * X = X := by
  ext <;> simp [One.one, Mul.mul, OpVec3.smulLeft, OpVec3.smulRight]

@[simp] theorem mul_one (X : OpZornMatrix A) : X * (1 : OpZornMatrix A) = X := by
  ext <;> simp [One.one, Mul.mul, OpVec3.smulLeft, OpVec3.smulRight]

/-- The associator `[X, Y, Z] = (X * Y) * Z - X * (Y * Z)` measuring non-associativity. -/
def associator (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  (X * Y) * Z - X * (Y * Z)

/-- Upper Peirce idempotent `e₁₁ = [[1, 0], [0, 0]]`. -/
def e11 : OpZornMatrix A := ⟨1, 0, 0, 0⟩

/-- Lower Peirce idempotent `e₂₂ = [[0, 0], [0, 1]]`. -/
def e22 : OpZornMatrix A := ⟨0, 0, 0, 1⟩

/-- Krein / Peirce grading involution `γ = e₁₁ - e₂₂ = [[1, 0], [0, -1]]`. -/
def opZornGamma : OpZornMatrix A := ⟨1, 0, 0, -1⟩

/-- Upper unipotent generator `U₊(v) = [[1, v], [0, 1]]`. -/
def UPlus (v : OpVec3 A) : OpZornMatrix A := ⟨1, v, 0, 1⟩

/-- Lower unipotent generator `U₋(w) = [[1, 0], [w, 1]]`. -/
def UMinus (w : OpVec3 A) : OpZornMatrix A := ⟨1, 0, w, 1⟩

/-- The Bruhat trifactor `T(w, v) = (U₋(w) * e₁₁) * U₊(v) = [[1, v], [w, w · v]]`. -/
def opBruhatTrifactor (w v : OpVec3 A) : OpZornMatrix A :=
  (UMinus w * e11) * UPlus v

theorem e11_idempotent : (e11 : OpZornMatrix A) * e11 = e11 := by
  ext <;> simp [e11, Mul.mul]

theorem e22_idempotent : (e22 : OpZornMatrix A) * e22 = e22 := by
  ext <;> simp [e22, Mul.mul]

theorem e11_add_e22 : (e11 : OpZornMatrix A) + e22 = 1 := by
  ext <;> simp [e11, e22, One.one, Add.add]

theorem opBruhatTrifactor_explicit (w v : OpVec3 A) :
    opBruhatTrifactor w v = ⟨1, v, w, OpVec3.dot w v⟩ := by
  ext <;> simp [opBruhatTrifactor, UMinus, UPlus, e11, Mul.mul]

/-! ## Archetype IV & V: The Noncommutative Zorn–Riccati Operator & Taylor Cocycle -/

/-- The 8D Noncommutative Zorn–Riccati Operator `ℛ_X(q)` on `OpVec3 A`:
`ℛ_X(q) = q ·_R (X.w · q) + q ·_R X.b - X.a ·_L q - X.v`. -/
def opZornRiccati (X : OpZornMatrix A) (q : OpVec3 A) : OpVec3 A :=
  OpVec3.smulRight q (OpVec3.dot X.w q) + OpVec3.smulRight q X.b
    - OpVec3.smulLeft X.a q - X.v

/-- The noncommutative Fréchet derivative (linearized tangent operator) of `ℛ_X` at `q`
applied to a perturbation `δ`:
`Dℛ_X(q)[δ] = q ·_R (X.w · δ) + δ ·_R (X.w · q + X.b) - X.a ·_L δ`. -/
def opZornRiccatiTangent (X : OpZornMatrix A) (q δ : OpVec3 A) : OpVec3 A :=
  OpVec3.smulRight q (OpVec3.dot X.w δ)
    + OpVec3.smulRight δ (OpVec3.dot X.w q + X.b)
    - OpVec3.smulLeft X.a δ

/-- **Theorem (Moving-Frame Peirce Origin of the Noncommutative Zorn–Riccati Operator):**
For any `X : OpZornMatrix A` and frame velocity `q : OpVec3 A`, the `(1,2)`-Peirce vector
component of the conjugated observable `(U₊(-q) * X) * U₊(q)` is `-ℛ_X(q)`. -/
theorem movingFrame_v_eq_neg_opZornRiccati (X : OpZornMatrix A) (q : OpVec3 A) :
    ((UPlus (-q) * X) * UPlus q).v = -opZornRiccati X q := by
  ext <;> simp [UPlus, opZornRiccati, OpVec3.smulLeft, OpVec3.smulRight,
    OpVec3.dot, OpVec3.cross] <;> abel

/-- **Theorem (Bruhat Trifactor Fixed-Point Theorem):**
For any `w, v : OpVec3 A`, the Bruhat trifactor `T = opBruhatTrifactor w v` is an exact zero
of the noncommutative Zorn–Riccati operator at `q = v`: `ℛ_T(v) = 0`. -/
theorem opZornRiccati_bruhatTrifactor_fixed_point (w v : OpVec3 A) :
    opZornRiccati (opBruhatTrifactor w v) v = 0 := by
  rw [opBruhatTrifactor_explicit]
  ext <;> simp [opZornRiccati, OpVec3.smulLeft, OpVec3.smulRight, OpVec3.dot] <;> abel

/-- **Theorem (Archetype XCII: Exact Noncommutative Riccati Shift / Taylor Cocycle Law):**
For any observable `X : OpZornMatrix A` and frame vectors `q, δ : OpVec3 A`, `ℛ_X(q + δ)`
expands around `ℛ_X(q)` as the sum of the base Riccati value, the noncommutative Fréchet
derivative `Dℛ_X(q)[δ]`, and the quadratic curvature `δ ·_R (X.w · δ)`. -/
theorem opZornRiccati_shift_cocycle (X : OpZornMatrix A) (q δ : OpVec3 A) :
    opZornRiccati X (q + δ) =
      opZornRiccati X q
        + opZornRiccatiTangent X q δ
        + OpVec3.smulRight δ (OpVec3.dot X.w δ) := by
  ext <;> simp [opZornRiccati, opZornRiccatiTangent, OpVec3.smulLeft,
    OpVec3.smulRight, OpVec3.dot, left_distrib, right_distrib] <;> abel

/-- **Corollary (Perturbation Expansion Around the Bruhat Trifactor Fixed Point):**
At the Bruhat trifactor fixed point `T = opBruhatTrifactor w v`, the constant term vanishes
and the shifted Riccati operator `ℛ_T(v + δ)` reduces purely to the tangent linearization plus
the quadratic curvature. -/
theorem opZornRiccati_bruhat_perturbation (w v δ : OpVec3 A) :
    opZornRiccati (opBruhatTrifactor w v) (v + δ) =
      opZornRiccatiTangent (opBruhatTrifactor w v) v δ
        + OpVec3.smulRight δ (OpVec3.dot w δ) := by
  rw [opZornRiccati_shift_cocycle, opZornRiccati_bruhatTrifactor_fixed_point, zero_add]
  rw [opBruhatTrifactor_explicit]

/-! ## Archetype VI: Functorial Lift `OpZornMatrix.map` & Inductive Colimit Intertwining -/

/-- Functorial lift of a ring homomorphism `f : A →+* B` to `OpZornMatrix`. -/
def map {B : Type v} [Ring B] (f : A →+* B) (X : OpZornMatrix A) : OpZornMatrix B :=
  ⟨f X.a, OpVec3.map f X.v, OpVec3.map f X.w, f X.b⟩

@[simp] theorem map_id (X : OpZornMatrix A) : map (RingHom.id A) X = X := by
  ext <;> rfl

theorem map_comp {B : Type v} {C : Type w} [Ring B] [Ring C]
    (g : B →+* C) (f : A →+* B) (X : OpZornMatrix A) :
    map (g.comp f) X = map g (map f X) := by
  ext <;> rfl

@[simp] theorem map_zero {B : Type v} [Ring B] (f : A →+* B) :
    map f (0 : OpZornMatrix A) = 0 := by
  ext <;> simp [map, Zero.zero]

@[simp] theorem map_one {B : Type v} [Ring B] (f : A →+* B) :
    map f (1 : OpZornMatrix A) = 1 := by
  ext <;> simp [map, One.one]

@[simp] theorem map_add {B : Type v} [Ring B] (f : A →+* B) (X Y : OpZornMatrix A) :
    map f (X + Y) = map f X + map f Y := by
  ext <;> simp [map, Add.add]

@[simp] theorem map_neg {B : Type v} [Ring B] (f : A →+* B) (X : OpZornMatrix A) :
    map f (-X) = -map f X := by
  ext <;> simp [map, Neg.neg]

@[simp] theorem map_sub {B : Type v} [Ring B] (f : A →+* B) (X Y : OpZornMatrix A) :
    map f (X - Y) = map f X - map f Y := by
  ext <;> simp [map, Sub.sub]

/-- **Theorem (Archetype XC: Functorial Preservation of Non-Associative Multiplication):**
Any ring homomorphism `f : A →+* B` induces a strict homomorphism of non-associative Zorn
algebras `OpZornMatrix.map f (X * Y) = OpZornMatrix.map f X * OpZornMatrix.map f Y`. -/
@[simp] theorem map_mul {B : Type v} [Ring B] (f : A →+* B) (X Y : OpZornMatrix A) :
    map f (X * Y) = map f X * map f Y := by
  ext <;> simp [map, Mul.mul]

/-- **Theorem (Functorial Preservation of the Non-Associative Associator):** -/
@[simp] theorem map_associator {B : Type v} [Ring B] (f : A →+* B) (X Y Z : OpZornMatrix A) :
    map f (associator X Y Z) = associator (map f X) (map f Y) (map f Z) := by
  simp [associator]

@[simp] theorem map_e11 {B : Type v} [Ring B] (f : A →+* B) :
    map f (e11 : OpZornMatrix A) = e11 := by
  ext <;> simp [map, e11]

@[simp] theorem map_e22 {B : Type v} [Ring B] (f : A →+* B) :
    map f (e22 : OpZornMatrix A) = e22 := by
  ext <;> simp [map, e22]

@[simp] theorem map_opZornGamma {B : Type v} [Ring B] (f : A →+* B) :
    map f (opZornGamma : OpZornMatrix A) = opZornGamma := by
  ext <;> simp [map, opZornGamma]

@[simp] theorem map_UPlus {B : Type v} [Ring B] (f : A →+* B) (v : OpVec3 A) :
    map f (UPlus v) = UPlus (OpVec3.map f v) := by
  ext <;> simp [map, UPlus]

@[simp] theorem map_UMinus {B : Type v} [Ring B] (f : A →+* B) (w : OpVec3 A) :
    map f (UMinus w) = UMinus (OpVec3.map f w) := by
  ext <;> simp [map, UMinus]

@[simp] theorem map_opBruhatTrifactor {B : Type v} [Ring B]
    (f : A →+* B) (w v : OpVec3 A) :
    map f (opBruhatTrifactor w v) =
      opBruhatTrifactor (OpVec3.map f w) (OpVec3.map f v) := by
  simp [opBruhatTrifactor]

/-- **Theorem (Archetype XC: Functorial Intertwining of the 8D Zorn–Riccati Operator):**
For every ring homomorphism `f : A →+* B`, `OpVec3.map f` intertwines `opZornRiccati`:
`OpVec3.map f (opZornRiccati X q) = opZornRiccati (OpZornMatrix.map f X) (OpVec3.map f q)`. -/
@[simp] theorem map_opZornRiccati {B : Type v} [Ring B]
    (f : A →+* B) (X : OpZornMatrix A) (q : OpVec3 A) :
    OpVec3.map f (opZornRiccati X q) =
      opZornRiccati (map f X) (OpVec3.map f q) := by
  simp [opZornRiccati, map]

/-! ## Archetype VII: Projective Spinor Kets/Bras & Gauge Invariance -/

/-- Projective Chevalley spinor ket `|Ψ(q)⟩ = U₋(q) * e₁₁ = [[1, 0], [q, 0]]`. -/
def spinorKet (q : OpVec3 A) : OpZornMatrix A :=
  UMinus q * e11

/-- Projective Chevalley spinor bra `⟨Ψ(p)| = e₁₁ * U₊(-p) = [[1, -p], [0, 0]]`. -/
def spinorBra (p : OpVec3 A) : OpZornMatrix A :=
  e11 * UPlus (-p)

theorem spinorKet_explicit (q : OpVec3 A) :
    spinorKet q = ⟨1, 0, q, 0⟩ := by
  ext <;> simp [spinorKet, UMinus, e11, Mul.mul]

theorem spinorBra_explicit (p : OpVec3 A) :
    spinorBra p = ⟨1, -p, 0, 0⟩ := by
  ext <;> simp [spinorBra, UPlus, e11, Mul.mul]

/-- **Theorem (Projective Spinor Contraction Formula):**
The inner contraction `⟨Ψ(p) | Ψ(q)⟩ = spinorBra p * spinorKet q` projects onto the upper
Peirce idempotent `e₁₁` scaled by the noncommutative affine pairing `1 - p · q`. -/
theorem spinorBra_mul_spinorKet (p q : OpVec3 A) :
    spinorBra p * spinorKet q = ⟨1 - OpVec3.dot p q, 0, 0, 0⟩ := by
  rw [spinorBra_explicit, spinorKet_explicit]
  ext <;> simp [Mul.mul, OpVec3.dot, sub_eq_add_neg]

/-- **Theorem (Archetype XCIII: Lower-Peirce Gauge Invariance of Spinor Kets):**
Right-multiplying a spinor ket by any lower-Peirce perturbation `⟨0, 0, w, b⟩` annihilates
the perturbation identically, leaving the ket strictly invariant under `1 + ⟨0, 0, w, b⟩`. -/
theorem spinorKet_right_gauge_invariant (q w : OpVec3 A) (b : A) :
    spinorKet q * (1 + ⟨0, 0, w, b⟩) = spinorKet q := by
  rw [spinorKet_explicit]
  ext <;> simp [One.one, Add.add, Mul.mul]

@[simp] theorem map_spinorKet {B : Type v} [Ring B] (f : A →+* B) (q : OpVec3 A) :
    map f (spinorKet q) = spinorKet (OpVec3.map f q) := by
  simp [spinorKet]

@[simp] theorem map_spinorBra {B : Type v} [Ring B] (f : A →+* B) (p : OpVec3 A) :
    map f (spinorBra p) = spinorBra (OpVec3.map f p) := by
  simp [spinorBra]

end OpZornMatrix

/-! ## Archetype XCI: Inductive Ring Systems & Direct-Limit Bonding Intertwiners -/

/-- A directed inductive tower of noncommutative rings `A 0 →+* A 1 →+* A 2 →+* ⋯`
equipped with coherent multi-step bonding homomorphisms `bond i j` for `i ≤ j`. -/
structure InductiveRingSystem where
  carrier : ℕ → Type u
  ringInst : ∀ n, Ring (carrier n)
  bond : ∀ {i j : ℕ}, i ≤ j → (carrier i →+* carrier j)
  bond_refl : ∀ i, bond (le_refl i) = RingHom.id (carrier i)
  bond_trans : ∀ {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k),
    bond (le_trans hij hjk) = (bond hjk).comp (bond hij)

attribute [instance] InductiveRingSystem.ringInst

namespace InductiveRingSystem

variable (S : InductiveRingSystem.{u})

/-- The induced bonding map on the non-associative Zorn algebra tower `OpZornMatrix (S.carrier i)`. -/
def zornBond {i j : ℕ} (hij : i ≤ j) :
    OpZornMatrix (S.carrier i) → OpZornMatrix (S.carrier j) :=
  OpZornMatrix.map (S.bond hij)

/-- The induced bonding map on the 3-vector tower `OpVec3 (S.carrier i)`. -/
def vecBond {i j : ℕ} (hij : i ≤ j) :
    OpVec3 (S.carrier i) → OpVec3 (S.carrier j) :=
  OpVec3.map (S.bond hij)

@[simp] theorem zornBond_refl (i : ℕ) (X : OpZornMatrix (S.carrier i)) :
    S.zornBond (le_refl i) X = X := by
  simp [zornBond, S.bond_refl]

theorem zornBond_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (X : OpZornMatrix (S.carrier i)) :
    S.zornBond (le_trans hij hjk) X = S.zornBond hjk (S.zornBond hij X) := by
  simp [zornBond, S.bond_trans, OpZornMatrix.map_comp]

/-- **Theorem (Archetype XCI: Inductive Tower Preservation of the Zorn–Riccati Cocycle):**
Across any multi-step transition `i ≤ j` in an inductive system of noncommutative rings,
the bonding maps `vecBond` and `zornBond` strictly intertwine the noncommutative Zorn–Riccati
operator and preserve the Bruhat trifactor fixed point at every stage of the tower. -/
theorem vecBond_intertwines_riccati {i j : ℕ} (hij : i ≤ j)
    (X : OpZornMatrix (S.carrier i)) (q : OpVec3 (S.carrier i)) :
    S.vecBond hij (OpZornMatrix.opZornRiccati X q) =
      OpZornMatrix.opZornRiccati (S.zornBond hij X) (S.vecBond hij q) := by
  simp [vecBond, zornBond]

theorem zornBond_preserves_bruhat_fixed_point {i j : ℕ} (hij : i ≤ j)
    (w v : OpVec3 (S.carrier i)) :
    OpZornMatrix.opZornRiccati
      (S.zornBond hij (OpZornMatrix.opBruhatTrifactor w v))
      (S.vecBond hij v) = 0 := by
  rw [← S.vecBond_intertwines_riccati hij]
  rw [OpZornMatrix.opZornRiccati_bruhatTrifactor_fixed_point]
  simp [vecBond]

end InductiveRingSystem

end NoncommutativeZornAlgebra
</USER_REQUEST>
<ADDITIONAL_METADATA>
The current local time is: 2026-10-26T21:17:11+02:00.
</ADDITIONAL_METADATA>
