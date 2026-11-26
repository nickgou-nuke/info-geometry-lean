/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CompactOctonion
import InfoGeometry.Algebra.H3ZornJordanInstance
import Mathlib.Algebra.Jordan.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Compact Albert Jordan Algebra `H₃(𝕆)` (`H3Octonion ℝ`, 27D Euclidean Formally Real)

Formalizes the 27-dimensional compact exceptional Jordan algebra `H₃(𝕆)` of `3 × 3`
Hermitian matrices over the compact division octonions `CompactOctonion ℝ`:

1. Carrier `H3Octonion`, 27D basis `h3OctonionBasis`, and `Module.finrank ℝ (H3Octonion ℝ) = 27`.
2. Trace form `traceBilin`, cubic norm `normCubic`, quadratic adjoint `adjointQuad`,
   Freudenthal cross product `crossProduct`, quadratic representation `U`, and triple product `T`.
3. McCrimmon cubic-norm identities `(10)–(19)`, quadratic representation identity `four_U`,
   and commutation `P_comm_U`.
4. Native `NonUnitalNonAssocCommRing (H3Octonion ℝ)` and `IsCommJordan (H3Octonion ℝ)`
   with `jordanU (R := ℝ) X Y = U X Y` and `X * X# = N(X) • 1`.
5. **Euclidean / Formal Reality**:
   * Positive-definite `traceBilin` (`0 ≤ traceBilin x x` and `traceBilin x x = 0 ↔ x = 0`).
   * Formal reality: `x * x + y * y = 0 → x = 0 ∧ y = 0`.
   * Real-form non-isomorphism: `IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ)`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open CompactOctonion

/-- Elements of the 27-dimensional compact Albert Jordan algebra `H₃(𝕆)` over `R`:
diagonal scalars `(α₁, α₂, α₃)` and off-diagonal octonions `(a, b, c) = (x₁₂, x₂₃, x₃₁)`. -/
structure H3Octonion (R : Type*) where
  α₁ : R
  α₂ : R
  α₃ : R
  a : CompactOctonion R
  b : CompactOctonion R
  c : CompactOctonion R

namespace H3Octonion

section CarrierOps

variable {R : Type*} [CommRing R]

omit [CommRing R] in
@[ext] theorem ext_h3 {x y : H3Octonion R}
    (h1 : x.α₁ = y.α₁) (h2 : x.α₂ = y.α₂) (h3 : x.α₃ = y.α₃)
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) : x = y := by
  cases x; cases y; simp_all

def add (x y : H3Octonion R) : H3Octonion R :=
  ⟨x.α₁ + y.α₁, x.α₂ + y.α₂, x.α₃ + y.α₃, x.a + y.a, x.b + y.b, x.c + y.c⟩

def neg (x : H3Octonion R) : H3Octonion R :=
  ⟨-x.α₁, -x.α₂, -x.α₃, -x.a, -x.b, -x.c⟩

def zero : H3Octonion R := ⟨0, 0, 0, 0, 0, 0⟩

def one : H3Octonion R := ⟨1, 1, 1, 0, 0, 0⟩

def sub (x y : H3Octonion R) : H3Octonion R :=
  ⟨x.α₁ - y.α₁, x.α₂ - y.α₂, x.α₃ - y.α₃, x.a - y.a, x.b - y.b, x.c - y.c⟩

def smul (r : R) (x : H3Octonion R) : H3Octonion R :=
  ⟨r * x.α₁, r * x.α₂, r * x.α₃, r • x.a, r • x.b, r • x.c⟩

instance : Zero (H3Octonion R) := ⟨zero⟩
instance : One (H3Octonion R) := ⟨one⟩
instance : Add (H3Octonion R) := ⟨add⟩
instance : Neg (H3Octonion R) := ⟨neg⟩
instance : Sub (H3Octonion R) := ⟨sub⟩
instance : SMul R (H3Octonion R) := ⟨smul⟩

instance : AddCommGroup (H3Octonion R) where
  add := add
  zero := zero
  neg := neg
  sub := sub
  add_assoc _ _ _ := by apply ext_h3 <;> exact add_assoc _ _ _
  zero_add _ := by apply ext_h3 <;> exact zero_add _
  add_zero _ := by apply ext_h3 <;> exact add_zero _
  neg_add_cancel _ := by apply ext_h3 <;> exact neg_add_cancel _
  add_comm _ _ := by apply ext_h3 <;> exact add_comm _ _
  sub_eq_add_neg _ _ := by apply ext_h3 <;> exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (H3Octonion R) where
  smul := smul
  one_smul _ := by apply ext_h3 <;> first | exact one_mul _ | exact one_smul _ _
  mul_smul _ _ _ := by apply ext_h3 <;> first | exact mul_assoc _ _ _ | exact mul_smul _ _ _
  smul_zero _ := by apply ext_h3 <;> first | exact mul_zero _ | exact smul_zero _
  smul_add _ _ _ := by apply ext_h3 <;> first | exact _root_.mul_add _ _ _ | exact smul_add _ _ _
  add_smul _ _ _ := by apply ext_h3 <;> first | exact _root_.add_mul _ _ _ | exact add_smul _ _ _
  zero_smul _ := by apply ext_h3 <;> first | exact zero_mul _ | exact zero_smul _ _

@[simp] theorem zero_α₁ : (0 : H3Octonion R).α₁ = 0 := rfl
@[simp] theorem zero_α₂ : (0 : H3Octonion R).α₂ = 0 := rfl
@[simp] theorem zero_α₃ : (0 : H3Octonion R).α₃ = 0 := rfl
@[simp] theorem zero_a : (0 : H3Octonion R).a = 0 := rfl
@[simp] theorem zero_b : (0 : H3Octonion R).b = 0 := rfl
@[simp] theorem zero_c : (0 : H3Octonion R).c = 0 := rfl

@[simp] theorem one_α₁ : (1 : H3Octonion R).α₁ = 1 := rfl
@[simp] theorem one_α₂ : (1 : H3Octonion R).α₂ = 1 := rfl
@[simp] theorem one_α₃ : (1 : H3Octonion R).α₃ = 1 := rfl
@[simp] theorem one_a : (1 : H3Octonion R).a = 0 := rfl
@[simp] theorem one_b : (1 : H3Octonion R).b = 0 := rfl
@[simp] theorem one_c : (1 : H3Octonion R).c = 0 := rfl

@[simp] theorem add_α₁ (x y : H3Octonion R) : (x + y).α₁ = x.α₁ + y.α₁ := rfl
@[simp] theorem add_α₂ (x y : H3Octonion R) : (x + y).α₂ = x.α₂ + y.α₂ := rfl
@[simp] theorem add_α₃ (x y : H3Octonion R) : (x + y).α₃ = x.α₃ + y.α₃ := rfl
@[simp] theorem add_a (x y : H3Octonion R) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : H3Octonion R) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : H3Octonion R) : (x + y).c = x.c + y.c := rfl

@[simp] theorem neg_α₁ (x : H3Octonion R) : (-x).α₁ = -x.α₁ := rfl
@[simp] theorem neg_α₂ (x : H3Octonion R) : (-x).α₂ = -x.α₂ := rfl
@[simp] theorem neg_α₃ (x : H3Octonion R) : (-x).α₃ = -x.α₃ := rfl
@[simp] theorem neg_a (x : H3Octonion R) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : H3Octonion R) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : H3Octonion R) : (-x).c = -x.c := rfl

@[simp] theorem sub_α₁ (x y : H3Octonion R) : (x - y).α₁ = x.α₁ - y.α₁ := rfl
@[simp] theorem sub_α₂ (x y : H3Octonion R) : (x - y).α₂ = x.α₂ - y.α₂ := rfl
@[simp] theorem sub_α₃ (x y : H3Octonion R) : (x - y).α₃ = x.α₃ - y.α₃ := rfl
@[simp] theorem sub_a (x y : H3Octonion R) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : H3Octonion R) : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c (x y : H3Octonion R) : (x - y).c = x.c - y.c := rfl

@[simp] theorem smul_α₁ (r : R) (x : H3Octonion R) : (r • x).α₁ = r * x.α₁ := rfl
@[simp] theorem smul_α₂ (r : R) (x : H3Octonion R) : (r • x).α₂ = r * x.α₂ := rfl
@[simp] theorem smul_α₃ (r : R) (x : H3Octonion R) : (r • x).α₃ = r * x.α₃ := rfl
@[simp] theorem smul_a (r : R) (x : H3Octonion R) : (r • x).a = r • x.a := rfl
@[simp] theorem smul_b (r : R) (x : H3Octonion R) : (r • x).b = r • x.b := rfl
@[simp] theorem smul_c (r : R) (x : H3Octonion R) : (r • x).c = r • x.c := rfl

def diagCartan (l1 l2 l3 : R) : H3Octonion R := ⟨l1, l2, l3, 0, 0, 0⟩
def embedJ12 (a : CompactOctonion R) : H3Octonion R := ⟨0, 0, 0, a, 0, 0⟩
def embedJ23 (b : CompactOctonion R) : H3Octonion R := ⟨0, 0, 0, 0, b, 0⟩
def embedJ31 (c : CompactOctonion R) : H3Octonion R := ⟨0, 0, 0, 0, 0, c⟩

def rotate (x : H3Octonion R) : H3Octonion R :=
  ⟨x.α₂, x.α₃, x.α₁, x.b, x.c, x.a⟩

omit [CommRing R] in @[simp] theorem rotate_α₁ (x : H3Octonion R) : (rotate x).α₁ = x.α₂ := rfl
omit [CommRing R] in @[simp] theorem rotate_α₂ (x : H3Octonion R) : (rotate x).α₂ = x.α₃ := rfl
omit [CommRing R] in @[simp] theorem rotate_α₃ (x : H3Octonion R) : (rotate x).α₃ = x.α₁ := rfl
omit [CommRing R] in @[simp] theorem rotate_a (x : H3Octonion R) : (rotate x).a = x.b := rfl
omit [CommRing R] in @[simp] theorem rotate_b (x : H3Octonion R) : (rotate x).b = x.c := rfl
omit [CommRing R] in @[simp] theorem rotate_c (x : H3Octonion R) : (rotate x).c = x.a := rfl

omit [CommRing R] in theorem rotate_rotate_rotate (x : H3Octonion R) : rotate (rotate (rotate x)) = x := rfl

theorem rotate_add (x y : H3Octonion R) : rotate (x + y) = rotate x + rotate y := by
  apply ext_h3 <;> simp [rotate]

theorem rotate_smul (r : R) (x : H3Octonion R) : rotate (r • x) = r • rotate x := by
  apply ext_h3 <;> simp [rotate]

def linearTrace (x : H3Octonion R) : R := x.α₁ + x.α₂ + x.α₃

@[simp] theorem linearTrace_zero : linearTrace (0 : H3Octonion R) = 0 := by simp [linearTrace]
@[simp] theorem linearTrace_one : linearTrace (1 : H3Octonion R) = 3 := by
  change (1 : R) + 1 + 1 = 3
  ring
theorem linearTrace_add (x y : H3Octonion R) : linearTrace (x + y) = linearTrace x + linearTrace y := by
  simp [linearTrace]; ring
theorem linearTrace_sub (x y : H3Octonion R) : linearTrace (x - y) = linearTrace x - linearTrace y := by
  simp [linearTrace, sub_eq_add_neg]; ring
theorem linearTrace_neg (x : H3Octonion R) : linearTrace (-x) = -linearTrace x := by
  simp [linearTrace]; ring
theorem linearTrace_smul (r : R) (x : H3Octonion R) : linearTrace (r • x) = r * linearTrace x := by
  simp [linearTrace]; ring
@[simp] theorem linearTrace_rotate (x : H3Octonion R) : linearTrace (rotate x) = linearTrace x := by
  simp [linearTrace, rotate]; ring

def traceBilin (x y : H3Octonion R) : R :=
  x.α₁ * y.α₁ + x.α₂ * y.α₂ + x.α₃ * y.α₃ +
    trace (mul x.a (conj y.a)) + trace (mul x.b (conj y.b)) + trace (mul x.c (conj y.c))

theorem traceBilin_symm (x y : H3Octonion R) : traceBilin x y = traceBilin y x := by
  simp only [traceBilin]
  rw [trace_mul_conj_comm x.a y.a, trace_mul_conj_comm x.b y.b, trace_mul_conj_comm x.c y.c]
  ring

theorem traceBilin_one (x : H3Octonion R) : traceBilin x 1 = linearTrace x := by
  simp [traceBilin, linearTrace]

theorem traceBilin_one_left (x : H3Octonion R) : traceBilin 1 x = linearTrace x := by
  rw [traceBilin_symm, traceBilin_one]

theorem traceBilin_add_left (x₁ x₂ y : H3Octonion R) :
    traceBilin (x₁ + x₂) y = traceBilin x₁ y + traceBilin x₂ y := by
  simp only [traceBilin, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
    CompactOctonion.add_mul, CompactOctonion.trace_add]
  ring

theorem traceBilin_add_right (x y₁ y₂ : H3Octonion R) :
    traceBilin x (y₁ + y₂) = traceBilin x y₁ + traceBilin x y₂ := by
  rw [traceBilin_symm, traceBilin_add_left, traceBilin_symm y₁ x, traceBilin_symm y₂ x]

theorem traceBilin_sub_left (x₁ x₂ y : H3Octonion R) :
    traceBilin (x₁ - x₂) y = traceBilin x₁ y - traceBilin x₂ y := by
  simp only [traceBilin, sub_α₁, sub_α₂, sub_α₃, sub_a, sub_b, sub_c,
    CompactOctonion.sub_mul, CompactOctonion.trace_sub]
  ring

theorem traceBilin_sub_right (x y₁ y₂ : H3Octonion R) :
    traceBilin x (y₁ - y₂) = traceBilin x y₁ - traceBilin x y₂ := by
  rw [traceBilin_symm, traceBilin_sub_left, traceBilin_symm y₁ x, traceBilin_symm y₂ x]

theorem traceBilin_neg_left (x y : H3Octonion R) : traceBilin (-x) y = -traceBilin x y := by
  simp only [traceBilin, neg_α₁, neg_α₂, neg_α₃, neg_a, neg_b, neg_c,
    CompactOctonion.neg_mul, CompactOctonion.trace_neg]
  ring

theorem traceBilin_neg_right (x y : H3Octonion R) : traceBilin x (-y) = -traceBilin x y := by
  rw [traceBilin_symm, traceBilin_neg_left, traceBilin_symm]

theorem traceBilin_smul_left (r : R) (x y : H3Octonion R) :
    traceBilin (r • x) y = r * traceBilin x y := by
  simp only [traceBilin, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
    CompactOctonion.smul_mul, CompactOctonion.trace_smul]
  ring

theorem traceBilin_smul_right (r : R) (x y : H3Octonion R) :
    traceBilin x (r • y) = r * traceBilin x y := by
  rw [traceBilin_symm, traceBilin_smul_left, traceBilin_symm]

@[simp] theorem traceBilin_zero_left (y : H3Octonion R) : traceBilin 0 y = 0 := by
  simp [traceBilin]

@[simp] theorem traceBilin_zero_right (x : H3Octonion R) : traceBilin x 0 = 0 := by
  simp [traceBilin]

@[simp] theorem traceBilin_rotate (x y : H3Octonion R) :
    traceBilin (rotate x) (rotate y) = traceBilin x y := by
  simp [traceBilin, rotate]; ring

def normCubic (x : H3Octonion R) : R :=
  x.α₁ * x.α₂ * x.α₃ - x.α₁ * CompactOctonion.norm x.b - x.α₂ * CompactOctonion.norm x.c -
    x.α₃ * CompactOctonion.norm x.a + trace (mul (mul x.a x.b) x.c)

@[simp] theorem normCubic_zero : normCubic (0 : H3Octonion R) = 0 := by
  simp [normCubic]

@[simp] theorem normCubic_one : normCubic (1 : H3Octonion R) = 1 := by
  simp [normCubic]

theorem normCubic_smul (r : R) (x : H3Octonion R) :
    normCubic (r • x) = r ^ 3 * normCubic x := by
  simp only [normCubic, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
    norm_smul, CompactOctonion.smul_mul, CompactOctonion.mul_smul, trace_smul]
  ring

@[simp] theorem normCubic_rotate (x : H3Octonion R) : normCubic (rotate x) = normCubic x := by
  simp only [normCubic, rotate_α₁, rotate_α₂, rotate_α₃, rotate_a, rotate_b, rotate_c]
  rw [trace_mul_cyclic x.a x.b x.c]
  ring

def adjointQuad (x : H3Octonion R) : H3Octonion R where
  α₁ := x.α₂ * x.α₃ - CompactOctonion.norm x.b
  α₂ := x.α₃ * x.α₁ - CompactOctonion.norm x.c
  α₃ := x.α₁ * x.α₂ - CompactOctonion.norm x.a
  a := mul (conj x.c) (conj x.b) - x.α₃ • x.a
  b := mul (conj x.a) (conj x.c) - x.α₁ • x.b
  c := mul (conj x.b) (conj x.a) - x.α₂ • x.c

@[simp] theorem adjointQuad_zero : adjointQuad (0 : H3Octonion R) = 0 := by
  apply ext_h3 <;> simp [adjointQuad]

@[simp] theorem adjointQuad_one : adjointQuad (1 : H3Octonion R) = 1 := by
  apply ext_h3 <;> simp [adjointQuad]

theorem adjointQuad_smul (r : R) (x : H3Octonion R) :
    adjointQuad (r • x) = (r ^ 2) • adjointQuad x := by
  apply ext_h3 <;> simp [adjointQuad, norm_smul, conj_smul, CompactOctonion.smul_mul,
    CompactOctonion.mul_smul, smul_sub, smul_smul] <;> ring

theorem adjointQuad_rotate (x : H3Octonion R) :
    adjointQuad (rotate x) = rotate (adjointQuad x) := by
  apply ext_h3 <;> simp [adjointQuad, rotate]

def crossProduct (x y : H3Octonion R) : H3Octonion R where
  α₁ := x.α₂ * y.α₃ + y.α₂ * x.α₃ - trace (mul x.b (conj y.b))
  α₂ := x.α₃ * y.α₁ + y.α₃ * x.α₁ - trace (mul x.c (conj y.c))
  α₃ := x.α₁ * y.α₂ + y.α₁ * x.α₂ - trace (mul x.a (conj y.a))
  a := mul (conj x.c) (conj y.b) + mul (conj y.c) (conj x.b) - x.α₃ • y.a - y.α₃ • x.a
  b := mul (conj x.a) (conj y.c) + mul (conj y.a) (conj x.c) - x.α₁ • y.b - y.α₁ • x.b
  c := mul (conj x.b) (conj y.a) + mul (conj y.b) (conj x.a) - x.α₂ • y.c - y.α₂ • x.c

theorem crossProduct_symm (x y : H3Octonion R) : crossProduct x y = crossProduct y x := by
  apply ext_h3
  · simp [crossProduct]; rw [trace_mul_conj_comm]; ring
  · simp [crossProduct]; rw [trace_mul_conj_comm]; ring
  · simp [crossProduct]; rw [trace_mul_conj_comm]; ring
  · simp [crossProduct]; abel
  · simp [crossProduct]; abel
  · simp [crossProduct]; abel

theorem crossProduct_self (x : H3Octonion R) :
    crossProduct x x = (2 : R) • adjointQuad x := by
  apply ext_h3
  · simp [crossProduct, adjointQuad, norm, trace, mul, conj]; ring
  · simp [crossProduct, adjointQuad, norm, trace, mul, conj]; ring
  · simp [crossProduct, adjointQuad, norm, trace, mul, conj]; ring
  · simp [crossProduct, adjointQuad, smul_sub]; module
  · simp [crossProduct, adjointQuad, smul_sub]; module
  · simp [crossProduct, adjointQuad, smul_sub]; module

theorem crossProduct_one (x : H3Octonion R) :
    crossProduct x 1 = linearTrace x • (1 : H3Octonion R) - x := by
  apply ext_h3
  · simp [crossProduct, linearTrace]; ring
  · simp [crossProduct, linearTrace]; ring
  · simp [crossProduct, linearTrace]
  · simp [crossProduct]
  · simp [crossProduct]
  · simp [crossProduct]

theorem crossProduct_add_left (x₁ x₂ y : H3Octonion R) :
    crossProduct (x₁ + x₂) y = crossProduct x₁ y + crossProduct x₂ y := by
  apply ext_h3
  · simp only [crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      CompactOctonion.add_mul, trace_add]
    ring
  · simp only [crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      CompactOctonion.add_mul, trace_add]
    ring
  · simp only [crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      CompactOctonion.add_mul, trace_add]
    ring
  · simp only [crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      conj_add, CompactOctonion.add_mul, CompactOctonion.mul_add, add_smul, smul_add]
    abel
  · simp only [crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      conj_add, CompactOctonion.add_mul, CompactOctonion.mul_add, add_smul, smul_add]
    abel
  · simp only [crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      conj_add, CompactOctonion.add_mul, CompactOctonion.mul_add, add_smul, smul_add]
    abel

theorem crossProduct_add_right (x y₁ y₂ : H3Octonion R) :
    crossProduct x (y₁ + y₂) = crossProduct x y₁ + crossProduct x y₂ := by
  rw [crossProduct_symm, crossProduct_add_left, crossProduct_symm y₁ x, crossProduct_symm y₂ x]

theorem crossProduct_smul_left (r : R) (x y : H3Octonion R) :
    crossProduct (r • x) y = r • crossProduct x y := by
  apply ext_h3
  · simp only [crossProduct, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
      CompactOctonion.smul_mul, trace_smul]
    ring
  · simp only [crossProduct, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
      CompactOctonion.smul_mul, trace_smul]
    ring
  · simp only [crossProduct, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
      CompactOctonion.smul_mul, trace_smul]
    ring
  · simp only [crossProduct, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
      conj_smul, CompactOctonion.smul_mul, CompactOctonion.mul_smul, smul_sub, smul_add, smul_smul]
    module
  · simp only [crossProduct, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
      conj_smul, CompactOctonion.smul_mul, CompactOctonion.mul_smul, smul_sub, smul_add, smul_smul]
    module
  · simp only [crossProduct, smul_α₁, smul_α₂, smul_α₃, smul_a, smul_b, smul_c,
      conj_smul, CompactOctonion.smul_mul, CompactOctonion.mul_smul, smul_sub, smul_add, smul_smul]
    module

theorem crossProduct_smul_right (r : R) (x y : H3Octonion R) :
    crossProduct x (r • y) = r • crossProduct x y := by
  rw [crossProduct_symm, crossProduct_smul_left, crossProduct_symm]

@[simp] theorem crossProduct_zero_left (y : H3Octonion R) : crossProduct 0 y = 0 := by
  apply ext_h3 <;> simp [crossProduct]

@[simp] theorem crossProduct_zero_right (x : H3Octonion R) : crossProduct x 0 = 0 := by
  rw [crossProduct_symm, crossProduct_zero_left]

theorem crossProduct_rotate (x y : H3Octonion R) :
    crossProduct (rotate x) (rotate y) = rotate (crossProduct x y) := by
  apply ext_h3 <;> simp [crossProduct, rotate]

theorem adjointQuad_add (x y : H3Octonion R) :
    adjointQuad (x + y) = adjointQuad x + crossProduct x y + adjointQuad y := by
  apply ext_h3
  · simp only [adjointQuad, crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      norm_add]; ring
  · simp only [adjointQuad, crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      norm_add]; ring
  · simp only [adjointQuad, crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      norm_add]; ring
  · simp only [adjointQuad, crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      conj_add, CompactOctonion.add_mul, CompactOctonion.mul_add, add_smul, smul_add]
    abel
  · simp only [adjointQuad, crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      conj_add, CompactOctonion.add_mul, CompactOctonion.mul_add, add_smul, smul_add]
    abel
  · simp only [adjointQuad, crossProduct, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
      conj_add, CompactOctonion.add_mul, CompactOctonion.mul_add, add_smul, smul_add]
    abel

theorem normCubic_add (x y : H3Octonion R) :
    normCubic (x + y) =
      normCubic x + traceBilin (adjointQuad x) y + traceBilin x (adjointQuad y) + normCubic y := by
  simp only [normCubic, traceBilin, adjointQuad, add_α₁, add_α₂, add_α₃, add_a, add_b, add_c,
    norm_add, CompactOctonion.add_mul, CompactOctonion.mul_add, trace_add,
    CompactOctonion.sub_mul, CompactOctonion.mul_sub, trace_sub, conj_sub,
    CompactOctonion.conj_mul, CompactOctonion.conj_conj, conj_smul,
    CompactOctonion.smul_mul, CompactOctonion.mul_smul, trace_smul]
  have hr1 : trace (mul (mul (conj x.c) (conj x.b)) (conj y.a)) = trace (mul (mul y.a x.b) x.c) := by
    rw [trace_mul_conj_comm, CompactOctonion.conj_mul, CompactOctonion.conj_conj,
      CompactOctonion.conj_conj, ← trace_mul_assoc]
  have hr2 : trace (mul (mul (conj x.a) (conj x.c)) (conj y.b)) = trace (mul (mul x.a y.b) x.c) := by
    rw [trace_mul_conj_comm, CompactOctonion.conj_mul, CompactOctonion.conj_conj,
      CompactOctonion.conj_conj, ← trace_mul_assoc, ← trace_mul_cyclic]
  have hr3 : trace (mul (mul (conj x.b) (conj x.a)) (conj y.c)) = trace (mul (mul x.a x.b) y.c) := by
    rw [trace_mul_conj_comm, CompactOctonion.conj_mul, CompactOctonion.conj_conj,
      CompactOctonion.conj_conj, trace_mul_comm]
  have hy1 : trace (mul x.a (mul y.b y.c)) = trace (mul (mul x.a y.b) y.c) :=
    (trace_mul_assoc x.a y.b y.c).symm
  have hy2 : trace (mul x.b (mul y.c y.a)) = trace (mul (mul y.a x.b) y.c) :=
    (trace_mul_assoc x.b y.c y.a).symm.trans (trace_mul_cyclic y.a x.b y.c).symm
  have hy3 : trace (mul x.c (mul y.a y.b)) = trace (mul (mul y.a y.b) x.c) :=
    (trace_mul_assoc x.c y.a y.b).symm.trans (trace_mul_cyclic x.c y.a y.b)
  rw [hr1, hr2, hr3, hy1, hy2, hy3]
  ring

theorem normCubic_line (r : R) (x y : H3Octonion R) :
    normCubic (x + r • y) = normCubic x +
      r * traceBilin (adjointQuad x) y +
      r ^ 2 * traceBilin (adjointQuad y) x +
      r ^ 3 * normCubic y := by
  rw [normCubic_add, normCubic_smul, traceBilin_smul_right, adjointQuad_smul,
    traceBilin_smul_right, traceBilin_symm x (adjointQuad y)]

private theorem adjointQuad_adjointQuad_comp_a (x : H3Octonion R) :
    (adjointQuad (adjointQuad x)).a = normCubic x • x.a := by
  simp only [adjointQuad, normCubic, CompactOctonion.conj_sub, CompactOctonion.conj_mul,
    CompactOctonion.conj_conj, CompactOctonion.conj_smul]
  exact adjoint_component_composition x.α₁ x.α₂ x.α₃ x.a x.b x.c

private theorem adjointQuad_adjointQuad_comp_α₁ (x : H3Octonion R) :
    (adjointQuad (adjointQuad x)).α₁ = normCubic x * x.α₁ := by
  simp only [adjointQuad, normCubic]
  rw [mul_comm x.α₃ x.α₁]
  exact adjoint_diagonal_composition x.α₁ x.α₂ x.α₃ x.a x.b x.c

/-- Core McCrimmon identity `(X#)# = N(X) • X` on compact `H₃(𝕆)`. -/
theorem adjointQuad_adjointQuad (x : H3Octonion R) :
    adjointQuad (adjointQuad x) = normCubic x • x := by
  have h1 : ∀ z : H3Octonion R,
      (adjointQuad (adjointQuad z)).α₁ = (normCubic z • z).α₁ ∧
      (adjointQuad (adjointQuad z)).a = (normCubic z • z).a := fun z =>
    ⟨adjointQuad_adjointQuad_comp_α₁ z, adjointQuad_adjointQuad_comp_a z⟩
  have hr1 := h1 x
  have hr2 := h1 (rotate x)
  have hr3 := h1 (rotate (rotate x))
  simp only [adjointQuad_rotate, normCubic_rotate] at hr2 hr3
  apply ext_h3
  · exact hr1.1
  · exact hr2.1
  · exact hr3.1
  · exact hr1.2
  · exact hr2.2
  · exact hr3.2

def U (x y : H3Octonion R) : H3Octonion R :=
  traceBilin x y • x - crossProduct (adjointQuad x) y

def T (x y z : H3Octonion R) : H3Octonion R :=
  U (x + z) y - U x y - U z y

theorem U_add_left (x₁ x₂ y : H3Octonion R) : U (x₁ + x₂) y = U x₁ y + T x₁ y x₂ + U x₂ y := by
  dsimp [T]; abel

theorem U_add_right (x y₁ y₂ : H3Octonion R) : U x (y₁ + y₂) = U x y₁ + U x y₂ := by
  simp only [U, traceBilin_add_right, add_smul, crossProduct_add_right]; abel

theorem U_sub_right (x y₁ y₂ : H3Octonion R) : U x (y₁ - y₂) = U x y₁ - U x y₂ := by
  rw [sub_eq_add_neg, show -y₂ = (-1 : R) • y₂ by module, U_add_right]
  simp only [U, traceBilin_smul_right, crossProduct_smul_right]; module

theorem U_smul_left (r : R) (x y : H3Octonion R) : U (r • x) y = (r ^ 2) • U x y := by
  simp only [U, traceBilin_smul_left, adjointQuad_smul, crossProduct_smul_left, smul_smul, smul_sub]
  rw [show r * traceBilin x y * r = r ^ 2 * traceBilin x y by ring]

theorem U_smul_right (r : R) (x y : H3Octonion R) : U x (r • y) = r • U x y := by
  simp only [U, traceBilin_smul_right, crossProduct_smul_right, smul_smul, smul_sub]

theorem U_one (y : H3Octonion R) : U (1 : H3Octonion R) y = y := by
  rw [U, traceBilin_symm, traceBilin_one, adjointQuad_one, crossProduct_symm, crossProduct_one]
  module

theorem T_outer_formula (x y z : H3Octonion R) :
    T x y z = traceBilin x y • z + traceBilin z y • x - crossProduct (crossProduct x z) y := by
  simp only [T, U, traceBilin_add_left, adjointQuad_add, crossProduct_add_left,
    add_smul, smul_add]
  module

theorem T_symm_outer (x y z : H3Octonion R) : T x y z = T z y x := by
  simp only [T_outer_formula, crossProduct_symm x z]; module

theorem T_add_right (x y₁ y₂ z : H3Octonion R) : T x (y₁ + y₂) z = T x y₁ z + T x y₂ z := by
  simp only [T, U_add_right]; module

theorem T_add_left (x₁ x₂ y z : H3Octonion R) : T (x₁ + x₂) y z = T x₁ y z + T x₂ y z := by
  simp only [T_outer_formula, traceBilin_add_left, crossProduct_add_left, add_smul]; module

theorem T_smul_left (r : R) (x y z : H3Octonion R) : T (r • x) y z = r • T x y z := by
  simp only [T_outer_formula, traceBilin_smul_left, crossProduct_smul_left, smul_smul, smul_add,
    smul_sub]
  rw [mul_comm (traceBilin z y) r]

theorem T_smul_right (r : R) (x y z : H3Octonion R) : T x (r • y) z = r • T x y z := by
  simp only [T, U_smul_right]; module

theorem T_smul_outer (r : R) (x y z : H3Octonion R) : T x y (r • z) = r • T x y z := by
  rw [T_symm_outer, T_smul_left, T_symm_outer]

theorem T_add_outer (x y z₁ z₂ : H3Octonion R) : T x y (z₁ + z₂) = T x y z₁ + T x y z₂ := by
  rw [T_symm_outer, T_add_left, T_symm_outer z₁ y x, T_symm_outer z₂ y x]

theorem T_one_formula (x z : H3Octonion R) :
    T x 1 z = linearTrace x • z + linearTrace z • x + crossProduct x z -
      linearTrace (crossProduct x z) • (1 : H3Octonion R) := by
  rw [T_outer_formula, traceBilin_one, traceBilin_one, crossProduct_one]
  module

end CarrierOps

section BasisAndFinrank

def basisVec (k : Fin 27) : H3Octonion ℝ :=
  if hk1 : k.val = 0 then diagCartan 1 0 0
  else if hk2 : k.val = 1 then diagCartan 0 1 0
  else if hk3 : k.val = 2 then diagCartan 0 0 1
  else if h12 : k.val < 11 then embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩)
  else if h23 : k.val < 19 then embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩)
  else embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩)

def coordFun (x : H3Octonion ℝ) (k : Fin 27) : ℝ :=
  if k.val = 0 then x.α₁
  else if k.val = 1 then x.α₂
  else if k.val = 2 then x.α₃
  else if h12 : k.val < 11 then CompactOctonion.coordFun x.a ⟨k.val - 3, by omega⟩
  else if h23 : k.val < 19 then CompactOctonion.coordFun x.b ⟨k.val - 11, by omega⟩
  else CompactOctonion.coordFun x.c ⟨k.val - 19, by omega⟩

private def mkOfFun (f : Fin 27 → ℝ) : H3Octonion ℝ :=
  ⟨f 0, f 1, f 2,
   CompactOctonion.mkOfFun (fun i => f ⟨3 + i.val, by omega⟩),
   CompactOctonion.mkOfFun (fun i => f ⟨11 + i.val, by omega⟩),
   CompactOctonion.mkOfFun (fun i => f ⟨19 + i.val, by omega⟩)⟩

def h3OctonionCoordEquiv : H3Octonion ℝ ≃ₗ[ℝ] (Fin 27 → ℝ) where
  toFun := coordFun
  invFun := mkOfFun
  left_inv x := by
    ext <;> dsimp [mkOfFun, coordFun, CompactOctonion.mkOfFun, CompactOctonion.coordFun]
  right_inv f := by
    ext k
    fin_cases k <;> rfl
  map_add' x y := by
    ext k
    fin_cases k <;> rfl
  map_smul' r x := by
    ext k
    fin_cases k <;> rfl

def h3OctonionBasis : Module.Basis (Fin 27) ℝ (H3Octonion ℝ) :=
  Module.Basis.ofEquivFun h3OctonionCoordEquiv

@[simp] theorem h3OctonionBasis_apply (k : Fin 27) : h3OctonionBasis k = basisVec k := by
  have hk_cases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨
      (3 ≤ k.val ∧ k.val < 11) ∨ (11 ≤ k.val ∧ k.val < 19) ∨ (19 ≤ k.val ∧ k.val < 27) := by
    omega
  rcases hk_cases with h0 | h1 | h2 | ⟨h3a, h3b⟩ | ⟨h4a, h4b⟩ | ⟨h5a, h5b⟩
  · have hk : k = 0 := Fin.ext h0
    subst hk
    apply ext_h3 <;> (try ext) <;>
      simp [h3OctonionBasis, h3OctonionCoordEquiv, mkOfFun, basisVec, diagCartan,
        CompactOctonion.mkOfFun]
  · have hk : k = 1 := Fin.ext h1
    subst hk
    apply ext_h3 <;> (try ext) <;>
      simp [h3OctonionBasis, h3OctonionCoordEquiv, mkOfFun, basisVec, diagCartan,
        CompactOctonion.mkOfFun]
  · have hk : k = 2 := Fin.ext h2
    subst hk
    apply ext_h3 <;> (try ext) <;>
      simp [h3OctonionBasis, h3OctonionCoordEquiv, mkOfFun, basisVec, diagCartan,
        CompactOctonion.mkOfFun]
  · have hbas : h3OctonionBasis k = mkOfFun (Pi.single k (1 : ℝ)) :=
      congrFun (Module.Basis.coe_ofEquivFun h3OctonionCoordEquiv) k
    have hbv : basisVec k = embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
      simp [basisVec, show k.val ≠ 0 by omega, show k.val ≠ 1 by omega, show k.val ≠ 2 by omega, h3b]
    rw [hbas, hbv]
    apply ext_h3
    · dsimp [mkOfFun, embedJ12]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · dsimp [mkOfFun, embedJ12]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · dsimp [mkOfFun, embedJ12]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · rw [← CompactOctonion.compactOctonionBasis_apply ⟨k.val - 3, by omega⟩]
      have hcb : CompactOctonion.compactOctonionBasis ⟨k.val - 3, by omega⟩ =
          CompactOctonion.mkOfFun (Pi.single ⟨k.val - 3, by omega⟩ (1 : ℝ)) :=
        congrFun (Module.Basis.coe_ofEquivFun CompactOctonion.coordEquiv) ⟨k.val - 3, by omega⟩
      rw [hcb]
      dsimp [mkOfFun, embedJ12]
      congr 1; ext i; simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    · ext <;>
      · dsimp [mkOfFun, CompactOctonion.mkOfFun, embedJ12]
        apply Pi.single_eq_of_ne
        exact Fin.ne_of_val_ne (by dsimp; omega)
    · ext <;>
      · dsimp [mkOfFun, CompactOctonion.mkOfFun, embedJ12]
        apply Pi.single_eq_of_ne
        exact Fin.ne_of_val_ne (by dsimp; omega)
  · have hbas : h3OctonionBasis k = mkOfFun (Pi.single k (1 : ℝ)) :=
      congrFun (Module.Basis.coe_ofEquivFun h3OctonionCoordEquiv) k
    have hbv : basisVec k = embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
      simp [basisVec, show k.val ≠ 0 by omega, show k.val ≠ 1 by omega, show k.val ≠ 2 by omega,
        show ¬ k.val < 11 by omega, h4b]
    rw [hbas, hbv]
    apply ext_h3
    · dsimp [mkOfFun, embedJ23]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · dsimp [mkOfFun, embedJ23]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · dsimp [mkOfFun, embedJ23]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · ext <;>
      · dsimp [mkOfFun, CompactOctonion.mkOfFun, embedJ23]
        apply Pi.single_eq_of_ne
        exact Fin.ne_of_val_ne (by dsimp; omega)
    · rw [← CompactOctonion.compactOctonionBasis_apply ⟨k.val - 11, by omega⟩]
      have hcb : CompactOctonion.compactOctonionBasis ⟨k.val - 11, by omega⟩ =
          CompactOctonion.mkOfFun (Pi.single ⟨k.val - 11, by omega⟩ (1 : ℝ)) :=
        congrFun (Module.Basis.coe_ofEquivFun CompactOctonion.coordEquiv) ⟨k.val - 11, by omega⟩
      rw [hcb]
      dsimp [mkOfFun, embedJ23]
      congr 1; ext i; simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    · ext <;>
      · dsimp [mkOfFun, CompactOctonion.mkOfFun, embedJ23]
        apply Pi.single_eq_of_ne
        exact Fin.ne_of_val_ne (by dsimp; omega)
  · have hbas : h3OctonionBasis k = mkOfFun (Pi.single k (1 : ℝ)) :=
      congrFun (Module.Basis.coe_ofEquivFun h3OctonionCoordEquiv) k
    have hbv : basisVec k = embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
      simp [basisVec, show k.val ≠ 0 by omega, show k.val ≠ 1 by omega, show k.val ≠ 2 by omega,
        show ¬ k.val < 11 by omega, show ¬ k.val < 19 by omega]
    rw [hbas, hbv]
    apply ext_h3
    · dsimp [mkOfFun, embedJ31]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · dsimp [mkOfFun, embedJ31]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · dsimp [mkOfFun, embedJ31]
      apply Pi.single_eq_of_ne
      exact Fin.ne_of_val_ne (by dsimp; omega)
    · ext <;>
      · dsimp [mkOfFun, CompactOctonion.mkOfFun, embedJ31]
        apply Pi.single_eq_of_ne
        exact Fin.ne_of_val_ne (by dsimp; omega)
    · ext <;>
      · dsimp [mkOfFun, CompactOctonion.mkOfFun, embedJ31]
        apply Pi.single_eq_of_ne
        exact Fin.ne_of_val_ne (by dsimp; omega)
    · rw [← CompactOctonion.compactOctonionBasis_apply ⟨k.val - 19, by omega⟩]
      have hcb : CompactOctonion.compactOctonionBasis ⟨k.val - 19, by omega⟩ =
          CompactOctonion.mkOfFun (Pi.single ⟨k.val - 19, by omega⟩ (1 : ℝ)) :=
        congrFun (Module.Basis.coe_ofEquivFun CompactOctonion.coordEquiv) ⟨k.val - 19, by omega⟩
      rw [hcb]
      dsimp [mkOfFun, embedJ31]
      congr 1; ext i; simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem finrank_h3Octonion : Module.finrank ℝ (H3Octonion ℝ) = 27 := by
  rw [Module.finrank_eq_card_basis h3OctonionBasis, Fintype.card_fin]

theorem basisVec_decomposition (x : H3Octonion ℝ) :
    x = ∑ k : Fin 27, coordFun x k • basisVec k := by
  have h := (h3OctonionBasis.sum_repr x).symm
  simp only [h3OctonionBasis_apply] at h
  exact h

end BasisAndFinrank

section McCrimmonAndQuadraticIdentities

private theorem extract_master_linearization (x y : H3Octonion ℝ) :
    (crossProduct (adjointQuad x) (crossProduct x y) =
      normCubic x • y + traceBilin (adjointQuad x) y • x) ∧
    (crossProduct (adjointQuad x) (adjointQuad y) + adjointQuad (crossProduct x y) =
      traceBilin (adjointQuad x) y • y + traceBilin (adjointQuad y) x • x) := by
  have m (r : ℝ) : adjointQuad (adjointQuad (x + r • y)) =
      normCubic (x + r • y) • (x + r • y) :=
    adjointQuad_adjointQuad (x + r • y)
  have lhs_exp : ∀ r : ℝ,
      adjointQuad (adjointQuad (x + r • y)) =
        adjointQuad (adjointQuad x) +
        r • crossProduct (adjointQuad x) (crossProduct x y) +
        r ^ 2 • (crossProduct (adjointQuad x) (adjointQuad y) + adjointQuad (crossProduct x y)) +
        r ^ 3 • crossProduct (crossProduct x y) (adjointQuad y) +
        r ^ 4 • adjointQuad (adjointQuad y) := by
    intro r
    rw [adjointQuad_add, crossProduct_smul_right, adjointQuad_smul, adjointQuad_add,
      adjointQuad_add, crossProduct_add_left, crossProduct_smul_right, crossProduct_smul_right,
      crossProduct_smul_left, crossProduct_smul_right, adjointQuad_smul, adjointQuad_smul]
    simp only [smul_smul]
    have h4 : (r ^ 2) ^ 2 = r ^ 4 := by ring
    have h3 : r * r ^ 2 = r ^ 3 := by ring
    rw [h4, h3]
    module
  have rhs_exp : ∀ r : ℝ,
      normCubic (x + r • y) • (x + r • y) =
        normCubic x • x +
        r • (normCubic x • y + traceBilin (adjointQuad x) y • x) +
        r ^ 2 • (traceBilin (adjointQuad x) y • y + traceBilin (adjointQuad y) x • x) +
        r ^ 3 • (traceBilin (adjointQuad y) x • y + normCubic y • x) +
        r ^ 4 • (normCubic y • y) := by
    intro r
    rw [normCubic_line]
    have hr1 : ∀ c : ℝ, r * c * r = r ^ 2 * c := fun c => by ring
    have hr2 : ∀ c : ℝ, r ^ 2 * c * r = r ^ 3 * c := fun c => by ring
    have hr3 : ∀ c : ℝ, r ^ 3 * c * r = r ^ 4 * c := fun c => by ring
    simp only [smul_add, add_smul, smul_smul, _root_.add_mul, hr1, hr2, hr3]
    module
  let c1 : H3Octonion ℝ :=
    crossProduct (adjointQuad x) (crossProduct x y) -
      (normCubic x • y + traceBilin (adjointQuad x) y • x)
  let c2 : H3Octonion ℝ :=
    crossProduct (adjointQuad x) (adjointQuad y) + adjointQuad (crossProduct x y) -
      (traceBilin (adjointQuad x) y • y + traceBilin (adjointQuad y) x • x)
  let c3 : H3Octonion ℝ :=
    crossProduct (crossProduct x y) (adjointQuad y) -
      (traceBilin (adjointQuad y) x • y + normCubic y • x)
  have poly : ∀ r : ℝ, r • c1 + r ^ 2 • c2 + r ^ 3 • c3 = 0 := by
    intro r
    have hm := m r
    rw [lhs_exp r, rhs_exp r, adjointQuad_adjointQuad x, adjointQuad_adjointQuad y] at hm
    have hsub := sub_eq_zero.mpr hm
    convert hsub using 1
    dsimp [c1, c2, c3]
    module
  have h1 := poly 1
  have hm1 := poly (-1)
  have h2 := poly 2
  have hc2_8 : (6 : ℝ) • c2 = 0 := by
    have hsum : (2 : ℝ) • c2 = 0 := by
      have hh := congrArg₂ (fun A B : H3Octonion ℝ => A + B) h1 hm1
      simp only [add_zero] at hh
      convert hh using 1
      module
    have : (6 : ℝ) • c2 = (3 : ℝ) • ((2 : ℝ) • c2) := by module
    rw [this, hsum, smul_zero]
  have hc2 : c2 = 0 := (smul_eq_zero.mp hc2_8).resolve_left (by norm_num)
  have h1' : c1 + c3 = 0 := by
    have hh := h1
    rw [hc2, smul_zero, add_zero, one_smul, one_pow, one_smul] at hh
    exact hh
  have h2' : (2 : ℝ) • c1 + (8 : ℝ) • c3 = 0 := by
    have hh := h2
    rw [hc2, smul_zero, add_zero] at hh
    convert hh using 1
    norm_num
  have hc1_6 : (6 : ℝ) • c1 = 0 := by
    have : (6 : ℝ) • c1 = (8 : ℝ) • (c1 + c3) - ((2 : ℝ) • c1 + (8 : ℝ) • c3) := by module
    rw [this, h1', h2', smul_zero, sub_zero]
  have hc1 : c1 = 0 := (smul_eq_zero.mp hc1_6).resolve_left (by norm_num)
  exact ⟨sub_eq_zero.mp hc1, sub_eq_zero.mp hc2⟩

theorem mccrimmon_identity_10 (x y : H3Octonion ℝ) :
    crossProduct (adjointQuad x) (crossProduct x y) =
      normCubic x • y + traceBilin (adjointQuad x) y • x :=
  (extract_master_linearization x y).1

theorem mccrimmon_identity_11 (x y : H3Octonion ℝ) :
    crossProduct (adjointQuad x) (adjointQuad y) + adjointQuad (crossProduct x y) =
      traceBilin (adjointQuad x) y • y + traceBilin (adjointQuad y) x • x :=
  (extract_master_linearization x y).2

theorem mccrimmon_identity_12 (x y z : H3Octonion ℝ) :
    crossProduct (adjointQuad x) (crossProduct y z) +
        crossProduct (crossProduct x y) (crossProduct x z) =
      traceBilin (adjointQuad x) y • z + traceBilin (adjointQuad x) z • y +
        traceBilin (crossProduct y z) x • x := by
  have h := mccrimmon_identity_11 x (y + z)
  have hy := mccrimmon_identity_11 x y
  have hz := mccrimmon_identity_11 x z
  rw [adjointQuad_add,
    crossProduct_add_right (adjointQuad x) (adjointQuad y + crossProduct y z) (adjointQuad z),
    crossProduct_add_right (adjointQuad x) (adjointQuad y) (crossProduct y z),
    crossProduct_add_right x y z,
    adjointQuad_add, traceBilin_add_right, traceBilin_add_left, traceBilin_add_left] at h
  have hdiff := congrArg₂ (fun A B : H3Octonion ℝ => A - B)
    (congrArg₂ (fun A B : H3Octonion ℝ => A - B) h hy) hz
  convert hdiff using 1
  · module
  · rw [add_smul, add_smul, smul_add, smul_add, traceBilin_symm (crossProduct y z) x]
    module

theorem mccrimmon_identity_13 (x : H3Octonion ℝ) :
    traceBilin (adjointQuad x) x = 3 * normCubic x := by
  have h := normCubic_add x x
  rw [show x + x = (2 : ℝ) • x by module, normCubic_smul, traceBilin_symm x (adjointQuad x)] at h
  linarith

theorem mccrimmon_identity_15 (x y z : H3Octonion ℝ) :
    traceBilin (crossProduct x y) z = traceBilin x (crossProduct y z) := by
  have hl := normCubic_add (x + y) z
  have hr := normCubic_add x (y + z)
  rw [normCubic_add x y, adjointQuad_add, traceBilin_add_left, traceBilin_add_left,
    traceBilin_add_left] at hl
  rw [normCubic_add y z, adjointQuad_add, traceBilin_add_right, traceBilin_add_right,
    traceBilin_add_right] at hr
  have heq : normCubic (x + y + z) = normCubic (x + (y + z)) := by rw [add_assoc]
  rw [hl, hr] at heq
  rw [traceBilin_symm x (adjointQuad z), traceBilin_symm y (adjointQuad z),
    traceBilin_symm (adjointQuad x) y, traceBilin_symm (adjointQuad x) z,
    traceBilin_symm x (adjointQuad y)] at heq
  linarith

theorem mccrimmon_identity_16 (x y : H3Octonion ℝ) :
    linearTrace (crossProduct x y) = linearTrace x * linearTrace y - traceBilin x y := by
  have h := mccrimmon_identity_15 x y 1
  rw [← traceBilin_one, h, crossProduct_one,
    traceBilin_sub_right, traceBilin_smul_right, traceBilin_one, traceBilin_symm]
  ring

theorem mccrimmon_identity_17 (x y : H3Octonion ℝ) :
    U x (crossProduct x y) = traceBilin (adjointQuad x) y • x - normCubic x • y := by
  have ht := mccrimmon_identity_15 x x y
  rw [crossProduct_self, traceBilin_smul_left] at ht
  rw [U, mccrimmon_identity_10, ht.symm]
  module

theorem mccrimmon_identity_18 (x : H3Octonion ℝ) :
    crossProduct (adjointQuad x) x =
      (linearTrace (adjointQuad x) * linearTrace x - normCubic x) • (1 : H3Octonion ℝ) -
        linearTrace (adjointQuad x) • x - linearTrace x • adjointQuad x := by
  have h2 : linearTrace x • crossProduct (adjointQuad x) 1 - crossProduct (adjointQuad x) x =
      normCubic x • (1 : H3Octonion ℝ) + traceBilin (adjointQuad x) 1 • x := by
    have hh := mccrimmon_identity_10 x 1
    rw [crossProduct_one, sub_eq_add_neg, crossProduct_add_right, crossProduct_smul_right,
      show crossProduct (adjointQuad x) (-x) = -(crossProduct (adjointQuad x) x) by
        rw [show -x = (-1 : ℝ) • x by module, crossProduct_smul_right]; module] at hh
    simpa [sub_eq_add_neg] using hh
  rw [crossProduct_one, traceBilin_one] at h2
  have hsolve := congrArg (fun W : H3Octonion ℝ => linearTrace x • (linearTrace (adjointQuad x) • 1 - adjointQuad x) - W) h2
  have h1 : linearTrace x • (linearTrace (adjointQuad x) • 1 - adjointQuad x) -
      (linearTrace x • (linearTrace (adjointQuad x) • 1 - adjointQuad x) - crossProduct (adjointQuad x) x) =
      crossProduct (adjointQuad x) x := by module
  rw [← h1, hsolve, smul_sub, smul_smul, mul_comm (linearTrace x) (linearTrace (adjointQuad x))]
  module

private theorem mccrimmon_identity_18_polar (x y : H3Octonion ℝ) :
    crossProduct (adjointQuad x) y + crossProduct (crossProduct x y) x =
      (linearTrace (crossProduct x y) * linearTrace x +
          linearTrace (adjointQuad x) * linearTrace y - traceBilin (adjointQuad x) y) •
          (1 : H3Octonion ℝ) -
        linearTrace (crossProduct x y) • x - linearTrace (adjointQuad x) • y -
        linearTrace y • adjointQuad x - linearTrace x • crossProduct x y := by
  let F : H3Octonion ℝ → H3Octonion ℝ := fun z =>
    crossProduct (adjointQuad z) z -
      ((linearTrace (adjointQuad z) * linearTrace z - normCubic z) • (1 : H3Octonion ℝ) -
        linearTrace (adjointQuad z) • z - linearTrace z • adjointQuad z)
  have hF0 : ∀ z, F z = 0 := fun z => sub_eq_zero.mpr (mccrimmon_identity_18 z)
  have hsub_adj : adjointQuad (x - y) = adjointQuad x - crossProduct x y + adjointQuad y := by
    rw [sub_eq_add_neg, show -y = (-1 : ℝ) • y by module, adjointQuad_add,
      crossProduct_smul_right, adjointQuad_smul]
    module
  have hn_sub : normCubic (x - y) =
      normCubic x - traceBilin (adjointQuad x) y + traceBilin x (adjointQuad y) - normCubic y := by
    rw [sub_eq_add_neg, show -y = (-1 : ℝ) • y by module, normCubic_add, adjointQuad_smul,
      normCubic_smul, traceBilin_smul_right, traceBilin_smul_right]
    ring
  have hcross_sub_left : ∀ A B C : H3Octonion ℝ,
      crossProduct (A - B) C = crossProduct A C - crossProduct B C := fun A B C => by
    rw [sub_eq_add_neg, show -B = (-1 : ℝ) • B by module, crossProduct_add_left,
      crossProduct_smul_left]
    module
  have hcross_sub_right : ∀ A B C : H3Octonion ℝ,
      crossProduct A (B - C) = crossProduct A B - crossProduct A C := fun A B C => by
    rw [sub_eq_add_neg, show -C = (-1 : ℝ) • C by module, crossProduct_add_right,
      crossProduct_smul_right]
    module
  have hcomb : F (x + y) - F (x - y) - (2 : ℝ) • F y = 0 := by
    rw [hF0 (x + y), hF0 (x - y), hF0 y, sub_zero, smul_zero, sub_zero]
  have hexp : F (x + y) - F (x - y) - (2 : ℝ) • F y =
      (2 : ℝ) • (crossProduct (adjointQuad x) y + crossProduct (crossProduct x y) x -
        ((linearTrace (crossProduct x y) * linearTrace x +
            linearTrace (adjointQuad x) * linearTrace y - traceBilin (adjointQuad x) y) •
            (1 : H3Octonion ℝ) -
          linearTrace (crossProduct x y) • x - linearTrace (adjointQuad x) • y -
          linearTrace y • adjointQuad x - linearTrace x • crossProduct x y)) := by
    dsimp [F]
    rw [adjointQuad_add, hsub_adj, normCubic_add, hn_sub]
    simp only [crossProduct_add_left, crossProduct_add_right, hcross_sub_left, hcross_sub_right,
      linearTrace_add, linearTrace_sub]
    simp only [add_smul, sub_smul, smul_add, smul_sub]
    module
  rw [hexp] at hcomb
  exact sub_eq_zero.mp ((smul_eq_zero.mp hcomb).resolve_left (by norm_num))

theorem mccrimmon_identity_18_full_polarization (x y z : H3Octonion ℝ) :
    crossProduct (crossProduct x y) z + crossProduct (crossProduct x z) y +
        crossProduct (crossProduct y z) x =
      (linearTrace (crossProduct x y) * linearTrace z +
          linearTrace (crossProduct x z) * linearTrace y +
          linearTrace (crossProduct y z) * linearTrace x -
          traceBilin (crossProduct x y) z) • (1 : H3Octonion ℝ) -
        linearTrace (crossProduct x y) • z - linearTrace (crossProduct x z) • y -
        linearTrace (crossProduct y z) • x - linearTrace z • crossProduct x y -
        linearTrace y • crossProduct x z - linearTrace x • crossProduct y z := by
  let G : H3Octonion ℝ → H3Octonion ℝ := fun u =>
    crossProduct (adjointQuad u) z + crossProduct (crossProduct u z) u -
      ((linearTrace (crossProduct u z) * linearTrace u +
          linearTrace (adjointQuad u) * linearTrace z - traceBilin (adjointQuad u) z) •
          (1 : H3Octonion ℝ) -
        linearTrace (crossProduct u z) • u - linearTrace (adjointQuad u) • z -
        linearTrace z • adjointQuad u - linearTrace u • crossProduct u z)
  have hG0 : ∀ u, G u = 0 := fun u => sub_eq_zero.mpr (mccrimmon_identity_18_polar u z)
  have hdiff : G (x + y) - G x - G y = 0 := by
    rw [hG0 (x + y), hG0 x, hG0 y, sub_zero, sub_zero]
  have hexp : G (x + y) - G x - G y =
      crossProduct (crossProduct x y) z + crossProduct (crossProduct x z) y +
        crossProduct (crossProduct y z) x -
      ((linearTrace (crossProduct x y) * linearTrace z +
          linearTrace (crossProduct x z) * linearTrace y +
          linearTrace (crossProduct y z) * linearTrace x -
          traceBilin (crossProduct x y) z) • (1 : H3Octonion ℝ) -
        linearTrace (crossProduct x y) • z - linearTrace (crossProduct x z) • y -
        linearTrace (crossProduct y z) • x - linearTrace z • crossProduct x y -
        linearTrace y • crossProduct x z - linearTrace x • crossProduct y z) := by
    dsimp [G]
    rw [adjointQuad_add]
    simp only [crossProduct_add_left, crossProduct_add_right, traceBilin_add_left,
      linearTrace_add, add_smul, smul_add]
    module
  rw [hexp] at hdiff
  exact sub_eq_zero.mp hdiff

theorem mccrimmon_identity_19 (x y : H3Octonion ℝ) :
    crossProduct x (crossProduct (adjointQuad x) y) =
      normCubic x • y + traceBilin x y • adjointQuad x := by
  have h18 := mccrimmon_identity_18 x
  have hsub : ∀ A B C : H3Octonion ℝ,
      crossProduct (A - B) C = crossProduct A C - crossProduct B C := fun A B C => by
    rw [sub_eq_add_neg, show -B = (-1 : ℝ) • B by module, crossProduct_add_left,
      crossProduct_smul_left]; module
  have h10 : crossProduct (crossProduct x y) (adjointQuad x) =
      normCubic x • y + traceBilin (adjointQuad x) y • x := by
    rw [crossProduct_symm (crossProduct x y) (adjointQuad x)]
    exact mccrimmon_identity_10 x y
  have htr : traceBilin (crossProduct x (adjointQuad x)) y =
      (linearTrace (adjointQuad x) * linearTrace x - normCubic x) * linearTrace y -
        linearTrace (adjointQuad x) * traceBilin x y -
        linearTrace x * traceBilin (adjointQuad x) y := by
    rw [crossProduct_symm x (adjointQuad x), h18]
    simp only [traceBilin_sub_left, traceBilin_smul_left, traceBilin_one_left]
  have htr_cx : linearTrace (crossProduct x (adjointQuad x)) =
      linearTrace x * linearTrace (adjointQuad x) - 3 * normCubic x := by
    rw [mccrimmon_identity_16, traceBilin_symm, mccrimmon_identity_13]
  have htr_xy : linearTrace (crossProduct x y) = linearTrace x * linearTrace y - traceBilin x y :=
    mccrimmon_identity_16 x y
  have htr_ay : linearTrace (crossProduct (adjointQuad x) y) =
      linearTrace (adjointQuad x) * linearTrace y - traceBilin (adjointQuad x) y :=
    mccrimmon_identity_16 (adjointQuad x) y
  have hc1 : crossProduct ((linearTrace (adjointQuad x) * linearTrace x - normCubic x) •
        (1 : H3Octonion ℝ) - linearTrace (adjointQuad x) • x - linearTrace x • adjointQuad x) y =
      (linearTrace (adjointQuad x) * linearTrace x - normCubic x) • (linearTrace y • (1 : H3Octonion ℝ) - y) -
        linearTrace (adjointQuad x) • crossProduct x y -
        linearTrace x • crossProduct (adjointQuad x) y := by
    rw [hsub, hsub, crossProduct_smul_left, crossProduct_smul_left, crossProduct_smul_left,
      crossProduct_symm 1 y, crossProduct_one]
  have hfull := mccrimmon_identity_18_full_polarization x (adjointQuad x) y
  rw [htr, htr_cx, htr_xy, htr_ay, crossProduct_symm x (adjointQuad x), h18, hc1, h10,
    crossProduct_symm (crossProduct (adjointQuad x) y) x] at hfull
  have hiso := congrArg (fun W : H3Octonion ℝ =>
      W - ((linearTrace (adjointQuad x) * linearTrace x - normCubic x) • (linearTrace y • (1 : H3Octonion ℝ) - y) -
        linearTrace (adjointQuad x) • crossProduct x y -
        linearTrace x • crossProduct (adjointQuad x) y +
        (normCubic x • y + traceBilin (adjointQuad x) y • x))) hfull
  have hnorm : crossProduct x (crossProduct (adjointQuad x) y) =
      ((linearTrace (adjointQuad x) * linearTrace x - normCubic x) • (linearTrace y • (1 : H3Octonion ℝ) - y) -
        linearTrace (adjointQuad x) • crossProduct x y -
        linearTrace x • crossProduct (adjointQuad x) y +
        (normCubic x • y + traceBilin (adjointQuad x) y • x)) +
      crossProduct x (crossProduct (adjointQuad x) y) -
      ((linearTrace (adjointQuad x) * linearTrace x - normCubic x) • (linearTrace y • (1 : H3Octonion ℝ) - y) -
        linearTrace (adjointQuad x) • crossProduct x y -
        linearTrace x • crossProduct (adjointQuad x) y +
        (normCubic x • y + traceBilin (adjointQuad x) y • x)) := by module
  rw [hnorm, hiso]
  simp only [smul_sub, add_smul, sub_smul, smul_smul]
  module

private theorem T_one_self (x : H3Octonion ℝ) :
    T x 1 x = (2 * linearTrace x) • x + (2 : ℝ) • adjointQuad x -
      (2 * linearTrace (adjointQuad x)) • (1 : H3Octonion ℝ) := by
  rw [T_one_formula, crossProduct_self, linearTrace_smul]
  module

private theorem T_one_one (x : H3Octonion ℝ) : T x 1 1 = (2 : ℝ) • x := by
  rw [T_one_formula, crossProduct_one, linearTrace_one, linearTrace_sub, linearTrace_smul,
    linearTrace_one]
  module

private theorem bilin_X_cross_XZ (x z : H3Octonion ℝ) :
    traceBilin x (crossProduct x z) = 2 * traceBilin (adjointQuad x) z := by
  rw [← mccrimmon_identity_15, crossProduct_self, traceBilin_smul_left]

private theorem bilin_X_cross_adjZ (x z : H3Octonion ℝ) :
    traceBilin x (crossProduct (adjointQuad x) z) =
      (linearTrace (adjointQuad x) * linearTrace x - normCubic x) * linearTrace z -
        linearTrace (adjointQuad x) * traceBilin x z -
        linearTrace x * traceBilin (adjointQuad x) z := by
  rw [← mccrimmon_identity_15 x (adjointQuad x) z, crossProduct_symm x (adjointQuad x),
    mccrimmon_identity_18]
  simp only [traceBilin_sub_left, traceBilin_smul_left, traceBilin_one_left]

private theorem linearTrace_cross_X_XZ (x z : H3Octonion ℝ) :
    linearTrace (crossProduct x (crossProduct x z)) =
      linearTrace x * linearTrace (crossProduct x z) - 2 * traceBilin (adjointQuad x) z := by
  rw [mccrimmon_identity_16, bilin_X_cross_XZ]

private theorem cross_X_cross_X_Z (x z : H3Octonion ℝ) :
    crossProduct x (crossProduct x z) =
      (linearTrace z * linearTrace (adjointQuad x) + linearTrace x * linearTrace (crossProduct x z) -
          traceBilin (adjointQuad x) z) • (1 : H3Octonion ℝ) -
        linearTrace z • adjointQuad x - crossProduct (adjointQuad x) z -
        linearTrace x • crossProduct x z - linearTrace (adjointQuad x) • z +
        (traceBilin x z - linearTrace z * linearTrace x) • x := by
  have h := mccrimmon_identity_12 x 1 z
  rw [crossProduct_symm 1 z, crossProduct_one, crossProduct_one,
    traceBilin_one, crossProduct_symm (adjointQuad x) (linearTrace z • (1 : H3Octonion ℝ) - z)] at h
  have h1 : crossProduct (linearTrace z • (1 : H3Octonion ℝ) - z) (adjointQuad x) =
      linearTrace z • (linearTrace (adjointQuad x) • (1 : H3Octonion ℝ) - adjointQuad x) -
        crossProduct (adjointQuad x) z := by
    rw [sub_eq_add_neg, show -z = (-1 : ℝ) • z by module, crossProduct_add_left,
      crossProduct_smul_left, crossProduct_smul_left, crossProduct_symm 1, crossProduct_one,
      crossProduct_symm z]
    module
  have h2 : crossProduct (linearTrace x • (1 : H3Octonion ℝ) - x) (crossProduct x z) =
      linearTrace x • (linearTrace (crossProduct x z) • (1 : H3Octonion ℝ) - crossProduct x z) -
        crossProduct x (crossProduct x z) := by
    rw [sub_eq_add_neg, show -x = (-1 : ℝ) • x by module, crossProduct_add_left,
      crossProduct_smul_left, crossProduct_smul_left, crossProduct_symm 1, crossProduct_one]
    module
  have htr : traceBilin (linearTrace z • (1 : H3Octonion ℝ) - z) x =
      linearTrace z * linearTrace x - traceBilin x z := by
    rw [traceBilin_sub_left, traceBilin_smul_left, traceBilin_one_left, traceBilin_symm z x]
  rw [h1, h2, htr] at h
  have hiso := congrArg (fun W : H3Octonion ℝ =>
      (linearTrace z • (linearTrace (adjointQuad x) • (1 : H3Octonion ℝ) - adjointQuad x) -
        crossProduct (adjointQuad x) z) +
      linearTrace x • (linearTrace (crossProduct x z) • (1 : H3Octonion ℝ) - crossProduct x z) - W) h
  have hl : (linearTrace z • (linearTrace (adjointQuad x) • (1 : H3Octonion ℝ) - adjointQuad x) -
        crossProduct (adjointQuad x) z) +
      linearTrace x • (linearTrace (crossProduct x z) • (1 : H3Octonion ℝ) - crossProduct x z) -
      ((linearTrace z • (linearTrace (adjointQuad x) • (1 : H3Octonion ℝ) - adjointQuad x) -
        crossProduct (adjointQuad x) z) +
      (linearTrace x • (linearTrace (crossProduct x z) • (1 : H3Octonion ℝ) - crossProduct x z) -
        crossProduct x (crossProduct x z))) = crossProduct x (crossProduct x z) := by module
  rw [hl] at hiso
  rw [hiso]
  simp only [smul_sub, add_smul, sub_smul, smul_smul]
  module

theorem four_U (x z : H3Octonion ℝ) :
    (4 : ℝ) • U x z = (2 : ℝ) • T x 1 (T x 1 z) - T (T x 1 x) 1 z := by
  have hTxz : T x 1 z = linearTrace x • z + linearTrace z • x + crossProduct x z -
      linearTrace (crossProduct x z) • (1 : H3Octonion ℝ) := T_one_formula x z
  have hL1 : T x 1 (T x 1 z) =
      linearTrace x • T x 1 z + linearTrace z • T x 1 x +
        (linearTrace x • crossProduct x z + linearTrace (crossProduct x z) • x +
          crossProduct x (crossProduct x z) -
          linearTrace (crossProduct x (crossProduct x z)) • (1 : H3Octonion ℝ)) -
        linearTrace (crossProduct x z) • T x 1 1 := by
    conv_lhs => rw [hTxz]
    rw [sub_eq_add_neg, show -(linearTrace (crossProduct x z) • (1 : H3Octonion ℝ)) =
        (-linearTrace (crossProduct x z)) • (1 : H3Octonion ℝ) by module]
    simp only [T_add_outer, T_smul_outer]
    rw [T_one_formula x (crossProduct x z)]
    module
  have hTxx : T x 1 x = (2 * linearTrace x) • x + (2 : ℝ) • adjointQuad x -
      (2 * linearTrace (adjointQuad x)) • (1 : H3Octonion ℝ) := T_one_self x
  have hL2 : T (T x 1 x) 1 z =
      (2 * linearTrace x) • T x 1 z + (2 : ℝ) • T (adjointQuad x) 1 z -
        (2 * linearTrace (adjointQuad x)) • T 1 1 z := by
    rw [hTxx, sub_eq_add_neg, show -((2 * linearTrace (adjointQuad x)) • (1 : H3Octonion ℝ)) =
        (-(2 * linearTrace (adjointQuad x))) • (1 : H3Octonion ℝ) by module]
    simp only [T_add_left, T_smul_left]
    module
  have hT11z : T 1 1 z = (2 : ℝ) • z := by rw [T_symm_outer, T_one_one]
  have hTadjz : T (adjointQuad x) 1 z =
      linearTrace (adjointQuad x) • z + linearTrace z • adjointQuad x + crossProduct (adjointQuad x) z -
        (linearTrace (adjointQuad x) * linearTrace z - traceBilin (adjointQuad x) z) •
          (1 : H3Octonion ℝ) := by
    rw [T_one_formula, mccrimmon_identity_16]
  rw [hL1, hL2, hT11z, hTadjz, T_one_one, hTxx, linearTrace_cross_X_XZ, cross_X_cross_X_Z,
    mccrimmon_identity_16]
  simp only [U, smul_add, smul_sub, add_smul, sub_smul, smul_smul]
  module

theorem P_comm_U (x z : H3Octonion ℝ) :
    T x 1 (U x z) = U x (T x 1 z) := by
  have hcr_sub : ∀ A B C : H3Octonion ℝ,
      crossProduct A (B - C) = crossProduct A B - crossProduct A C := fun A B C => by
    rw [sub_eq_add_neg, show -C = (-1 : ℝ) • C by module, crossProduct_add_right,
      crossProduct_smul_right]; module
  have htr_adj : linearTrace (adjointQuad x) =
      (1 / 2 : ℝ) * (linearTrace x * linearTrace x - traceBilin x x) := by
    have h16 := mccrimmon_identity_16 x x
    rw [crossProduct_self, linearTrace_smul] at h16
    linarith
  conv_lhs => rw [T_one_formula, mccrimmon_identity_16]
  simp only [U]
  rw [T_one_formula x z]
  simp only [linearTrace_sub, linearTrace_smul, traceBilin_sub_right, traceBilin_add_right,
    traceBilin_smul_right, traceBilin_one, hcr_sub, crossProduct_add_right, crossProduct_smul_right,
    crossProduct_one, crossProduct_self, mccrimmon_identity_16, mccrimmon_identity_18,
    mccrimmon_identity_10, mccrimmon_identity_19, bilin_X_cross_XZ, bilin_X_cross_adjZ, htr_adj]
  module

end McCrimmonAndQuadraticIdentities

section JordanAlgebraInstance

/-- Canonical Jordan product `x * y = (1 / 2) • T x 1 y` on `H3Octonion ℝ`. -/
def candidateJordanMul (x y : H3Octonion ℝ) : H3Octonion ℝ :=
  (1 / 2 : ℝ) • T x 1 y

instance : Mul (H3Octonion ℝ) := ⟨candidateJordanMul⟩

theorem mul_def (x y : H3Octonion ℝ) : x * y = (1 / 2 : ℝ) • T x 1 y := rfl

theorem mul_comm (x y : H3Octonion ℝ) : x * y = y * x := by
  simp only [mul_def, T_symm_outer]

theorem mul_trace_formula (x y : H3Octonion ℝ) :
    x * y = (1 / 2 : ℝ) • (linearTrace x • y + linearTrace y • x -
      linearTrace (crossProduct x y) • (1 : H3Octonion ℝ) + crossProduct x y) := by
  rw [mul_def, T_one_formula]
  congr 1
  module

instance : NonUnitalNonAssocCommRing (H3Octonion ℝ) where
  left_distrib x y z := by
    simp only [mul_def, T_add_outer, smul_add]
  right_distrib x y z := by
    simp only [mul_def, T_add_left, smul_add]
  zero_mul x := by
    simp [mul_def, T_outer_formula]
  mul_zero x := by
    simp [mul_def, T_outer_formula]
  mul_comm := mul_comm

instance : SMulCommClass ℝ (H3Octonion ℝ) (H3Octonion ℝ) where
  smul_comm r x y := by
    change r • (x * y) = x * (r • y)
    rw [mul_def, mul_def, T_smul_outer, smul_comm r (1 / 2 : ℝ)]

instance : IsScalarTower ℝ (H3Octonion ℝ) (H3Octonion ℝ) where
  smul_assoc r x y := by
    change (r • x) * y = r • (x * y)
    rw [mul_def, mul_def, T_smul_left, smul_comm r (1 / 2 : ℝ)]

theorem h3Octonion_jordan_identity (a b : H3Octonion ℝ) :
    (a * b) * (a * a) = a * (b * (a * a)) := by
  have h1 : (4 : ℝ) • U a (T a 1 b) = (2 : ℝ) • T a 1 (T a 1 (T a 1 b)) - T (T a 1 a) 1 (T a 1 b) :=
    four_U a (T a 1 b)
  have h2 : (4 : ℝ) • T a 1 (U a b) = (2 : ℝ) • T a 1 (T a 1 (T a 1 b)) - T a 1 (T (T a 1 a) 1 b) := by
    have h4 := congrArg (fun W : H3Octonion ℝ => T a 1 W) (four_U a b)
    rw [T_smul_outer, sub_eq_add_neg, show -(T (T a 1 a) 1 b) = (-1 : ℝ) • T (T a 1 a) 1 b by module,
      T_add_outer, T_smul_outer, T_smul_outer] at h4
    convert h4 using 1
    module
  have hcomm : U a (T a 1 b) = T a 1 (U a b) := (P_comm_U a b).symm
  have hsub : (2 : ℝ) • T a 1 (T a 1 (T a 1 b)) - T (T a 1 a) 1 (T a 1 b) =
      (2 : ℝ) • T a 1 (T a 1 (T a 1 b)) - T a 1 (T (T a 1 a) 1 b) := by
    rw [← h1, hcomm, h2]
  have hT : T (T a 1 a) 1 (T a 1 b) = T a 1 (T (T a 1 a) 1 b) := by
    have he := congrArg (fun W => (2 : ℝ) • T a 1 (T a 1 (T a 1 b)) - W) hsub
    simp only [sub_sub_cancel] at he
    exact he
  simp only [mul_def, T_smul_left, T_smul_outer, smul_smul]
  have h8 : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (1 / 2 : ℝ)) = 1 / 8 := by norm_num
  rw [h8, T_symm_outer (T a 1 b) 1 (T a 1 a), hT, T_symm_outer (T a 1 a) 1 b]

instance : IsCommJordan (H3Octonion ℝ) where
  lmul_comm_rmul_rmul x y := by
    have h := h3Octonion_jordan_identity x y
    simpa [mul_comm] using h

theorem jordanU_eq_U (x y : H3Octonion ℝ) :
    (2 : ℝ) • (x * (x * y)) - (x * x) * y = U x y := by
  have h := four_U x y
  have h4 : (4 : ℝ) • ((2 : ℝ) • (x * (x * y)) - (x * x) * y) = (4 : ℝ) • U x y := by
    simp only [mul_def, T_smul_left, T_smul_outer, smul_sub, smul_smul]
    rw [h]
    module
  have hsub : (4 : ℝ) • ((2 : ℝ) • (x * (x * y)) - (x * x) * y - U x y) = 0 := by
    rw [smul_sub, h4, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (by norm_num))

theorem one_mul_h3Octonion (x : H3Octonion ℝ) : (1 : H3Octonion ℝ) * x = x := by
  rw [mul_def, T_symm_outer, T_one_formula, linearTrace_one, crossProduct_one,
    linearTrace_sub, linearTrace_smul, linearTrace_one]
  module

theorem h3Octonion_mul_one (x : H3Octonion ℝ) : x * (1 : H3Octonion ℝ) = x := by
  rw [mul_comm, one_mul_h3Octonion]

theorem h3octonion_jordan_mul_adjoint_eq_norm_one (x : H3Octonion ℝ) :
    x * adjointQuad x = normCubic x • (1 : H3Octonion ℝ) := by
  rw [mul_trace_formula, mccrimmon_identity_16, traceBilin_symm x (adjointQuad x),
    mccrimmon_identity_13 x, crossProduct_symm x (adjointQuad x), mccrimmon_identity_18 x]
  module

theorem h3octonion_mul_self_eq_adjoint (x : H3Octonion ℝ) :
    x * x = linearTrace x • x - linearTrace (adjointQuad x) • (1 : H3Octonion ℝ) + adjointQuad x := by
  rw [mul_trace_formula, crossProduct_self, linearTrace_smul]
  module

end JordanAlgebraInstance

section EuclideanAndFormalReality

/-- Positive-definiteness of `traceBilin` on `H₃(𝕆)` (unique to the compact real form). -/
theorem traceBilin_self_eq (x : H3Octonion ℝ) :
    traceBilin x x =
      x.α₁ * x.α₁ + x.α₂ * x.α₂ + x.α₃ * x.α₃ +
        2 * CompactOctonion.norm x.a + 2 * CompactOctonion.norm x.b + 2 * CompactOctonion.norm x.c := by
  change x.α₁ * x.α₁ + x.α₂ * x.α₂ + x.α₃ * x.α₃ +
      CompactOctonion.bilin x.a x.a + CompactOctonion.bilin x.b x.b +
      CompactOctonion.bilin x.c x.c = _
  rw [CompactOctonion.bilin_self, CompactOctonion.bilin_self, CompactOctonion.bilin_self]

theorem traceBilin_self_nonneg (x : H3Octonion ℝ) : 0 ≤ traceBilin x x := by
  rw [traceBilin_self_eq]
  have h1 := mul_self_nonneg x.α₁
  have h2 := mul_self_nonneg x.α₂
  have h3 := mul_self_nonneg x.α₃
  have ha := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CompactOctonion.norm_nonneg x.a)
  have hb := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CompactOctonion.norm_nonneg x.b)
  have hc := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CompactOctonion.norm_nonneg x.c)
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) ha) hb) hc

theorem traceBilin_self_eq_zero_iff (x : H3Octonion ℝ) : traceBilin x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [traceBilin_self_eq] at h
    have h1 := mul_self_nonneg x.α₁
    have h2 := mul_self_nonneg x.α₂
    have h3 := mul_self_nonneg x.α₃
    have ha := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CompactOctonion.norm_nonneg x.a)
    have hb := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CompactOctonion.norm_nonneg x.b)
    have hc := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (CompactOctonion.norm_nonneg x.c)
    have h12 : 0 ≤ x.α₁ * x.α₁ + x.α₂ * x.α₂ := add_nonneg h1 h2
    have h123 : 0 ≤ x.α₁ * x.α₁ + x.α₂ * x.α₂ + x.α₃ * x.α₃ := add_nonneg h12 h3
    have h123a : 0 ≤ x.α₁ * x.α₁ + x.α₂ * x.α₂ + x.α₃ * x.α₃ + 2 * CompactOctonion.norm x.a :=
      add_nonneg h123 ha
    have h123ab : 0 ≤ x.α₁ * x.α₁ + x.α₂ * x.α₂ + x.α₃ * x.α₃ + 2 * CompactOctonion.norm x.a +
        2 * CompactOctonion.norm x.b := add_nonneg h123a hb
    have p1 := (add_eq_zero_iff_of_nonneg h123ab hc).mp h
    have p2 := (add_eq_zero_iff_of_nonneg h123a hb).mp p1.1
    have p3 := (add_eq_zero_iff_of_nonneg h123 ha).mp p2.1
    have p4 := (add_eq_zero_iff_of_nonneg h12 h3).mp p3.1
    have p5 := (add_eq_zero_iff_of_nonneg h1 h2).mp p4.1
    apply ext_h3
    · exact mul_self_eq_zero.mp p5.1
    · exact mul_self_eq_zero.mp p5.2
    · exact mul_self_eq_zero.mp p4.2
    · exact (CompactOctonion.norm_eq_zero_iff x.a).mp ((mul_eq_zero.mp p3.2).resolve_left (by norm_num))
    · exact (CompactOctonion.norm_eq_zero_iff x.b).mp ((mul_eq_zero.mp p2.2).resolve_left (by norm_num))
    · exact (CompactOctonion.norm_eq_zero_iff x.c).mp ((mul_eq_zero.mp p1.2).resolve_left (by norm_num))
  · rintro rfl
    simp

theorem traceBilin_nondegenerate (x : H3Octonion ℝ) (hx : ∀ y : H3Octonion ℝ, traceBilin x y = 0) :
    x = 0 :=
  (traceBilin_self_eq_zero_iff x).mp (hx x)

theorem eq_of_traceBilin_left_eq {x y : H3Octonion ℝ}
    (h : ∀ z : H3Octonion ℝ, traceBilin x z = traceBilin y z) : x = y := by
  apply sub_eq_zero.mp
  apply traceBilin_nondegenerate
  intro z
  rw [traceBilin_sub_left, h z, sub_self]

theorem linearTrace_jordanMul (x y : H3Octonion ℝ) :
    linearTrace (x * y) = traceBilin x y := by
  rw [mul_trace_formula, linearTrace_smul, linearTrace_add, linearTrace_sub, linearTrace_add,
    linearTrace_smul, linearTrace_smul, linearTrace_smul, linearTrace_one, mccrimmon_identity_16]
  ring

/-- **Formal Reality of `H₃(𝕆)`**: in the compact Albert algebra, a sum of squares vanishes
only when both summands vanish (`x * x + y * y = 0 → x = 0 ∧ y = 0`). -/
theorem formal_reality (x y : H3Octonion ℝ) (h : x * x + y * y = 0) :
    x = 0 ∧ y = 0 := by
  have htr : linearTrace (x * x + y * y) = 0 := by rw [h, linearTrace_zero]
  rw [linearTrace_add, linearTrace_jordanMul, linearTrace_jordanMul] at htr
  have h0 := (add_eq_zero_iff_of_nonneg (traceBilin_self_nonneg x) (traceBilin_self_nonneg y)).mp htr
  exact ⟨(traceBilin_self_eq_zero_iff x).mp h0.1, (traceBilin_self_eq_zero_iff y).mp h0.2⟩

/-- Explicit nonzero nilpotent (`w * w = 0`) witness in the split Albert algebra `H3Zorn ℝ`. -/
private def splitNilpotentWitness : H3Zorn ℝ :=
  ⟨0, 0, 0, ⟨1, 0, 0, 0⟩, 0, 0⟩

private theorem splitNilpotentWitness_ne_zero : splitNilpotentWitness ≠ 0 := by
  intro h
  have ha : splitNilpotentWitness.a.a = (0 : H3Zorn ℝ).a.a := congrArg (fun x => x.a.a) h
  change (1 : ℝ) = 0 at ha
  exact one_ne_zero ha

private theorem splitNilpotentWitness_mul_self :
    splitNilpotentWitness * splitNilpotentWitness = 0 := by
  change InfoGeometry.Algebra.candidateJordanMul splitNilpotentWitness splitNilpotentWitness = 0
  rw [InfoGeometry.Algebra.candidateJordanMul_trace_formula]
  have htr : H3Zorn.linearTrace splitNilpotentWitness = 0 := by
    simp [H3Zorn.linearTrace, splitNilpotentWitness]
  have hadj : H3Zorn.adjointQuad splitNilpotentWitness = 0 := by
    apply H3Zorn.ext_h3 <;>
      simp [H3Zorn.adjointQuad, splitNilpotentWitness, ZornVectorMatrix.norm,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.sub,
        ZornVectorMatrix.add, ZornVectorMatrix.neg,
        ZornVectorMatrix.smul, ZornVec3.dot, ZornVec3.cross, ZornVectorMatrix.zero]
  have hcross : H3Zorn.crossProduct splitNilpotentWitness splitNilpotentWitness = 0 := by
    rw [H3Zorn.crossProduct_self, hadj, smul_zero]
  have htr0 : H3Zorn.linearTrace (0 : H3Zorn ℝ) = 0 := by
    simp [H3Zorn.linearTrace]
  rw [htr, hcross, htr0]
  simp only [zero_smul, add_zero, sub_zero, smul_zero]

/-- **Real-Form Separation**: the compact Albert Jordan algebra `H₃(𝕆)` (`H3Octonion ℝ`)
and the split Albert Jordan algebra `H₃(𝕆_s)` (`H3Zorn ℝ`) are NOT isomorphic as
non-associative Jordan rings (hence not isomorphic as real Jordan algebras). -/
theorem no_jordanIso_H3Octonion_H3Zorn : IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) := by
  refine ⟨fun e => ?_⟩
  let x : H3Octonion ℝ := e.symm splitNilpotentWitness
  have hmul : e (x * x) = 0 := by
    rw [map_mul]
    simp only [x, RingEquiv.apply_symm_apply, splitNilpotentWitness_mul_self]
  have hx2 : x * x = 0 := e.injective (by rw [hmul, map_zero])
  have hx0 : x = 0 := (formal_reality x 0 (by simp [hx2])).1
  have hw0 : splitNilpotentWitness = 0 := by
    calc splitNilpotentWitness = e x := (e.apply_symm_apply splitNilpotentWitness).symm
      _ = e 0 := by rw [hx0]
      _ = 0 := map_zero e
  exact splitNilpotentWitness_ne_zero hw0

end EuclideanAndFormalReality

end H3Octonion

end InfoGeometry.Algebra



