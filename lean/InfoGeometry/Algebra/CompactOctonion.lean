/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Basic.Real.Basic

/-!
# Compact (Positive-Definite) Octonions `𝕆`

This module formalizes the real division octonions `CompactOctonion R` with positive-definite
Euclidean norm `∑ i, xᵢ²`, Fano-plane multiplication matching `OctonionCl8`, conjugation,
trace, alternative & Moufang laws, Degen's 8-square multiplicativity, multiplicative inverses
over `ℝ`, 8D orthonormal basis, and triviality of the pure-imaginary left nucleus.
-/

namespace InfoGeometry.Algebra

/-- Coordinate carrier for the compact (division) octonions over a ring `R`. -/
@[ext]
structure CompactOctonion (R : Type*) where
  e0 : R
  e1 : R
  e2 : R
  e3 : R
  e4 : R
  e5 : R
  e6 : R
  e7 : R
  deriving DecidableEq

namespace CompactOctonion

section CommRingLaws

variable {R : Type*} [CommRing R]

def add (x y : CompactOctonion R) : CompactOctonion R :=
  ⟨x.e0 + y.e0, x.e1 + y.e1, x.e2 + y.e2, x.e3 + y.e3,
   x.e4 + y.e4, x.e5 + y.e5, x.e6 + y.e6, x.e7 + y.e7⟩

def neg (x : CompactOctonion R) : CompactOctonion R :=
  ⟨-x.e0, -x.e1, -x.e2, -x.e3, -x.e4, -x.e5, -x.e6, -x.e7⟩

def zero : CompactOctonion R := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def one : CompactOctonion R := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

def sub (x y : CompactOctonion R) : CompactOctonion R := add x (neg y)

def smul (r : R) (x : CompactOctonion R) : CompactOctonion R :=
  ⟨r * x.e0, r * x.e1, r * x.e2, r * x.e3,
   r * x.e4, r * x.e5, r * x.e6, r * x.e7⟩

instance : Zero (CompactOctonion R) := ⟨zero⟩
instance : One (CompactOctonion R) := ⟨one⟩
instance : Add (CompactOctonion R) := ⟨add⟩
instance : Neg (CompactOctonion R) := ⟨neg⟩
instance : Sub (CompactOctonion R) := ⟨sub⟩
instance : SMul R (CompactOctonion R) := ⟨smul⟩

instance : AddCommGroup (CompactOctonion R) where
  add := add
  add_assoc x y z := by ext <;> change (_ + _) + _ = _ + (_ + _) <;> ring
  zero := zero
  zero_add x := by ext <;> change 0 + _ = _ <;> ring
  add_zero x := by ext <;> change _ + 0 = _ <;> ring
  neg := neg
  neg_add_cancel x := by ext <;> change -_ + _ = 0 <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_comm x y := by ext <;> change _ + _ = _ + _ <;> ring

instance : Module R (CompactOctonion R) where
  smul := smul
  one_smul x := by ext <;> change 1 * _ = _ <;> ring
  mul_smul r s x := by ext <;> change (r * s) * _ = r * (s * _) <;> ring
  smul_zero r := by ext <;> change r * 0 = 0 <;> ring
  smul_add r x y := by ext <;> change r * (_ + _) = r * _ + r * _ <;> ring
  add_smul r s x := by ext <;> change (r + s) * _ = r * _ + s * _ <;> ring
  zero_smul x := by ext <;> change 0 * _ = 0 <;> ring

@[simp] theorem zero_e0 : (0 : CompactOctonion R).e0 = 0 := rfl
@[simp] theorem zero_e1 : (0 : CompactOctonion R).e1 = 0 := rfl
@[simp] theorem zero_e2 : (0 : CompactOctonion R).e2 = 0 := rfl
@[simp] theorem zero_e3 : (0 : CompactOctonion R).e3 = 0 := rfl
@[simp] theorem zero_e4 : (0 : CompactOctonion R).e4 = 0 := rfl
@[simp] theorem zero_e5 : (0 : CompactOctonion R).e5 = 0 := rfl
@[simp] theorem zero_e6 : (0 : CompactOctonion R).e6 = 0 := rfl
@[simp] theorem zero_e7 : (0 : CompactOctonion R).e7 = 0 := rfl

@[simp] theorem one_e0 : (1 : CompactOctonion R).e0 = 1 := rfl
@[simp] theorem one_e1 : (1 : CompactOctonion R).e1 = 0 := rfl
@[simp] theorem one_e2 : (1 : CompactOctonion R).e2 = 0 := rfl
@[simp] theorem one_e3 : (1 : CompactOctonion R).e3 = 0 := rfl
@[simp] theorem one_e4 : (1 : CompactOctonion R).e4 = 0 := rfl
@[simp] theorem one_e5 : (1 : CompactOctonion R).e5 = 0 := rfl
@[simp] theorem one_e6 : (1 : CompactOctonion R).e6 = 0 := rfl
@[simp] theorem one_e7 : (1 : CompactOctonion R).e7 = 0 := rfl

@[simp] theorem add_e0 (x y : CompactOctonion R) : (x + y).e0 = x.e0 + y.e0 := rfl
@[simp] theorem add_e1 (x y : CompactOctonion R) : (x + y).e1 = x.e1 + y.e1 := rfl
@[simp] theorem add_e2 (x y : CompactOctonion R) : (x + y).e2 = x.e2 + y.e2 := rfl
@[simp] theorem add_e3 (x y : CompactOctonion R) : (x + y).e3 = x.e3 + y.e3 := rfl
@[simp] theorem add_e4 (x y : CompactOctonion R) : (x + y).e4 = x.e4 + y.e4 := rfl
@[simp] theorem add_e5 (x y : CompactOctonion R) : (x + y).e5 = x.e5 + y.e5 := rfl
@[simp] theorem add_e6 (x y : CompactOctonion R) : (x + y).e6 = x.e6 + y.e6 := rfl
@[simp] theorem add_e7 (x y : CompactOctonion R) : (x + y).e7 = x.e7 + y.e7 := rfl

@[simp] theorem neg_e0 (x : CompactOctonion R) : (-x).e0 = -x.e0 := rfl
@[simp] theorem neg_e1 (x : CompactOctonion R) : (-x).e1 = -x.e1 := rfl
@[simp] theorem neg_e2 (x : CompactOctonion R) : (-x).e2 = -x.e2 := rfl
@[simp] theorem neg_e3 (x : CompactOctonion R) : (-x).e3 = -x.e3 := rfl
@[simp] theorem neg_e4 (x : CompactOctonion R) : (-x).e4 = -x.e4 := rfl
@[simp] theorem neg_e5 (x : CompactOctonion R) : (-x).e5 = -x.e5 := rfl
@[simp] theorem neg_e6 (x : CompactOctonion R) : (-x).e6 = -x.e6 := rfl
@[simp] theorem neg_e7 (x : CompactOctonion R) : (-x).e7 = -x.e7 := rfl

@[simp] theorem smul_e0 (r : R) (x : CompactOctonion R) : (r • x).e0 = r * x.e0 := rfl
@[simp] theorem smul_e1 (r : R) (x : CompactOctonion R) : (r • x).e1 = r * x.e1 := rfl
@[simp] theorem smul_e2 (r : R) (x : CompactOctonion R) : (r • x).e2 = r * x.e2 := rfl
@[simp] theorem smul_e3 (r : R) (x : CompactOctonion R) : (r • x).e3 = r * x.e3 := rfl
@[simp] theorem smul_e4 (r : R) (x : CompactOctonion R) : (r • x).e4 = r * x.e4 := rfl
@[simp] theorem smul_e5 (r : R) (x : CompactOctonion R) : (r • x).e5 = r * x.e5 := rfl
@[simp] theorem smul_e6 (r : R) (x : CompactOctonion R) : (r • x).e6 = r * x.e6 := rfl
@[simp] theorem smul_e7 (r : R) (x : CompactOctonion R) : (r • x).e7 = r * x.e7 := rfl

/-- Standard Fano multiplication following triples `(1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3)`. -/
def mul (x y : CompactOctonion R) : CompactOctonion R where
  e0 := x.e0 * y.e0 - x.e1 * y.e1 - x.e2 * y.e2 - x.e3 * y.e3 -
        x.e4 * y.e4 - x.e5 * y.e5 - x.e6 * y.e6 - x.e7 * y.e7
  e1 := x.e0 * y.e1 + x.e1 * y.e0 + x.e2 * y.e4 - x.e4 * y.e2 +
        x.e5 * y.e6 - x.e6 * y.e5 + x.e3 * y.e7 - x.e7 * y.e3
  e2 := x.e0 * y.e2 + x.e2 * y.e0 + x.e4 * y.e1 - x.e1 * y.e4 +
        x.e3 * y.e5 - x.e5 * y.e3 + x.e6 * y.e7 - x.e7 * y.e6
  e3 := x.e0 * y.e3 + x.e3 * y.e0 + x.e5 * y.e2 - x.e2 * y.e5 +
        x.e4 * y.e6 - x.e6 * y.e4 + x.e7 * y.e1 - x.e1 * y.e7
  e4 := x.e0 * y.e4 + x.e4 * y.e0 + x.e1 * y.e2 - x.e2 * y.e1 +
        x.e6 * y.e3 - x.e3 * y.e6 + x.e5 * y.e7 - x.e7 * y.e5
  e5 := x.e0 * y.e5 + x.e5 * y.e0 + x.e2 * y.e3 - x.e3 * y.e2 +
        x.e7 * y.e4 - x.e4 * y.e7 + x.e6 * y.e1 - x.e1 * y.e6
  e6 := x.e0 * y.e6 + x.e6 * y.e0 + x.e3 * y.e4 - x.e4 * y.e3 +
        x.e1 * y.e5 - x.e5 * y.e1 + x.e7 * y.e2 - x.e2 * y.e7
  e7 := x.e0 * y.e7 + x.e7 * y.e0 + x.e4 * y.e5 - x.e5 * y.e4 +
        x.e2 * y.e6 - x.e6 * y.e2 + x.e1 * y.e3 - x.e3 * y.e1

def conj (x : CompactOctonion R) : CompactOctonion R :=
  ⟨x.e0, -x.e1, -x.e2, -x.e3, -x.e4, -x.e5, -x.e6, -x.e7⟩

def trace (x : CompactOctonion R) : R := x.e0 + x.e0

def norm (x : CompactOctonion R) : R :=
  x.e0 * x.e0 + x.e1 * x.e1 + x.e2 * x.e2 + x.e3 * x.e3 +
  x.e4 * x.e4 + x.e5 * x.e5 + x.e6 * x.e6 + x.e7 * x.e7

def scalar (r : R) : CompactOctonion R := ⟨r, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem mul_zero (x : CompactOctonion R) : mul x 0 = 0 := by
  ext <;> simp [mul]

@[simp] theorem zero_mul (x : CompactOctonion R) : mul 0 x = 0 := by
  ext <;> simp [mul]

@[simp] theorem mul_one (x : CompactOctonion R) : mul x 1 = x := by
  ext <;> simp [mul]

@[simp] theorem one_mul (x : CompactOctonion R) : mul 1 x = x := by
  ext <;> simp [mul]

theorem add_mul (x y z : CompactOctonion R) : mul (x + y) z = mul x z + mul y z := by
  ext <;> simp [mul] <;> ring

theorem mul_add (x y z : CompactOctonion R) : mul x (y + z) = mul x y + mul x z := by
  ext <;> simp [mul] <;> ring

theorem smul_mul (r : R) (x y : CompactOctonion R) : mul (r • x) y = r • mul x y := by
  ext <;> simp [mul] <;> ring

theorem mul_smul (r : R) (x y : CompactOctonion R) : mul x (r • y) = r • mul x y := by
  ext <;> simp [mul] <;> ring

theorem neg_mul (x y : CompactOctonion R) : mul (-x) y = -(mul x y) := by
  ext <;> simp [mul] <;> ring

theorem mul_neg (x y : CompactOctonion R) : mul x (-y) = -(mul x y) := by
  ext <;> simp [mul] <;> ring

theorem sub_mul (x y z : CompactOctonion R) : mul (x - y) z = mul x z - mul y z := by
  rw [show x - y = x + (-y) from rfl, add_mul, neg_mul]
  rfl

theorem mul_sub (x y z : CompactOctonion R) : mul x (y - z) = mul x y - mul x z := by
  rw [show y - z = y + (-z) from rfl, mul_add, mul_neg]
  rfl

@[simp] theorem conj_zero : conj (0 : CompactOctonion R) = 0 := by
  ext <;> simp [conj]

@[simp] theorem conj_one : conj (1 : CompactOctonion R) = 1 := by
  ext <;> simp [conj]

@[simp] theorem conj_conj (x : CompactOctonion R) : conj (conj x) = x := by
  ext <;> simp [conj]

theorem conj_add (x y : CompactOctonion R) : conj (x + y) = conj x + conj y := by
  ext <;> simp [conj] <;> ring

theorem conj_neg (x : CompactOctonion R) : conj (-x) = -(conj x) := by
  ext <;> simp [conj]

theorem conj_sub (x y : CompactOctonion R) : conj (x - y) = conj x - conj y := by
  rw [show x - y = x + (-y) from rfl, conj_add, conj_neg]
  rfl

theorem conj_smul (r : R) (x : CompactOctonion R) : conj (r • x) = r • conj x := by
  ext <;> simp [conj]

theorem conj_mul (x y : CompactOctonion R) : conj (mul x y) = mul (conj y) (conj x) := by
  ext <;> simp [conj, mul] <;> ring

theorem mul_conj_self (x : CompactOctonion R) : mul x (conj x) = norm x • 1 := by
  ext <;> simp [mul, conj, norm] <;> ring

theorem conj_mul_self (x : CompactOctonion R) : mul (conj x) x = norm x • 1 := by
  ext <;> simp [mul, conj, norm] <;> ring

@[simp] theorem norm_zero : norm (0 : CompactOctonion R) = 0 := by
  simp [norm]

@[simp] theorem norm_one : norm (1 : CompactOctonion R) = 1 := by
  simp [norm]

theorem norm_conj (x : CompactOctonion R) : norm (conj x) = norm x := by
  simp [norm, conj]

theorem norm_smul (r : R) (x : CompactOctonion R) : norm (r • x) = r ^ 2 * norm x := by
  simp [norm]
  ring

theorem norm_neg (x : CompactOctonion R) : norm (-x) = norm x := by
  simp [norm]

/-- Degen's 8-square composition law: `N(x * y) = N(x) * N(y)`. -/
theorem norm_mul (x y : CompactOctonion R) : norm (mul x y) = norm x * norm y := by
  simp [norm, mul]
  ring

theorem norm_add (x y : CompactOctonion R) :
    norm (x + y) = norm x + norm y + trace (mul x (conj y)) := by
  simp [norm, trace, mul, conj]
  ring

@[simp] theorem trace_zero : trace (0 : CompactOctonion R) = 0 := by
  simp [trace]

@[simp] theorem trace_one : trace (1 : CompactOctonion R) = 2 := by
  change (1 : R) + 1 = 2
  ring

theorem trace_add (x y : CompactOctonion R) : trace (x + y) = trace x + trace y := by
  simp [trace]
  ring

theorem trace_sub (x y : CompactOctonion R) : trace (x - y) = trace x - trace y := by
  simp [trace, show x - y = x + (-y) from rfl]
  ring

theorem trace_neg (x : CompactOctonion R) : trace (-x) = -trace x := by
  simp [trace]

theorem trace_smul (r : R) (x : CompactOctonion R) : trace (r • x) = r * trace x := by
  simp [trace]
  ring

@[simp] theorem trace_conj (x : CompactOctonion R) : trace (conj x) = trace x := by
  simp [trace, conj]

theorem trace_mul_comm (x y : CompactOctonion R) : trace (mul x y) = trace (mul y x) := by
  simp [trace, mul]
  ring

theorem trace_mul_conj_comm (x y : CompactOctonion R) :
    trace (mul x (conj y)) = trace (mul y (conj x)) := by
  simp [trace, mul, conj]
  ring

theorem trace_mul_assoc (x y z : CompactOctonion R) :
    trace (mul (mul x y) z) = trace (mul x (mul y z)) := by
  simp [trace, mul]
  ring

theorem trace_mul_cyclic (x y z : CompactOctonion R) :
    trace (mul (mul x y) z) = trace (mul (mul y z) x) := by
  simp [trace, mul]
  ring

theorem mul_self_sub_trace_add_norm (x : CompactOctonion R) :
    mul x x - trace x • x + norm x • (1 : CompactOctonion R) = 0 := by
  change add (sub (mul x x) (smul (trace x) x)) (smul (norm x) one) = zero
  ext <;> simp [mul, trace, norm, sub, add, neg, smul, one, zero] <;> ring

theorem add_conj_eq_trace (x : CompactOctonion R) :
    x + conj x = trace x • (1 : CompactOctonion R) := by
  change add x (conj x) = smul (trace x) one
  ext <;> simp [conj, trace, add, smul, one]

theorem mul_add_conj_mul_eq_trace (x y : CompactOctonion R) :
    mul x y + mul (conj y) (conj x) = trace (mul x y) • (1 : CompactOctonion R) := by
  rw [← conj_mul, add_conj_eq_trace]

theorem left_alternative (x y : CompactOctonion R) :
    mul (mul x x) y = mul x (mul x y) := by
  ext <;> dsimp only [mul] <;> ring

theorem right_alternative (x y : CompactOctonion R) :
    mul (mul x y) y = mul x (mul y y) := by
  ext <;> dsimp only [mul] <;> ring

theorem flexible (x y : CompactOctonion R) :
    mul (mul x y) x = mul x (mul y x) := by
  ext <;> dsimp only [mul] <;> ring

theorem moufang_middle (x y z : CompactOctonion R) :
    mul (mul z x) (mul y z) = mul z (mul (mul x y) z) := by
  ext <;> dsimp only [mul] <;> ring

theorem moufang_left (x y z : CompactOctonion R) :
    mul (mul z (mul x z)) y = mul z (mul x (mul z y)) := by
  ext <;> dsimp only [mul] <;> ring

theorem moufang_right (x y z : CompactOctonion R) :
    mul x (mul (mul z y) z) = mul (mul (mul x z) y) z := by
  ext <;> dsimp only [mul] <;> ring

theorem mul_conj_add_conj_mul (x y : CompactOctonion R) :
    mul x (conj y) + mul y (conj x) = trace (mul x (conj y)) • (1 : CompactOctonion R) := by
  change add (mul x (conj y)) (mul y (conj x)) = smul (trace (mul x (conj y))) one
  ext <;> dsimp only [mul, conj, trace, add, smul, one] <;> ring

/-- Key McCrimmon diagonal identity inside `CompactOctonion R` (mirrors `ZornVectorMatrix.adjoint_diagonal_composition`). -/
theorem adjoint_diagonal_composition (a1 a2 a3 : R) (a b c : CompactOctonion R) :
    (a1 * a3 - norm c) * (a1 * a2 - norm a) -
        norm (mul (conj a) (conj c) - a1 • b) =
      (a1 * a2 * a3 - a1 * norm b - a2 * norm c - a3 * norm a +
        trace (mul (mul a b) c)) * a1 := by
  have hn : norm (mul (conj a) (conj c) - a1 • b) =
      norm a * norm c + a1 ^ 2 * norm b - a1 * trace (mul (mul a b) c) := by
    rw [show mul (conj a) (conj c) - a1 • b = mul (conj a) (conj c) + (-a1) • b by module,
      norm_add, norm_mul, norm_conj, norm_conj, norm_smul, conj_smul,
      mul_smul, trace_smul]
    have htr : trace (mul (mul (conj a) (conj c)) (conj b)) = trace (mul (mul a b) c) := by
      rw [← conj_mul c a, ← conj_mul b (mul c a), trace_conj, trace_mul_comm, trace_mul_assoc]
      exact trace_mul_comm c (mul a b)
    rw [htr]
    ring
  rw [hn]
  ring

private theorem mul_mul_conj_right (x y : CompactOctonion R) :
    mul (mul x y) (conj y) = norm y • x := by
  have hy : conj y = trace y • (1 : CompactOctonion R) - y := eq_sub_of_add_eq' (add_conj_eq_trace y)
  rw [hy, mul_sub, mul_smul, mul_one, right_alternative]
  have hy2 : mul y y = trace y • y - norm y • (1 : CompactOctonion R) := by
    have h := mul_self_sub_trace_add_norm y
    calc mul y y = mul y y - (mul y y - trace y • y + norm y • (1 : CompactOctonion R)) := by rw [h, sub_zero]
      _ = trace y • y - norm y • (1 : CompactOctonion R) := by abel
  rw [hy2, mul_sub, mul_smul, mul_smul, mul_one]
  module

private theorem conj_mul_mul_left (x y : CompactOctonion R) :
    mul (conj x) (mul x y) = norm x • y := by
  have hx : conj x = trace x • (1 : CompactOctonion R) - x := eq_sub_of_add_eq' (add_conj_eq_trace x)
  rw [hx, sub_mul, smul_mul, one_mul, ← left_alternative]
  have hx2 : mul x x = trace x • x - norm x • (1 : CompactOctonion R) := by
    have h := mul_self_sub_trace_add_norm x
    calc mul x x = mul x x - (mul x x - trace x • x + norm x • (1 : CompactOctonion R)) := by rw [h, sub_zero]
      _ = trace x • x - norm x • (1 : CompactOctonion R) := by abel
  rw [hx2, sub_mul, smul_mul, smul_mul, one_mul]
  module

private theorem mul_ab_mul_ca (a b c : CompactOctonion R) :
    mul (mul a b) (mul c a) + norm a • mul (conj c) (conj b) =
      trace (mul (mul a b) c) • a := by
  change add (mul (mul a b) (mul c a)) (smul (norm a) (mul (conj c) (conj b))) =
    smul (trace (mul (mul a b) c)) a
  ext <;> dsimp only [mul, conj, norm, trace, add, smul] <;> ring

/-- Key McCrimmon component identity inside `CompactOctonion R` (mirrors `ZornVectorMatrix.adjoint_component_composition`). -/
theorem adjoint_component_composition (a1 a2 a3 : R) (a b c : CompactOctonion R) :
    mul (mul a b - a2 • conj c) (mul c a - a1 • conj b) -
        (a1 * a2 - norm a) • (mul (conj c) (conj b) - a3 • a) =
      (a1 * a2 * a3 - a1 * norm b - a2 * norm c - a3 * norm a +
        trace (mul (mul a b) c)) • a := by
  rw [sub_mul, mul_sub, mul_sub, smul_mul, mul_smul, mul_smul, smul_mul,
    smul_smul, mul_mul_conj_right a b, conj_mul_mul_left c a, smul_smul, smul_smul,
    smul_sub]
  have hcb := mul_ab_mul_ca a b c
  have hcb' : mul (mul a b) (mul c a) =
      trace (mul (mul a b) c) • a - norm a • mul (conj c) (conj b) :=
    eq_sub_of_add_eq hcb
  rw [hcb']
  module

end CommRingLaws

section RealLaws

/-- Standard orthonormal coordinate basis vector `i : Fin 8` in `CompactOctonion ℝ`. -/
def basisVec (i : Fin 8) : CompactOctonion ℝ :=
  match i with
  | 0 => ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
  | 4 => ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
  | 5 => ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
  | 6 => ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
  | 7 => ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

def coordFun (x : CompactOctonion ℝ) : Fin 8 → ℝ :=
  fun i => match i with
  | 0 => x.e0 | 1 => x.e1 | 2 => x.e2 | 3 => x.e3
  | 4 => x.e4 | 5 => x.e5 | 6 => x.e6 | 7 => x.e7

def mkOfFun (f : Fin 8 → ℝ) : CompactOctonion ℝ :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

noncomputable def coordEquiv : CompactOctonion ℝ ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := coordFun
  invFun := mkOfFun
  left_inv x := by ext <;> rfl
  right_inv f := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

noncomputable def compactOctonionBasis : Module.Basis (Fin 8) ℝ (CompactOctonion ℝ) :=
  Module.Basis.ofEquivFun coordEquiv

theorem compactOctonionBasis_apply (i : Fin 8) : compactOctonionBasis i = basisVec i := by
  fin_cases i <;> ext <;> simp [compactOctonionBasis, coordEquiv, mkOfFun, basisVec]

theorem finrank_compactOctonion : Module.finrank ℝ (CompactOctonion ℝ) = 8 := by
  rw [Module.finrank_eq_card_basis compactOctonionBasis]
  simp

theorem basisVec_decomposition (x : CompactOctonion ℝ) :
    ∑ i : Fin 8, coordFun x i • basisVec i = x := by
  rw [Fin.sum_univ_eight]
  ext <;> simp [coordFun, basisVec]

theorem norm_nonneg (x : CompactOctonion ℝ) : 0 ≤ norm x := by
  simp only [norm]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _))
    (mul_self_nonneg _)) (mul_self_nonneg _)) (mul_self_nonneg _))
    (mul_self_nonneg _)) (mul_self_nonneg _)

theorem norm_eq_zero_iff (x : CompactOctonion ℝ) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    simp only [norm] at h
    have hn : ∀ a : ℝ, 0 ≤ a * a := mul_self_nonneg
    have h4 : ∀ a b c d : ℝ, a * a + b * b + c * c + d * d = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
      intro a b c d habcd
      have h2 := (add_eq_zero_iff_of_nonneg
        (add_nonneg (add_nonneg (hn a) (hn b)) (hn c)) (hn d)).mp habcd
      have h1 := (add_eq_zero_iff_of_nonneg (add_nonneg (hn a) (hn b)) (hn c)).mp h2.1
      have h0 := (add_eq_zero_iff_of_nonneg (hn a) (hn b)).mp h1.1
      exact ⟨mul_self_eq_zero.mp h0.1, mul_self_eq_zero.mp h0.2,
        mul_self_eq_zero.mp h1.2, mul_self_eq_zero.mp h2.2⟩
    have hsplit := (add_eq_zero_iff_of_nonneg
      (add_nonneg (add_nonneg (hn x.e0) (hn x.e1)) (add_nonneg (hn x.e2) (hn x.e3)))
      (add_nonneg (add_nonneg (hn x.e4) (hn x.e5)) (add_nonneg (hn x.e6) (hn x.e7)))).mp
      (by linarith)
    obtain ⟨e0z, e1z, e2z, e3z⟩ := h4 x.e0 x.e1 x.e2 x.e3 (by linarith [hsplit.1])
    obtain ⟨e4z, e5z, e6z, e7z⟩ := h4 x.e4 x.e5 x.e6 x.e7 (by linarith [hsplit.2])
    ext <;> simp [e0z, e1z, e2z, e3z, e4z, e5z, e6z, e7z]
  · rintro rfl
    exact norm_zero

theorem mul_eq_zero_iff (x y : CompactOctonion ℝ) : mul x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    have hn : norm x * norm y = 0 := by
      rw [← norm_mul, h, norm_zero]
    rcases mul_eq_zero.mp hn with hx | hy
    · exact Or.inl ((norm_eq_zero_iff x).mp hx)
    · exact Or.inr ((norm_eq_zero_iff y).mp hy)
  · rintro (rfl | rfl)
    · exact zero_mul _
    · exact mul_zero _

/-- Multiplicative inverse `(N(x))⁻¹ • conj x` in the real division octonions. -/
noncomputable def inv (x : CompactOctonion ℝ) : CompactOctonion ℝ :=
  (norm x)⁻¹ • conj x

theorem mul_inv_cancel {x : CompactOctonion ℝ} (hx : x ≠ 0) : mul x (inv x) = 1 := by
  have hn : norm x ≠ 0 := mt (norm_eq_zero_iff x).mp hx
  rw [inv, mul_smul, mul_conj_self, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem inv_mul_cancel {x : CompactOctonion ℝ} (hx : x ≠ 0) : mul (inv x) x = 1 := by
  have hn : norm x ≠ 0 := mt (norm_eq_zero_iff x).mp hx
  rw [inv, smul_mul, conj_mul_self, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Trace pairing `trace (x * conj y)` is positive-definite on `CompactOctonion ℝ`. -/
def bilin (x y : CompactOctonion ℝ) : ℝ := trace (mul x (conj y))

theorem bilin_eq (x y : CompactOctonion ℝ) :
    bilin x y = 2 * (x.e0 * y.e0 + x.e1 * y.e1 + x.e2 * y.e2 + x.e3 * y.e3 +
      x.e4 * y.e4 + x.e5 * y.e5 + x.e6 * y.e6 + x.e7 * y.e7) := by
  simp [bilin, trace, mul, conj]
  ring

theorem bilin_self (x : CompactOctonion ℝ) : bilin x x = 2 * norm x := by
  simp [bilin_eq, norm]

theorem bilin_basis (i j : Fin 8) :
    bilin (basisVec i) (basisVec j) = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [bilin_eq, basisVec]

theorem eq_zero_of_bilin_basis (x : CompactOctonion ℝ)
    (h : ∀ i : Fin 8, bilin x (basisVec i) = 0) : x = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [bilin_eq, basisVec] at h0 h1 h2 h3 h4 h5 h6 h7
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7
  ext <;> simp <;> linarith

/-- Every pure-imaginary octonion in the left nucleus of `CompactOctonion ℝ` is zero. -/
theorem pureImaginary_left_nucleus_eq_zero (a : CompactOctonion ℝ)
    (htr : trace a = 0)
    (hnuc : ∀ x y : CompactOctonion ℝ, mul (mul a x) y = mul a (mul x y)) : a = 0 := by
  have h0 : a.e0 = 0 := by
    simp only [trace] at htr
    linarith
  have h12 := congrArg CompactOctonion.e6 (hnuc (basisVec 1) (basisVec 2))
  have h23 := congrArg CompactOctonion.e7 (hnuc (basisVec 2) (basisVec 3))
  have h34 := congrArg CompactOctonion.e1 (hnuc (basisVec 3) (basisVec 4))
  have h45 := congrArg CompactOctonion.e2 (hnuc (basisVec 4) (basisVec 5))
  have h56 := congrArg CompactOctonion.e3 (hnuc (basisVec 5) (basisVec 6))
  have h67 := congrArg CompactOctonion.e4 (hnuc (basisVec 6) (basisVec 7))
  have h71 := congrArg CompactOctonion.e5 (hnuc (basisVec 7) (basisVec 1))
  simp only [mul, basisVec] at h12 h23 h34 h45 h56 h67 h71
  ring_nf at h12 h23 h34 h45 h56 h67 h71
  have ha1 : a.e1 = 0 := by linarith
  have ha2 : a.e2 = 0 := by linarith
  have ha3 : a.e3 = 0 := by linarith
  have ha4 : a.e4 = 0 := by linarith
  have ha5 : a.e5 = 0 := by linarith
  have ha6 : a.e6 = 0 := by linarith
  have ha7 : a.e7 = 0 := by linarith
  ext <;> assumption

end RealLaws

end CompactOctonion

end InfoGeometry.Algebra
