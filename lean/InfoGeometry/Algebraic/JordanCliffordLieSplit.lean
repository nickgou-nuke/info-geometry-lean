/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry/Algebraic/JordanCliffordLieSplit.lean

Jordan-Lie split of associative kinematics (Theorem 1.1).
Establishing the decomposition: ab = (a ∘ b) + [a, b]_Lie.
-/

noncomputable section

namespace InfoGeometry.Algebraic

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- 
The symmetric Jordan product (metric readout) derived from an associative algebra. 
Mapped to the L2 Operator layer.
-/
@[rep_depth operator]
def jordanProduct (a b : A) : A :=
  (1/2 : ℝ) • (a * b + b * a)

/-- 
The antisymmetric Lie bracket (dynamical generator) derived from an associative algebra.
Mapped to the L2 Operator layer.
-/
@[rep_depth operator]
def lieBracket (a b : A) : A :=
  (1/2 : ℝ) • (a * b - b * a)

/-- 
Theorem 1.1: Jordan-Lie Split of Associative Kinematics.
The associative product admits a canonical decomposition into Jordan and Lie components.
-/
@[rep_depth operator]
theorem jordan_lie_split (a b : A) :
    a * b = jordanProduct a b + lieBracket a b := by
  unfold jordanProduct lieBracket
  simp [smul_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  rw [← add_smul]
  norm_num

/-- The affine Jordan--Lie interpolation obtained by weighting both product
orders with complementary scalar coefficients. -/
def weightedProduct (q : ℝ) (a b : A) : A :=
  ((1 + q) / 2 : ℝ) • (a * b) + ((1 - q) / 2 : ℝ) • (b * a)

/-- The weighted product is the Jordan product plus `q` times the Lie part. -/
theorem weightedProduct_eq_jordan_add_lie (q : ℝ) (a b : A) :
    weightedProduct q a b = jordanProduct a b + q • lieBracket a b := by
  unfold weightedProduct jordanProduct lieBracket
  module


theorem jordanProduct_comm (a b : A) :
    jordanProduct a b = jordanProduct b a := by
  unfold jordanProduct
  rw [add_comm]


theorem jordanProduct_self (a : A) :
    jordanProduct a a = a * a := by
  unfold jordanProduct
  module


theorem lieBracket_anti (a b : A) :
    lieBracket b a = -lieBracket a b := by
  unfold lieBracket
  rw [← smul_neg]
  simp [sub_eq_add_neg, add_comm]


theorem lieBracket_self (a : A) :
    lieBracket a a = 0 := by
  unfold lieBracket
  simp

end InfoGeometry.Algebraic
