import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
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

end InfoGeometry.Algebraic
