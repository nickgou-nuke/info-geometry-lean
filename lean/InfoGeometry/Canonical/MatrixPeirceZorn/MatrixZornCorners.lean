/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixZorn
import Mathlib.LinearAlgebra.Prod

/-!
# Exact even-channel range of the matrix-valued triple associator

The ordered contraction/cross identity preserves the order of all three matrix
factors. It implies that same-channel triple associators have opposite even
corners. Conversely, every such pair of arbitrary operator corners occurs.
Thus the exact image is the anti-diagonal even submodule, not all even corners.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn

variable {n : Type*}

/-- The linear embedding of an operator as two opposite even corners. -/
def antiDiagonalEvenMap : Op n →ₗ[ℂ] Carrier n where
  toFun A := corner (-A) A
  map_add' A B := by simp [corner, add_comm]
  map_smul' c A := by simp [corner]

@[simp] theorem antiDiagonalEvenMap_apply (A : Op n) :
    antiDiagonalEvenMap A = corner (-A) A := rfl

/-- The native submodule consisting of opposite even operator corners. -/
def antiDiagonalEven : Submodule ℂ (Carrier n) := LinearMap.range antiDiagonalEvenMap

@[simp] theorem mem_antiDiagonalEven (X : Carrier n) :
    X ∈ antiDiagonalEven ↔ ∃ A : Op n, corner (-A) A = X := Iff.rfl

theorem antiDiagonalEvenMap_injective :
    Function.Injective (antiDiagonalEvenMap (n := n)) := by
  intro A B h
  exact congrArg (fun X : Carrier n => X.2.2.2) h

variable [Fintype n] [DecidableEq n]

/-- Ordered contraction reassociation needs associativity, never coefficient commutativity. -/
theorem dot_cross_reassociate (u v w : Vec n) :
    dot (cross u v) w = dot u (cross v w) := by
  simp [dot_eq, cross]
  noncomm_ring

theorem upper_triple_associator_antiDiagonal (u v w : Vec n) :
    associator (upper u) (upper v) (upper w) =
      corner (-(dot u (cross v w))) (dot u (cross v w)) := by
  rw [associator_upper_upper_upper, dot_cross_reassociate]

theorem lower_triple_associator_antiDiagonal (u v w : Vec n) :
    associator (lower u) (lower v) (lower w) =
      corner (-(dot u (cross v w))) (dot u (cross v w)) := by
  rw [associator_lower_lower_lower, dot_cross_reassociate]

theorem upper_triple_associator_mem (u v w : Vec n) :
    associator (upper u) (upper v) (upper w) ∈ antiDiagonalEven := by
  exact ⟨dot u (cross v w), (upper_triple_associator_antiDiagonal u v w).symm⟩

theorem lower_triple_associator_mem (u v w : Vec n) :
    associator (lower u) (lower v) (lower w) ∈ antiDiagonalEven := by
  exact ⟨dot u (cross v w), (lower_triple_associator_antiDiagonal u v w).symm⟩

theorem same_channel_triple_associators_eq (u v w : Vec n) :
    associator (upper u) (upper v) (upper w) =
      associator (lower u) (lower v) (lower w) := by
  rw [upper_triple_associator_antiDiagonal, lower_triple_associator_antiDiagonal]

/-- The coefficient of the exact upper-channel Jacobiator. -/
def upperJacobiCoefficient (u v w : Vec n) : Op n :=
  dot (cross u v - cross v u) w + dot (cross v w - cross w v) u +
    dot (cross w u - cross u w) v

omit [DecidableEq n] in
private theorem dot_sub_left (u v w : Vec n) :
    dot (u - v) w = dot u w - dot v w := by
  simp [dot]

omit [DecidableEq n] in
private theorem dot_sub_right (u v w : Vec n) :
    dot u (v - w) = dot u v - dot u w := by
  simp [dot]

private theorem cyclic_cross_difference (u v w : Vec n) :
    dot w (cross u v - cross v u) + dot u (cross v w - cross w v) +
      dot v (cross w u - cross u w) = upperJacobiCoefficient u v w := by
  simp only [upperJacobiCoefficient, dot_sub_left, dot_sub_right, dot_cross_reassociate]
  abel

/-- The upper-channel Jacobiator also has exactly opposite even corners. -/
theorem upper_jacobiator_antiDiagonal (u v w : Vec n) :
    jacobiator (upper u) (upper v) (upper w) =
      corner (-(upperJacobiCoefficient u v w)) (upperJacobiCoefficient u v w) := by
  rw [jacobiator_upper_upper_upper]
  congr 1
  calc
    _ = -(dot w (cross u v - cross v u) + dot u (cross v w - cross w v) +
      dot v (cross w u - cross u w)) := by abel
    _ = _ := congrArg Neg.neg (cyclic_cross_difference u v w)

theorem upper_jacobiator_mem (u v w : Vec n) :
    jacobiator (upper u) (upper v) (upper w) ∈ antiDiagonalEven := by
  exact ⟨upperJacobiCoefficient u v w, (upper_jacobiator_antiDiagonal u v w).symm⟩

/-- Every opposite pair of even operator corners is attained by one triple associator. -/
theorem upper_triple_associator_realizes (A : Op n) :
    associator (upper ![A, 0, 0]) (upper ![0, 1, 0]) (upper ![0, 0, 1]) =
      corner (-A) A := by
  rw [upper_triple_associator_antiDiagonal]
  simp [dot_eq, cross]

/-- The image is precisely the anti-diagonal even submodule, with no span closure needed. -/
theorem range_upper_triple_associator :
    Set.range (fun t : Vec n × Vec n × Vec n =>
      associator (upper t.1) (upper t.2.1) (upper t.2.2)) =
        (↑(antiDiagonalEven (n := n)) : Set (Carrier n)) := by
  ext X
  constructor
  · rintro ⟨⟨u, v, w⟩, rfl⟩
    exact upper_triple_associator_mem u v w
  · rintro ⟨A, rfl⟩
    exact ⟨(![A, 0, 0], ![0, 1, 0], ![0, 0, 1]), upper_triple_associator_realizes A⟩

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn
