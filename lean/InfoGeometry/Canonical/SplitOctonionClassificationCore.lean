import Mathlib.Algebra.Ring.Associator
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornSpinor

/-!
# Split-octonion classification core

This file works on the explicit Zorn carrier and proves the two witness
existence statements in a coordinate form.

It stays away from any associative `[Ring]` hypothesis.  The carrier is the
nonassociative `InfoGeometry.Canonical.ZornMatrix`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionClassificationCore

open scoped BigOperators

namespace ZornMatrix

variable {R : Type*} [CommRing R]

/-- Explicit Zorn multiplication copied from the concrete carrier. -/
def mulZ (z1 z2 : InfoGeometry.Canonical.ZornMatrix R) :
    InfoGeometry.Canonical.ZornMatrix R :=
  { a := z1.a * z2.a + ZornMatrix.dot z1.x z2.y
    b := z1.b * z2.b + ZornMatrix.dot z1.y z2.x
    x := z1.a • z2.x + z2.b • z1.x - ZornMatrix.cross z1.y z2.y
    y := z1.b • z2.y + z2.a • z1.y + ZornMatrix.cross z1.x z2.x }

/-- The coordinate commutator `[x,y] = xy - yx`. -/
def commutator (x y : InfoGeometry.Canonical.ZornMatrix R) :
    InfoGeometry.Canonical.ZornMatrix R :=
  mulZ x y - mulZ y x

/-- The coordinate associator `(x,y,z) = (xy)z - x(yz)`. -/
def associator (x y z : InfoGeometry.Canonical.ZornMatrix R) :
    InfoGeometry.Canonical.ZornMatrix R :=
  mulZ (mulZ x y) z - mulZ x (mulZ y z)

/-- Scalar elements are scalar multiples of `1`. -/
def IsScalar (x : InfoGeometry.Canonical.ZornMatrix R) : Prop :=
  ∃ r : R, x = r • (1 : InfoGeometry.Canonical.ZornMatrix R)

/-- The three standard basis vectors of `Fin 3 → R`. -/
def e0 : Fin 3 → R := ![1, 0, 0]
def e1 : Fin 3 → R := ![0, 1, 0]
def e2 : Fin 3 → R := ![0, 0, 1]

/-- A coordinate basis vector selector. -/
def basisVec : Fin 3 → Fin 3 → R
  | 0 => e0
  | 1 => e1
  | 2 => e2

/-- Diagonal scalar sector. -/
def diag (a b : R) : InfoGeometry.Canonical.ZornMatrix R :=
  { a := a, b := b, x := 0, y := 0 }

/-- Upper nilpotent sector. -/
def upper (u : Fin 3 → R) : InfoGeometry.Canonical.ZornMatrix R :=
  { a := 0, b := 0, x := u, y := 0 }

/-- Lower nilpotent sector. -/
def lower (u : Fin 3 → R) : InfoGeometry.Canonical.ZornMatrix R :=
  { a := 0, b := 0, x := 0, y := u }

@[simp] theorem a_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).a = x.a - y.a := by
  rfl

@[simp] theorem b_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).b = x.b - y.b := by
  rfl

@[simp] theorem x_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).x = x.x - y.x := by
  rfl

@[simp] theorem y_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).y = x.y - y.y := by
  rfl

@[simp] theorem vecHead_eq (v : Fin 3 → R) : Matrix.vecHead v = v 0 := by
  rfl

@[simp] theorem vecHead_tail_eq (v : Fin 3 → R) :
    Matrix.vecHead (Matrix.vecTail v) = v 1 := by
  rfl

@[simp] theorem vecHead_tail_tail_eq (v : Fin 3 → R) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) = v 2 := by
  rfl

@[simp] theorem zero_a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by
  rfl

@[simp] theorem zero_b : (0 : InfoGeometry.Canonical.ZornMatrix R).b = 0 := by
  rfl

@[simp] theorem zero_x : (0 : InfoGeometry.Canonical.ZornMatrix R).x = 0 := by
  rfl

@[simp] theorem zero_y : (0 : InfoGeometry.Canonical.ZornMatrix R).y = 0 := by
  rfl

@[simp] theorem dot_e0 (v : Fin 3 → R) :
    ZornMatrix.dot e0 v = v 0 := by
  simp [ZornMatrix.dot, e0]

@[simp] theorem dot_e1 (v : Fin 3 → R) :
    ZornMatrix.dot e1 v = v 1 := by
  simp [ZornMatrix.dot, e1]

@[simp] theorem dot_e2 (v : Fin 3 → R) :
    ZornMatrix.dot e2 v = v 2 := by
  simp [ZornMatrix.dot, e2]

@[simp] theorem dot_v_e0 (v : Fin 3 → R) :
    ZornMatrix.dot v e0 = v 0 := by
  simp [ZornMatrix.dot, e0]

@[simp] theorem dot_v_e1 (v : Fin 3 → R) :
    ZornMatrix.dot v e1 = v 1 := by
  simp [ZornMatrix.dot, e1]

@[simp] theorem dot_v_e2 (v : Fin 3 → R) :
    ZornMatrix.dot v e2 = v 2 := by
  simp [ZornMatrix.dot, e2]

@[simp] theorem cross_e0 (v : Fin 3 → R) :
    ZornMatrix.cross e0 v = ![0, -v 2, v 1] := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross, e0]

@[simp] theorem cross_e1 (v : Fin 3 → R) :
    ZornMatrix.cross e1 v = ![v 2, 0, -v 0] := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross, e1]

@[simp] theorem cross_e2 (v : Fin 3 → R) :
    ZornMatrix.cross e2 v = ![-v 1, v 0, 0] := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross, e2]

@[simp] theorem cross_v_e0 (v : Fin 3 → R) :
    ZornMatrix.cross v e0 = ![0, v 2, -v 1] := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross, e0]

@[simp] theorem cross_v_e1 (v : Fin 3 → R) :
    ZornMatrix.cross v e1 = ![-v 2, 0, v 0] := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross, e1]

@[simp] theorem cross_v_e2 (v : Fin 3 → R) :
    ZornMatrix.cross v e2 = ![v 1, -v 0, 0] := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross, e2]

theorem dot_smul_left (a : R) (u v : Fin 3 → R) :
    ZornMatrix.dot (a • u) v = a * ZornMatrix.dot u v := by
  simp [ZornMatrix.dot]
  ring

theorem dot_smul_right (a : R) (u v : Fin 3 → R) :
    ZornMatrix.dot u (a • v) = a * ZornMatrix.dot u v := by
  simp [ZornMatrix.dot]
  ring

theorem cross_smul_left (a : R) (u v : Fin 3 → R) :
    ZornMatrix.cross (a • u) v = a • ZornMatrix.cross u v := by
  ext i <;> fin_cases i <;>
    simp [ZornMatrix.cross] <;> ring

theorem cross_smul_right (a : R) (u v : Fin 3 → R) :
    ZornMatrix.cross u (a • v) = a • ZornMatrix.cross u v := by
  ext i <;> fin_cases i <;>
    simp [ZornMatrix.cross] <;> ring

theorem cross_skew (u v : Fin 3 → R) :
    ZornMatrix.cross u v = - ZornMatrix.cross v u := by
  ext i <;> fin_cases i <;> simp [ZornMatrix.cross] <;> ring

theorem commutator_upper_e0_x0 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (upper e0)).x 0 - (mulZ (upper e0) x).x 0 = x.a - x.b := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, upper, e0, ZornMatrix.dot, ZornMatrix.cross]

theorem commutator_upper_e1_x2 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (upper e1)).y 2 - (mulZ (upper e1) x).y 2 = (2 : R) * x.x 0 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, upper, e1, ZornMatrix.dot, ZornMatrix.cross]
  ring_nf

theorem commutator_upper_e2_x0 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (upper e2)).y 0 - (mulZ (upper e2) x).y 0 = (2 : R) * x.x 1 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, upper, e2, ZornMatrix.dot, ZornMatrix.cross]
  ring_nf

theorem commutator_upper_e0_x1 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (upper e0)).y 1 - (mulZ (upper e0) x).y 1 = (2 : R) * x.x 2 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, upper, e0, ZornMatrix.dot, ZornMatrix.cross]
  ring_nf

theorem commutator_lower_e0_a (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (lower e0)).a - (mulZ (lower e0) x).a = x.x 0 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, lower, e0, ZornMatrix.dot, ZornMatrix.cross]

theorem commutator_lower_e1_a (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (lower e1)).a - (mulZ (lower e1) x).a = x.x 1 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, lower, e1, ZornMatrix.dot, ZornMatrix.cross]

theorem commutator_lower_e2_a (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (lower e2)).a - (mulZ (lower e2) x).a = x.x 2 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, lower, e2, ZornMatrix.dot, ZornMatrix.cross]

theorem commutator_lower_e0_x1 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (lower e0)).x 1 - (mulZ (lower e0) x).x 1 = - (2 : R) * x.y 2 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, lower, e0, ZornMatrix.dot, ZornMatrix.cross]
  ring_nf

theorem commutator_lower_e0_x2 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (lower e0)).x 2 - (mulZ (lower e0) x).x 2 = (2 : R) * x.y 1 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, lower, e0, ZornMatrix.dot, ZornMatrix.cross]
  ring_nf

theorem commutator_lower_e1_x2 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (mulZ x (lower e1)).x 2 - (mulZ (lower e1) x).x 2 = - (2 : R) * x.y 0 := by
  rcases x with ⟨a, b, x, y⟩
  simp [mulZ, lower, e1, ZornMatrix.dot, ZornMatrix.cross]
  ring_nf

theorem associator_upper_e0_lower_e0_y (x : InfoGeometry.Canonical.ZornMatrix R) :
    (associator x (upper e0) (lower e0)).y = ![0, -x.y 1, -x.y 2] := by
  rcases x with ⟨a, b, x, y⟩
  ext i <;> fin_cases i <;> simp [associator, mulZ, upper, lower, e0, ZornMatrix.dot, ZornMatrix.cross]

theorem associator_upper_e1_lower_e1_y (x : InfoGeometry.Canonical.ZornMatrix R) :
    (associator x (upper e1) (lower e1)).y = ![-x.y 0, 0, -x.y 2] := by
  rcases x with ⟨a, b, x, y⟩
  ext i <;> fin_cases i <;> simp [associator, mulZ, upper, lower, e1, ZornMatrix.dot, ZornMatrix.cross]

theorem associator_upper_e2_lower_e2_y (x : InfoGeometry.Canonical.ZornMatrix R) :
    (associator x (upper e2) (lower e2)).y = ![-x.y 0, -x.y 1, 0] := by
  rcases x with ⟨a, b, x, y⟩
  ext i <;> fin_cases i <;> simp [associator, mulZ, upper, lower, e2, ZornMatrix.dot, ZornMatrix.cross]

theorem nonzero_associator_of_y_ne_zero
    (x : InfoGeometry.Canonical.ZornMatrix R)
    (hy : x.y ≠ 0) :
    ∃ y z : InfoGeometry.Canonical.ZornMatrix R, associator x y z ≠ 0 := by
  by_cases h0 : x.y 0 ≠ 0
  · refine ⟨upper e1, lower e1, ?_⟩
    intro h
    have h' := congrArg ZornMatrix.y h
    rw [associator_upper_e1_lower_e1_y] at h'
    simp at h'
    exact h0 h'.1
  · by_cases h1 : x.y 1 ≠ 0
    · refine ⟨upper e2, lower e2, ?_⟩
      intro h
      have h' := congrArg ZornMatrix.y h
      rw [associator_upper_e2_lower_e2_y] at h'
      simp at h'
      exact h1 h'.2
    · push_neg at h0 h1
      have h2 : x.y 2 ≠ 0 := by
        intro h2
        apply hy
        ext i <;> fin_cases i <;> simp [h0, h1, h2]
      refine ⟨upper e0, lower e0, ?_⟩
      intro h
      have h' := congrArg ZornMatrix.y h
      rw [associator_upper_e0_lower_e0_y] at h'
      simp at h'
      exact h2 h'.2

end ZornMatrix

end InfoGeometry.Canonical.SplitOctonionClassificationCore
