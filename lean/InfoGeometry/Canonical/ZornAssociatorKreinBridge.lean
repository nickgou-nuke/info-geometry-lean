import Mathlib.Tactic

import InfoGeometry.Algebra.SplitOctonionZornAlgebra

/-!
# Zorn upper-sector associator and the Peirce/Krein grading

This module proves the exact associator identity on the repository-owned
split-octonion Zorn carrier.

For an upper chiral vector
  U(u) = (0,u;0,0),
the product of two upper vectors lands in the lower vector sector:
  U(u) U(v) = L(u × v).

For three upper vectors, the two bracketings land on opposite primitive
Peirce idempotents. Their difference is
  [U(u₁),U(u₂),U(u₃)] = -det(u₁,u₂,u₃) J,
where
  J = E₁ - E₂.

This is an exact algebraic theorem.  It does not by itself identify a gauge
group, prove a global G₂ stabilizer classification, or identify the Peirce
grading with a physical causal operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornAssociatorKreinBridge

open InfoGeometry.Algebra.SplitOctonionZorn

abbrev Vec3 := Vector3
abbrev Zorn := SplitOctonion

/-- Scalar triple product / oriented three-volume. -/
def tripleDet (u v w : Vec3) : ℝ :=
  Vector3.dot u (Vector3.cross v w)

/-- Upper chiral Zorn vector `(0,u;0,0)`. -/
def upper (u : Vec3) : Zorn :=
  ⟨0, u, 0, 0⟩

/-- Lower chiral Zorn vector `(0,0;v,0)`. -/
def lower (v : Vec3) : Zorn :=
  ⟨0, 0, v, 0⟩

/-- Peirce/Krein grading element `J = E₁ - E₂`. -/
def kreinJ : Zorn :=
  SplitOctonion.idempotentE1 - SplitOctonion.idempotentE2

/-- The native split-octonion associator. -/
def associator (X Y Z : Zorn) : Zorn :=
  (X * Y) * Z - X * (Y * Z)

@[simp] theorem kreinJ_coordinates :
    kreinJ = ⟨1, 0, 0, -1⟩ := by
  ext <;> rfl

/-- The two primitive idempotents resolve the algebraic unit. -/
theorem peirce_idempotents_sum :
    SplitOctonion.idempotentE1 + SplitOctonion.idempotentE2 =
      (1 : Zorn) := by
  ext <;> rfl

/-- The Peirce grading is the difference of the two primitive idempotents. -/
theorem peirce_idempotents_difference :
    SplitOctonion.idempotentE1 - SplitOctonion.idempotentE2 =
      kreinJ := rfl

/-- Multiplying two upper chiral vectors produces the lower cross-product sector. -/
theorem upper_mul_upper (u v : Vec3) :
    upper u * upper v = lower (Vector3.cross u v) := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  ext <;> simp [upper, lower, SplitOctonion.mul,
    Vector3.dot, Vector3.cross, Vector3.zero, Vector3.add,
    Vector3.sub, Vector3.smul]

/-- Lower-by-upper multiplication evaluates the scalar triple product in the
lower diagonal Peirce corner. -/
theorem lower_mul_upper (u v w : Vec3) :
    lower (Vector3.cross u v) * upper w =
      (tripleDet u v w) • SplitOctonion.idempotentE2 := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  rcases w with ⟨wx, wy, wz⟩
  ext <;> simp [lower, upper, tripleDet, SplitOctonion.mul,
    SplitOctonion.idempotentE2, Vector3.dot, Vector3.cross,
    Vector3.zero, Vector3.add, Vector3.sub, Vector3.smul,
    SplitOctonion.smul] <;> ring

/-- The scalar triple product is invariant under cyclic permutation. -/
theorem tripleDet_cyclic (u v w : Vec3) :
    tripleDet u v w = tripleDet v w u := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  rcases w with ⟨wx, wy, wz⟩
  simp [tripleDet, Vector3.dot, Vector3.cross]
  ring

/-- Upper-by-lower multiplication evaluates the same scalar triple product in
the upper diagonal Peirce corner. -/
theorem upper_mul_lower (u v w : Vec3) :
    upper u * lower (Vector3.cross v w) =
      (tripleDet u v w) • SplitOctonion.idempotentE1 := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  rcases w with ⟨wx, wy, wz⟩
  ext <;> simp [lower, upper, tripleDet, SplitOctonion.mul,
    SplitOctonion.idempotentE1, Vector3.dot, Vector3.cross,
    Vector3.zero, Vector3.add, Vector3.sub, Vector3.smul,
    SplitOctonion.smul] <;> ring

/-- First bracketing of three upper vectors lands entirely in the second
Peirce corner. -/
theorem upper_left_bracketing (u₁ u₂ u₃ : Vec3) :
    (upper u₁ * upper u₂) * upper u₃ =
      (tripleDet u₁ u₂ u₃) • SplitOctonion.idempotentE2 := by
  rw [upper_mul_upper]
  exact lower_mul_upper u₁ u₂ u₃

/-- Second bracketing lands entirely in the first Peirce corner. -/
theorem upper_right_bracketing (u₁ u₂ u₃ : Vec3) :
    upper u₁ * (upper u₂ * upper u₃) =
      (tripleDet u₁ u₂ u₃) • SplitOctonion.idempotentE1 := by
  rw [upper_mul_upper]
  exact upper_mul_lower u₁ u₂ u₃

/--
Associator--Peirce/Krein identity:
`[U₁,U₂,U₃] = -det(u₁,u₂,u₃) J`.
-/
theorem associator_upper_eq_neg_tripleDet_smul_kreinJ
    (u₁ u₂ u₃ : Vec3) :
    associator (upper u₁) (upper u₂) (upper u₃) =
      (-tripleDet u₁ u₂ u₃) • kreinJ := by
  rw [associator, upper_left_bracketing, upper_right_bracketing]
  ext <;> simp [kreinJ, SplitOctonion.idempotentE1,
    SplitOctonion.idempotentE2, SplitOctonion.smul] <;> ring

/-- Coordinate form of the same associator identity. -/
theorem associator_upper_coordinates
    (u₁ u₂ u₃ : Vec3) :
    associator (upper u₁) (upper u₂) (upper u₃) =
      ⟨-tripleDet u₁ u₂ u₃, 0, 0, tripleDet u₁ u₂ u₃⟩ := by
  rw [associator_upper_eq_neg_tripleDet_smul_kreinJ]
  ext <;> simp [kreinJ, SplitOctonion.idempotentE1,
    SplitOctonion.idempotentE2, SplitOctonion.smul]

/-- Nonzero oriented three-volume gives a genuinely nonzero associator. -/
theorem associator_upper_ne_zero_of_tripleDet_ne_zero
    (u₁ u₂ u₃ : Vec3)
    (hdet : tripleDet u₁ u₂ u₃ ≠ 0) :
    associator (upper u₁) (upper u₂) (upper u₃) ≠ 0 := by
  intro h
  have ha := congrArg SplitOctonion.a h
  rw [associator_upper_coordinates] at ha
  change -tripleDet u₁ u₂ u₃ = 0 at ha
  exact hdet (neg_eq_zero.mp ha)

/-- The associator of three upper vectors is always contained in the
one-dimensional span of the Peirce grading element. -/
theorem associator_upper_mem_span_kreinJ
    (u₁ u₂ u₃ : Vec3) :
    ∃ r : ℝ,
      associator (upper u₁) (upper u₂) (upper u₃) = r • kreinJ := by
  exact ⟨-tripleDet u₁ u₂ u₃,
    associator_upper_eq_neg_tripleDet_smul_kreinJ u₁ u₂ u₃⟩

end InfoGeometry.Canonical.ZornAssociatorKreinBridge
