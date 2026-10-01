import Mathlib.Tactic

import InfoGeometry.Canonical.ZornAssociatorKreinBridge

/-!
# Two-generator vanishing and three-generator Zorn associator obstruction

This module isolates the theorem-safe algebraic content behind the statement
that three independent upper Zorn directions are the minimal input needed for
the scalar-triple-product associator used by the repository.

It does not identify this obstruction with CKM mixing or CP violation.  Such
an identification requires an additional representation of flavor states,
mass operators, and the physical Jarlskog invariant.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornThreeGeneratorObstruction

open InfoGeometry.Algebra.SplitOctonionZorn
open InfoGeometry.Canonical.ZornAssociatorKreinBridge

abbrev Vec3 := ZornAssociatorKreinBridge.Vec3
abbrev Zorn := ZornAssociatorKreinBridge.Zorn

/-- First canonical upper direction. -/
def e0 : Vec3 := ⟨1, 0, 0⟩

/-- Second canonical upper direction. -/
def e1 : Vec3 := ⟨0, 1, 0⟩

/-- Third canonical upper direction. -/
def e2 : Vec3 := ⟨0, 0, 1⟩

@[simp] theorem tripleDet_self_left (u v : Vec3) :
    tripleDet u u v = 0 := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  simp [tripleDet, Vector3.dot, Vector3.cross]
  ring

@[simp] theorem tripleDet_self_right (u v : Vec3) :
    tripleDet u v v = 0 := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  simp [tripleDet, Vector3.dot, Vector3.cross]
  ring

@[simp] theorem tripleDet_first_eq_third (u v : Vec3) :
    tripleDet u v u = 0 := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  simp [tripleDet, Vector3.dot, Vector3.cross]
  ring

/-- Alternativity shadow on the upper Zorn sector:
the associator vanishes when the first two upper generators coincide. -/
@[simp] theorem associator_upper_self_left (u v : Vec3) :
    associator (upper u) (upper u) (upper v) = 0 := by
  rw [associator_upper_eq_neg_tripleDet_smul_kreinJ]
  simp

/-- The associator vanishes when the last two upper generators coincide. -/
@[simp] theorem associator_upper_self_right (u v : Vec3) :
    associator (upper u) (upper v) (upper v) = 0 := by
  rw [associator_upper_eq_neg_tripleDet_smul_kreinJ]
  simp

/-- The associator vanishes when the first and third upper generators coincide. -/
@[simp] theorem associator_upper_first_eq_third (u v : Vec3) :
    associator (upper u) (upper v) (upper u) = 0 := by
  rw [associator_upper_eq_neg_tripleDet_smul_kreinJ]
  simp

/--
Every ordered triple chosen from only two fixed upper generators has zero
associator.

This is a finite upper-sector consequence of the alternating scalar triple
product; it is deliberately weaker than a full formalization of Artin's
two-generated-subalgebra theorem.
-/
theorem two_upper_generators_associator_zero
    (u v : Vec3)
    (x y z : Bool) :
    let pick : Bool → Zorn := fun b => if b then upper u else upper v
    associator (pick x) (pick y) (pick z) = 0 := by
  intro pick
  cases x <;> cases y <;> cases z <;>
    simp [pick, associator_upper_self_left,
      associator_upper_self_right, associator_upper_first_eq_third]

/-- The canonical oriented upper basis has unit scalar triple product. -/
@[simp] theorem tripleDet_e0_e1_e2 :
    tripleDet e0 e1 e2 = 1 := by
  norm_num [tripleDet, e0, e1, e2, Vector3.dot, Vector3.cross]

/--
Three independent canonical upper directions have nonzero associator:
`[U(e0),U(e1),U(e2)] = -J`.
-/
theorem canonical_three_upper_associator :
    associator (upper e0) (upper e1) (upper e2) = -kreinJ := by
  rw [associator_upper_eq_neg_tripleDet_smul_kreinJ,
    tripleDet_e0_e1_e2]
  simp

/-- In particular, the canonical three-generator associator is nonzero. -/
theorem canonical_three_upper_associator_ne_zero :
    associator (upper e0) (upper e1) (upper e2) ≠ 0 := by
  apply associator_upper_ne_zero_of_tripleDet_ne_zero
  norm_num [tripleDet_e0_e1_e2]

/--
Exact minimal-arity witness for this upper-sector associator:
two fixed generators give only zero associators, while the three canonical
independent generators give a nonzero associator.
-/
theorem upper_sector_three_generator_obstruction
    (u v : Vec3) :
    (∀ x y z : Bool,
      let pick : Bool → Zorn := fun b => if b then upper u else upper v
      associator (pick x) (pick y) (pick z) = 0) ∧
    associator (upper e0) (upper e1) (upper e2) ≠ 0 := by
  constructor
  · intro x y z
    exact two_upper_generators_associator_zero u v x y z
  · exact canonical_three_upper_associator_ne_zero

end InfoGeometry.Canonical.ZornThreeGeneratorObstruction
