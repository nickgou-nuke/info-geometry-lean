/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.OrthogonalPolynomial
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Units.Hom

/-!
# Unit-shell dihedral representation of the Peirce generators

The existing off-shell identities specialize to a native representation of
`DihedralGroup 3` in the units of an arbitrary associative ring when `V = 1`.
No faithfulness or analytic interpretation is asserted.

The unit-shell condition is distinguished from the weaker idempotency of
`V`: the latter characterizes equality of reflection squares and kills all
positive iterates of its idempotency defect.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Algebra.OrthogonalPolynomial

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)

/-- The third cyclotomic polynomial vanishes exactly on the unit shell. -/
theorem cubeRoot_cyclotomic_eq_zero_iff (A C : B) :
    cyclotomicThree (cubeRootOp P A C) = 0 ↔ genV P A C = 1 := by
  obtain ⟨_, _, _, _, _, _, _, h, _⟩ :=
    archetype_A58_operator_cyclotomic_roots_and_discriminants hP A C
  rw [h, sub_eq_zero, eq_comm]

/-- Equality of the first two reflection squares only requires `V² = V`. -/
theorem s3Refl_square_eq_iff_defect_zero (A C : B) :
    s3Refl1 P A C * s3Refl1 P A C = s3Refl0 P A C * s3Refl0 P A C ↔
      idempotencyDefect (genV P A C) = 0 := by
  obtain ⟨_, _, h0, h1, _⟩ := s3Refl_components_squares_and_anticomm hP A C
  rw [h1, h0, idempotencyDefect_eq_zero_iff]

/-- Reflection-square equality collapses the complete positive defect orbit. -/
theorem s3Refl_square_eq_defect_iterates_zero (A C : B)
    (h : s3Refl1 P A C * s3Refl1 P A C = s3Refl0 P A C * s3Refl0 P A C)
    (n : ℕ) : idempotencyDefect^[n + 1] (genV P A C) = 0 := by
  exact idempotencyDefect_iterates_succ_eq_zero
    ((s3Refl_square_eq_iff_defect_zero hP A C).mp h) n

/-- Arbitrary integer polynomials split over the two cycles, with the exact
constant correction. This includes polynomials beyond the defect iteration. -/
theorem genV_polynomial_cycle_split (A C : B) (p : Polynomial ℤ) :
    p.eval₂ (Int.castRingHom B) (genV P A C) =
      p.eval₂ (Int.castRingHom B) (qgtPlus P A C) +
        p.eval₂ (Int.castRingHom B) (qgtMinus P A C) - (p.coeff 0 : B) := by
  change p.eval₂ (Int.castRingHom B) (qgtPlus P A C + qgtMinus P A C) = _
  exact eval₂_add_of_orthogonal (Int.castRingHom B) p
    (qgt_cycles_orthogonal hP A C).1 (qgt_cycles_orthogonal hP A C).2

/-- The three rotation values, indexed by the native cyclic group. -/
def peirceThreeRotation (P A C : B) (i : ZMod 3) : B :=
  if i = 0 then 1 else if i = 1 then cubeRootOp P A C else cubeRootOpConj P A C

@[simp] theorem peirceThreeRotation_zero (P A C : B) :
    peirceThreeRotation P A C 0 = 1 := by simp [peirceThreeRotation]

@[simp] theorem peirceThreeRotation_one (P A C : B) :
    peirceThreeRotation P A C 1 = cubeRootOp P A C := by
  norm_num [peirceThreeRotation]

@[simp] theorem peirceThreeRotation_two (P A C : B) :
    peirceThreeRotation P A C 2 = cubeRootOpConj P A C := by
  norm_num [peirceThreeRotation]

/-- On `V = 1`, the rotation values preserve cyclic addition. -/
theorem peirceThreeRotation_add (A C : B) (hV : genV P A C = 1)
    (i j : ZMod 3) :
    peirceThreeRotation P A C (i + j) =
      peirceThreeRotation P A C i * peirceThreeRotation P A C j := by
  obtain ⟨_, hab, hba, haa, hbb, _⟩ :=
    archetype_A59_s3_operator_cyclotomic_braiding_and_reflections hP A C
  have haa' : cubeRootOp P A C * cubeRootOp P A C = cubeRootOpConj P A C :=
    sub_eq_zero.mp (by simpa [hV] using haa)
  have hbb' : cubeRootOpConj P A C * cubeRootOpConj P A C = cubeRootOp P A C :=
    sub_eq_zero.mp (by simpa [hV] using hbb)
  fin_cases i <;> fin_cases j <;>
    norm_num [peirceThreeRotation, haa', hbb', hab, hba, hV]

/-- Reflection reverses the cyclic parameter. The braiding is valid even off shell. -/
theorem peirceThreeRotation_mul_phi (A C : B) (i : ZMod 3) :
    peirceThreeRotation P A C i * genPhi P A C =
      genPhi P A C * peirceThreeRotation P A C (-i) := by
  obtain ⟨_, _, _, _, _, ha, hb, _⟩ :=
    archetype_A59_s3_operator_cyclotomic_braiding_and_reflections hP A C
  fin_cases i <;> norm_num [peirceThreeRotation, ha, hb]

/-- The native order-six dihedral group acts by the Peirce operators on the
unit shell. Mathlib's `sr i` is reflection followed by rotation. -/
def peirceDihedralMonoidHom (A C : B) (hV : genV P A C = 1) :
    DihedralGroup 3 →* B where
  toFun
    | .r i => peirceThreeRotation P A C i
    | .sr i => genPhi P A C * peirceThreeRotation P A C i
  map_one' := peirceThreeRotation_zero P A C
  map_mul' := by
    have hPhi : genPhi P A C * genPhi P A C = 1 := by
      exact (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1.trans hV
    intro g h
    cases g with
    | r i =>
        cases h with
        | r j => exact peirceThreeRotation_add hP A C hV i j
        | sr j =>
            change genPhi P A C * peirceThreeRotation P A C (j - i) =
              peirceThreeRotation P A C i *
                (genPhi P A C * peirceThreeRotation P A C j)
            rw [← mul_assoc, peirceThreeRotation_mul_phi hP, mul_assoc,
              ← peirceThreeRotation_add hP A C hV]
            congr 2
            abel
    | sr i =>
        cases h with
        | r j =>
            change genPhi P A C * peirceThreeRotation P A C (i + j) =
              (genPhi P A C * peirceThreeRotation P A C i) *
                peirceThreeRotation P A C j
            rw [peirceThreeRotation_add hP A C hV, mul_assoc]
        | sr j =>
            change peirceThreeRotation P A C (j - i) =
              (genPhi P A C * peirceThreeRotation P A C i) *
                (genPhi P A C * peirceThreeRotation P A C j)
            rw [mul_assoc, ← mul_assoc (peirceThreeRotation P A C i),
              peirceThreeRotation_mul_phi hP, mul_assoc, ← mul_assoc (genPhi P A C),
              hPhi, one_mul, ← peirceThreeRotation_add hP A C hV]
            congr 1
            abel

/-- The ring-valued representation canonically lifts to actual units. -/
def peirceDihedralUnitHom (A C : B) (hV : genV P A C = 1) :
    DihedralGroup 3 →* Bˣ :=
  (peirceDihedralMonoidHom hP A C hV).toHomUnits

@[simp] theorem peirceDihedralUnitHom_rotation (A C : B)
    (hV : genV P A C = 1) :
    ((peirceDihedralUnitHom hP A C hV (.r 1) : Bˣ) : B) = cubeRootOp P A C := by
  exact peirceThreeRotation_one P A C

@[simp] theorem peirceDihedralUnitHom_reflection (A C : B)
    (hV : genV P A C = 1) :
    ((peirceDihedralUnitHom hP A C hV (.sr 0) : Bˣ) : B) = genPhi P A C := by
  change genPhi P A C * peirceThreeRotation P A C 0 = genPhi P A C
  simp

end InfoGeometry.OperatorAlgebra.PeirceSpine
