/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Peirce bulk transfer through opposite-corner sandwiches

The cross sandwich has only diagonal Peirce support and depends only on the
diagonal part of its input. This is an algebraic statement in an arbitrary
ring; no geometric or holographic interpretation is needed for the proof.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The two-step action of `Φ` is the inner derivation of the bulk metric.
This is the exact boundary-to-bulk connection identity, valid on the whole
operator ring. -/
theorem genPhi_anticomm_comm_eq_genV_comm
    {P : B} (hP : P * P = P) (A C X : B) :
    anticomm (genPhi P A C) (comm (genPhi P A C) X) =
      comm (genV P A C) X := by
  obtain ⟨_, _, _, _, _, h⟩ :=
    archetype_A1_dual_leibniz_and_jacobi (genPhi P A C) X X
  have hPhi := (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
  rw [h, hPhi]

theorem sandwichCross_is_even_and_factors_through_even
    {P : B} (hP : P * P = P) (A C X : B) :
    oddGrade P (sandwichCross P A C X) = 0 ∧
    evenGrade P (sandwichCross P A C X) = sandwichCross P A C X ∧
    sandwichCross P A C (oddGrade P X) = 0 ∧
    sandwichCross P A C (evenGrade P X) = sandwichCross P A C X := by
  simp only [sandwichCross, oddGrade, evenGrade, conePlus, coneMinus]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- On an even Peirce input, the cross-cone transfer is recovered without
division from the metric Jordan action and the double commutator by `Φ`.
The double commutator is essential: the corresponding single-commutator
expression is `{V, E} - [Φ, {Φ, E}] = 2 E V`, which is not generally the
cross-cone transfer. -/
theorem sandwichCross_even_reconstruction
    {P : B} (hP : P * P = P) (A C X : B) :
    (2 : ℤ) • sandwichCross P A C (evenGrade P X) =
      anticomm (genV P A C) (evenGrade P X) -
        comm (genPhi P A C)
          (comm (genPhi P A C) (evenGrade P X)) := by
  simp only [sandwichCross, evenGrade, genV, anticomm, genPhi, comm,
    conePlus, coneMinus, sub_mul, mul_sub, add_mul, mul_add,
    zsmul_add, zsmul_sub]
  peirce_nf hP

/-- Corrected source-facing A93 synthesis. The filter, parity intertwiners,
and connection identity hold as stated. The source's final single-commutator
expression is right multiplication by `V`; the crossed-corner transfer is
recovered by the separate double-commutator identity. -/
theorem archetype_A93_bulk_boundary_transfer_corrected
    {P : B} (hP : P * P = P) (A C X Y : B) :
    oddGrade P (sandwichCross P A C X) = 0 ∧
    evenGrade P (sandwichCross P A C X) = sandwichCross P A C X ∧
    sandwichCross P A C (oddGrade P X) = 0 ∧
    sandwichCross P A C (evenGrade P X) = sandwichCross P A C X ∧
    evenGrade P (comm (genPhi P A C) (evenGrade P X)) = 0 ∧
    oddGrade P (anticomm (genPhi P A C) (oddGrade P Y)) = 0 ∧
    anticomm (genPhi P A C) (comm (genPhi P A C) (evenGrade P X)) =
      comm (genV P A C) (evenGrade P X) ∧
    anticomm (genV P A C) (evenGrade P X) -
      comm (genPhi P A C) (anticomm (genPhi P A C) (evenGrade P X)) =
      (2 : ℤ) • (evenGrade P X * genV P A C) ∧
    (2 : ℤ) • sandwichCross P A C (evenGrade P X) =
      anticomm (genV P A C) (evenGrade P X) -
        comm (genPhi P A C)
          (comm (genPhi P A C) (evenGrade P X)) := by
  have hFilter := sandwichCross_is_even_and_factors_through_even hP A C X
  refine ⟨hFilter.1, hFilter.2.1, hFilter.2.2.1, hFilter.2.2.2,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evenGrade, comm, genPhi, conePlus, coneMinus]
    peirce_nf hP
  · simp only [oddGrade, anticomm, genPhi, conePlus, coneMinus]
    peirce_nf hP
  · exact genPhi_anticomm_comm_eq_genV_comm hP A C (evenGrade P X)
  · exact tetraktys_nested_bulk_expression hP A C (evenGrade P X)
  · exact sandwichCross_even_reconstruction hP A C X

end InfoGeometry.OperatorAlgebra.PeirceSpine
