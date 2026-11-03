/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Operator-valued Kauffman phase identities

The scalar Witten–Jones phase identity has a direct ordered-ring analogue.
For a two-sided inverse pair in an arbitrary unital ring, the cross terms in
`(A - A⁻¹)^2` reduce separately to the unit. No commutativity, field, trace,
or diagonal representation is used.

These are algebraic phase identities only. They do not identify the resulting
operator with a cosmological constant or establish a Chern–Simons/TQFT
interpretation.
-/

namespace InfoGeometry.Topology.WittenJonesOperatorPhase

variable {B : Type*} [Ring B]

/-- Ordered operator analogue of the normalized Kauffman phase defect. -/
def operatorCosmoDefect (A Ainv : B) : B :=
  A * A + Ainv * Ainv - 1 - 1

/-- The operator-valued loop expression used in the scalar phase model. -/
def operatorUnknotLoop (A Ainv : B) : B :=
  -(A * A) - (Ainv * Ainv)

/-- The phase-square identity in an arbitrary associative ring. Both inverse
orders are needed because expansion produces `A * Ainv` and `Ainv * A`. -/
theorem operator_phase_square_eq_cosmo_defect
    (A Ainv : B) (hRightInv : A * Ainv = 1) (hLeftInv : Ainv * A = 1) :
    (A - Ainv) * (A - Ainv) = operatorCosmoDefect A Ainv := by
  calc
    (A - Ainv) * (A - Ainv) =
        A * A - A * Ainv - Ainv * A + Ainv * Ainv := by noncomm_ring
    _ = A * A - 1 - 1 + Ainv * Ainv := by rw [hRightInv, hLeftInv]
    _ = operatorCosmoDefect A Ainv := by
      dsimp [operatorCosmoDefect]
      abel

/-- The loop expression is the negative phase defect shifted by `-2`; this
identity is unconditional and uses no inverse law. -/
theorem operator_unknot_loop_eq_neg_defect_sub_one_twice (A Ainv : B) :
    operatorUnknotLoop A Ainv = -operatorCosmoDefect A Ainv - 1 - 1 := by
  dsimp [operatorUnknotLoop, operatorCosmoDefect]
  norm_num
  abel_nf

/-- The same loop identity with the two unit subtractions written as `2`. -/
theorem operator_unknot_loop_eq_neg_defect_sub_two (A Ainv : B) :
    operatorUnknotLoop A Ainv = -operatorCosmoDefect A Ainv - 2 := by
  have hTwo : (2 : B) = (1 : B) + 1 := by norm_num
  calc
    operatorUnknotLoop A Ainv = -operatorCosmoDefect A Ainv - 1 - 1 :=
      operator_unknot_loop_eq_neg_defect_sub_one_twice A Ainv
    _ = -operatorCosmoDefect A Ainv - ((1 : B) + 1) := by noncomm_ring
    _ = -operatorCosmoDefect A Ainv - 2 := by rw [← hTwo]

/-- A compact synthesis of the ordered phase identities. -/
theorem operator_phase_identity_synthesis
    (A Ainv : B) (hRightInv : A * Ainv = 1) (hLeftInv : Ainv * A = 1) :
    (A - Ainv) * (A - Ainv) = operatorCosmoDefect A Ainv ∧
    operatorUnknotLoop A Ainv = -operatorCosmoDefect A Ainv - 2 :=
  ⟨operator_phase_square_eq_cosmo_defect A Ainv hRightInv hLeftInv,
    operator_unknot_loop_eq_neg_defect_sub_two A Ainv⟩

end InfoGeometry.Topology.WittenJonesOperatorPhase
