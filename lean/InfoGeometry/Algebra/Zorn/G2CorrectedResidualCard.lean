/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CellwiseCoordinates
import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard

/-! Residual cardinalities for the corrected native simple generators. -/
namespace InfoGeometry.Algebra.Zorn.G2CorrectedResidualCard

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.GroupTheory.DoubleCoset
open G2ConcreteWeylG2 G2TwoOppositeUnipotent G2TwoPCSubgroupClosure
open G2TwoBruhatClassification G2BruhatResidual G2CorrectedWordLength

def longestShift (p : WeylG2) : WeylG2 := (p.1 + 3, p.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem longestShift_evaluation : ∀ p : WeylG2,
    weylNF (longestShift p).1 (longestShift p).2 = w0 * weylNF p.1 p.2 := by
  intro p
  apply automorphism_ext_of_basis
  intro i
  revert i p
  decide

theorem complementary_powers : ∀ p : WeylG2,
    2 ^ correctedLength (longestShift p) * 2 ^ correctedLength p = 64 := by
  decide

theorem residual_card (p : WeylG2) :
    Nat.card (residualSubgroup p) = 2 ^ correctedLength p := by
  classical
  let w := w0 * weylNF p.1 p.2
  let : Fintype {x : SplitOctF2Aut // x ∈ concreteBruhatCell w} := Fintype.ofFinite _
  let : Fintype (MulAction.orbit (unipotentSubgroup × unipotentSubgroup) w) :=
    Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (unipotentSubgroup × unipotentSubgroup) w) :=
    Fintype.ofFinite _
  let : Fintype {x : SplitOctF2Aut //
    x ∈ doubleCoset unipotentSubgroup w unipotentSubgroup} := Fintype.ofFinite _
  let : Fintype (intersectionSubgroup unipotentSubgroup
    (conjugateSubgroup w unipotentSubgroup)) := Fintype.ofFinite _
  have h := G2BruhatCellIntersectionCard.concreteBruhatCell_card_mul_intersection_card w
  simp only [← Nat.card_eq_fintype_card] at h
  change Nat.card (concreteBruhatCell (w0 * weylNF p.1 p.2)) *
    Nat.card (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup (w0 * weylNF p.1 p.2) unipotentSubgroup)) = 4096 at h
  rw [← residualSubgroup_eq_doubleCoset_intersection,
    ← longestShift_evaluation, G2CellwiseCoordinates.weyl_cell_card] at h
  have hprod := complementary_powers p
  have hpos : 0 < 64 * 2 ^ correctedLength (longestShift p) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    (64 * 2 ^ correctedLength (longestShift p)) * Nat.card (residualSubgroup p) =
        4096 := h
    _ = (64 * 2 ^ correctedLength (longestShift p)) * 2 ^ correctedLength p := by
      rw [Nat.mul_assoc, hprod]

end InfoGeometry.Algebra.Zorn.G2CorrectedResidualCard
