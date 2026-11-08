/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact

/-! Explicit coordinates for the entire corrected reflection double coset. -/
namespace InfoGeometry.Algebra.Zorn.G2CorrectedCellCoordinates

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2ConcreteBN2CorrectSecondConjugation G2TwoPCSubgroupClosure
open G2TwoBruhatClassification G2TwoSylowSubgroup G2ResidualSimpleExact

noncomputable def cellMap (z : Bool × unipotentSubgroup) :
    concreteBruhatCell correctedT :=
  ⟨(if z.1 then pcWord correctedTRankOneExponent else 1) * correctedT * z.2.1, by
    refine ⟨_, _, ?_, ?_, rfl⟩
    · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
      cases z.1
      · exact unipotentSubgroup.one_mem
      · exact ⟨correctedTRankOneExponent, rfl⟩
    · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
      exact z.2.2⟩

theorem cellMap_surjective : Function.Surjective cellMap := by
  rintro ⟨g, a, b, ha, hb, rfl⟩
  rw [sylowTwoSubgroup_eq_unipotentSubgroup] at ha hb
  rcases correctedT_borel_split a ha with h | ⟨h, hh, rfl⟩
  · refine ⟨(false, ⟨(correctedT⁻¹ * a * correctedT) * b,
      unipotentSubgroup.mul_mem (correctedT_complement_conj_mem_unipotent a h) hb⟩), ?_⟩
    apply Subtype.ext
    change 1 * correctedT * ((correctedT⁻¹ * a * correctedT) * b) = _
    group
  · refine ⟨(true, ⟨(correctedT⁻¹ * h * correctedT) * b,
      unipotentSubgroup.mul_mem (correctedT_complement_conj_mem_unipotent h hh) hb⟩), ?_⟩
    apply Subtype.ext
    change pcWord correctedTRankOneExponent * correctedT *
      ((correctedT⁻¹ * h * correctedT) * b) = _
    group

theorem cellMap_bijective : Function.Bijective cellMap := by
  apply (Nat.bijective_iff_surjective_and_card cellMap).2
  refine ⟨cellMap_surjective, ?_⟩
  rw [Nat.card_prod, unipotentSubgroup_card, correctedT_bruhatCell_card]
  simp [Nat.card_eq_fintype_card]

/-- One Boolean branch and one native unipotent element, with no redundancy. -/
noncomputable def cellEquiv :
    (Bool × unipotentSubgroup) ≃ concreteBruhatCell correctedT :=
  Equiv.ofBijective cellMap cellMap_bijective

theorem cellEquiv_apply (z : Bool × unipotentSubgroup) :
    (cellEquiv z).1 =
      (if z.1 then pcWord correctedTRankOneExponent else 1) * correctedT * z.2.1 := rfl

theorem exists_unique_coordinates (g : concreteBruhatCell correctedT) :
    ∃! z : Bool × unipotentSubgroup,
      (if z.1 then pcWord correctedTRankOneExponent else 1) * correctedT * z.2.1 = g.1 := by
  refine ⟨cellEquiv.symm g, congrArg Subtype.val (cellEquiv.apply_symm_apply g), ?_⟩
  intro z hz
  apply cellEquiv.injective
  exact (Subtype.ext hz).trans (cellEquiv.apply_symm_apply g).symm

end InfoGeometry.Algebra.Zorn.G2CorrectedCellCoordinates
