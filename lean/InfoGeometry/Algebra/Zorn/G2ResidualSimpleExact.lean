import InfoGeometry.Algebra.Zorn.G2CorrectedTComplementPartition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleCase
import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
import InfoGeometry.Algebra.Zorn.G2PCWeylReadoutSeparation
import InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard

/-!
# Exact residual intersection in the corrected simple Weyl case

The second component of the index-two unipotent partition is excluded from
the residual intersection by the already certified identity-cell disjointness.
This is a group-theoretic transport proof; it does not enumerate the carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact

open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.Algebra.Zorn.G2CorrectedTComplementCard
open InfoGeometry.Algebra.Zorn.G2CorrectedTComplementPartition
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleCase
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.GroupTheory.DoubleCoset
open InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard

theorem correctedT_inv_eq : correctedT⁻¹ = correctedT := by
  calc
    correctedT⁻¹ = correctedT⁻¹ * 1 := by simp
    _ = correctedT⁻¹ * (correctedT * correctedT) := by rw [correctedT_sq]
    _ = correctedT := by group

theorem residual_conjugate_mem_unipotent
    {x : SplitOctF2Aut}
    (hx : x ∈ residualSubgroup (2, true)) :
    correctedT * x * correctedT ∈ unipotentSubgroup := by
  have h := (Subgroup.mem_inf.mp hx).2
  change correctedT⁻¹ * x * correctedT ∈ unipotentSubgroup at h
  rw [correctedT_inv_eq] at h
  exact h

theorem second_coset_conjugate_mem_cell_eleven
    {h : SplitOctF2Aut}
    (hh : h ∈ correctedTComplementSubgroup) :
    correctedT *
        (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h) *
        correctedT ∈ concreteBruhatCell correctedT := by
  have hc : correctedT⁻¹ * h * correctedT ∈ unipotentSubgroup :=
    correctedT_complement_conj_mem_unipotent h hh
  let c : SplitOctF2Aut := correctedT⁻¹ * h * correctedT
  have hc' : c ∈ unipotentSubgroup := by exact hc
  have hd :
      G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * c ∈
        unipotentSubgroup :=
    unipotentSubgroup.mul_mem
      ⟨correctedTRankOneExponent, rfl⟩ hc'
  have hrel :
      correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent *
          correctedT =
        G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT *
          G2TwoSylowSubgroup.pcWord correctedTRankOneExponent := by
    simpa [correctedTRankOneExponent] using correctedT_rank_one_witness
  have hTr :
      correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent =
        G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT *
          G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT := by
    calc
      correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent =
          (correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent) * 1 := by
            simp only [_root_.mul_one]
      _ = (correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent) *
            (correctedT * correctedT) := by rw [correctedT_sq]
      _ = ((correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent) *
            correctedT) * correctedT := by simp only [mul_assoc]
      _ = (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT *
            G2TwoSylowSubgroup.pcWord correctedTRankOneExponent) * correctedT := by
              rw [hrel]
      _ = G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT *
          G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT := by
            simp only [mul_assoc]
  have heq :
      correctedT *
          (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h) *
          correctedT =
        G2TwoSylowSubgroup.pcWord correctedTRankOneExponent *
          correctedT *
          (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * c) := by
    calc
      correctedT *
          (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h) *
          correctedT =
          (correctedT * G2TwoSylowSubgroup.pcWord correctedTRankOneExponent) *
            h * correctedT := by simp only [mul_assoc]
      _ = (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT *
          G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT) *
            h * correctedT := by rw [hTr]
      _ = G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * correctedT *
          (G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * c) := by
            dsimp [c]
            rw [correctedT_inv_eq]
            group
  rw [concreteBruhatCell]
  refine ⟨G2TwoSylowSubgroup.pcWord correctedTRankOneExponent,
    G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * c, ?_, ?_, heq⟩
  · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact ⟨correctedTRankOneExponent, rfl⟩
  · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact hd

theorem correctedT_not_mem_unipotentSubgroup :
    correctedT ∉ unipotentSubgroup := by
  intro hT
  rcases hT with ⟨e, he⟩
  exact G2PCWeylReadoutSeparation.pcWord_ne_concreteWeylElement_eleven e
    (by simpa [correctedT] using he)

theorem identity_cell_disjoint_correctedT :
    Disjoint (concreteBruhatCell (1 : SplitOctF2Aut))
      (concreteBruhatCell correctedT) := by
  rw [Set.disjoint_left]
  intro g hg0 hgT
  rcases hgT with ⟨b₁, b₂, hb₁, hb₂, hgb⟩
  have hgU : g ∈ unipotentSubgroup := by
    have hmem := congrArg
      (fun S : Set SplitOctF2Aut => g ∈ S)
      concreteBruhatCell_one_eq_sylow
    have hgs : g ∈ sylowTwoSubgroup := hmem.mp hg0
    change g ∈ (sylowTwoSubgroup : Set SplitOctF2Aut) at hgs
    have hsets : (sylowTwoSubgroup : Set SplitOctF2Aut) =
        (unipotentSubgroup : Set SplitOctF2Aut) := by
      rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    rw [hsets] at hgs
    exact hgs
  have hb₁U : b₁ ∈ unipotentSubgroup := by
    have h : b₁ ∈ (sylowTwoSubgroup : Set SplitOctF2Aut) := hb₁
    have hsets : (sylowTwoSubgroup : Set SplitOctF2Aut) =
        (unipotentSubgroup : Set SplitOctF2Aut) := by
      rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    rw [hsets] at h
    exact h
  have hb₂U : b₂ ∈ unipotentSubgroup := by
    have h : b₂ ∈ (sylowTwoSubgroup : Set SplitOctF2Aut) := hb₂
    have hsets : (sylowTwoSubgroup : Set SplitOctF2Aut) =
        (unipotentSubgroup : Set SplitOctF2Aut) := by
      rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    rw [hsets] at h
    exact h
  have hT : correctedT ∈ unipotentSubgroup := by
    have hleft := unipotentSubgroup.mul_mem
      (unipotentSubgroup.mul_mem (unipotentSubgroup.inv_mem hb₁U) hgU)
      (unipotentSubgroup.inv_mem hb₂U)
    rw [hgb] at hleft
    simpa [correctedT, mul_assoc] using hleft
  exact correctedT_not_mem_unipotentSubgroup hT

theorem residualSubgroup_simple_eq_correctedTComplementSubgroup :
    residualSubgroup (2, true) = correctedTComplementSubgroup := by
  apply le_antisymm
  · intro x hx
    have hxU : x ∈ unipotentSubgroup := (Subgroup.mem_inf.mp hx).1
    rcases correctedT_borel_split x hxU with hxC | ⟨h, hh, hxh⟩
    · exact hxC
    · exfalso
      have hyU : correctedT * x * correctedT ∈ unipotentSubgroup :=
        residual_conjugate_mem_unipotent hx
      have hy0 : correctedT * x * correctedT ∈
          concreteBruhatCell (1 : SplitOctF2Aut) := by
        rw [concreteBruhatCell_one_eq_sylow]
        rw [sylowTwoSubgroup_eq_unipotentSubgroup]
        exact hyU
      have hy11 : correctedT * x * correctedT ∈ concreteBruhatCell correctedT := by
        rw [hxh]
        exact second_coset_conjugate_mem_cell_eleven hh
      exact (Set.disjoint_left.mp identity_cell_disjoint_correctedT) hy0 hy11
  · exact correctedTComplementSubgroup_le_residualSubgroup

theorem residualSubgroup_simple_card_eq_32 :
    Nat.card (residualSubgroup (2, true)) = 32 := by
  rw [residualSubgroup_simple_eq_correctedTComplementSubgroup]
  exact correctedTComplementSubgroup_card

theorem residual_intersection_correctedT_eq :
    intersectionSubgroup unipotentSubgroup
        (conjugateSubgroup correctedT unipotentSubgroup) =
      residualSubgroup (2, true) := by
  rw [residualSubgroup_eq_doubleCoset_intersection]
  rw [← correctedT_eq_w0_mul_weylNF]

theorem correctedT_bruhatCell_card :
    Nat.card {x : SplitOctF2Aut // x ∈ concreteBruhatCell correctedT} =
      128 := by
  letI : Fintype {x : SplitOctF2Aut // x ∈ concreteBruhatCell correctedT} :=
    Fintype.ofFinite _
  letI : Fintype (MulAction.orbit
      (unipotentSubgroup × unipotentSubgroup) correctedT) :=
    Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer
      (unipotentSubgroup × unipotentSubgroup) correctedT) :=
    Fintype.ofFinite _
  letI : Fintype {x : SplitOctF2Aut //
      x ∈ doubleCoset unipotentSubgroup correctedT unipotentSubgroup} :=
    Fintype.ofFinite _
  letI : Fintype (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup correctedT unipotentSubgroup)) :=
    Fintype.ofFinite _
  have hprod := concreteBruhatCell_card_mul_intersection_card correctedT
  have hinterNat :
      Nat.card (intersectionSubgroup unipotentSubgroup
        (conjugateSubgroup correctedT unipotentSubgroup)) = 32 := by
    rw [residual_intersection_correctedT_eq]
    exact residualSubgroup_simple_card_eq_32
  have hinter :
      Fintype.card (intersectionSubgroup unipotentSubgroup
        (conjugateSubgroup correctedT unipotentSubgroup)) = 32 := by
    simpa only [Nat.card_eq_fintype_card] using hinterNat
  rw [hinter] at hprod
  have hcard :
      Fintype.card {x : SplitOctF2Aut // x ∈ concreteBruhatCell correctedT} =
        128 := by
    omega
  simpa [Nat.card_eq_fintype_card] using hcard

end InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
