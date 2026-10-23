/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CorrectedBruhatCover
import InfoGeometry.Algebra.Zorn.G2SignatureCellSeparation
import InfoGeometry.Algebra.Zorn.G2CorrectedWordLength
import InfoGeometry.Algebra.Zorn.G2SignatureCompleteness

/-! Cell-preserving coordinates from the corrected native quotient enumeration. -/
namespace InfoGeometry.Algebra.Zorn.G2CellwiseCoordinates

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2CorrectedQuotientCertificate G2CorrectedCosetSignature G2CorrectedBruhatCover
open G2FlagOrbitPartitionCertificate G2QuotientOrbitSeparation
open G2TwoBruhatClassification G2TwoPCSubgroupClosure G2TwoSylowSubgroup
open G2ConcreteWeylG2 G2CorrectedWordLength

theorem inverse_cells_disjoint {k l : Fin 12} (h : k ≠ l) :
    Disjoint (concreteBruhatCell (orbitWeylRepresentative k)⁻¹)
      (concreteBruhatCell (orbitWeylRepresentative l)⁻¹) := by
  rw [Set.disjoint_left]
  intro g hg hk
  have hg' := inverse_mem_cell hg
  have hk' := inverse_mem_cell hk
  simp only [inv_inv] at hg' hk'
  exact Set.disjoint_left.mp (G2SignatureCellSeparation.cells_disjoint h) hg' hk'

noncomputable def cellMap (k : Fin 12)
    (z : {i : Fin 189 // i ∈ orbitCells k} × unipotentSubgroup) :
    concreteBruhatCell (orbitWeylRepresentative k)⁻¹ :=
  ⟨(correctedQuotientRepresentative z.1.1)⁻¹ * z.2.1,
    concreteBruhatCell_right_mul _ _ _
      (by rw [sylowTwoSubgroup_eq_unipotentSubgroup]; exact z.2.2)
      (inverse_correctedRepresentative_mem k z.1.1 z.1.2)⟩

theorem cellMap_bijective (k : Fin 12) : Function.Bijective (cellMap k) := by
  constructor
  · rintro ⟨i, u⟩ ⟨j, v⟩ h
    have hv := congrArg Subtype.val h
    have hq : correctedCoset i.1 = correctedCoset j.1 := by
      apply G2SignatureCompleteness.quotient_eq_of_cosetSignature_eq
      have hs := congrArg cosetSignature hv
      change cosetSignature ((correctedQuotientRepresentative i.1)⁻¹ * u.1) =
        cosetSignature ((correctedQuotientRepresentative j.1)⁻¹ * v.1) at hs
      rwa [cosetSignature_mul_right _ u.2, cosetSignature_mul_right _ v.2] at hs
    have hij : i = j := Subtype.ext (correctedCoset_injective hq)
    subst j
    have huv : u = v := Subtype.ext (mul_left_cancel hv)
    subst v
    rfl
  · intro g
    obtain ⟨i, hi⟩ := correctedCoset_bijective.2 (QuotientGroup.mk g.1)
    have hmem : i ∈ Finset.univ.biUnion orbitCells := by
      rw [orbitCells_partition]; exact Finset.mem_univ i
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hmem
    have hu : correctedQuotientRepresentative i * g.1 ∈ unipotentSubgroup := by
      rw [correctedCoset, QuotientGroup.eq] at hi
      simpa using hi
    have hgl : g.1 ∈ concreteBruhatCell (orbitWeylRepresentative l)⁻¹ := by
      have hm := concreteBruhatCell_right_mul _ _ _
        (show correctedQuotientRepresentative i * g.1 ∈ sylowTwoSubgroup by
          rwa [sylowTwoSubgroup_eq_unipotentSubgroup])
        (inverse_correctedRepresentative_mem l i hl)
      simpa [mul_assoc, orbitWeylRepresentative] using hm
    have hlk : l = k := by
      by_contra hne
      exact Set.disjoint_left.mp (inverse_cells_disjoint hne) hgl g.2
    subst l
    refine ⟨(⟨i, hl⟩, ⟨correctedQuotientRepresentative i * g.1, hu⟩), ?_⟩
    apply Subtype.ext
    change (correctedQuotientRepresentative i)⁻¹ *
      (correctedQuotientRepresentative i * g.1) = g.1
    group

noncomputable def cellEquiv (k : Fin 12) :
    ({i : Fin 189 // i ∈ orbitCells k} × unipotentSubgroup) ≃
      concreteBruhatCell (orbitWeylRepresentative k)⁻¹ :=
  Equiv.ofBijective (cellMap k) (cellMap_bijective k)

theorem cellEquiv_apply (k : Fin 12)
    (z : {i : Fin 189 // i ∈ orbitCells k} × unipotentSubgroup) :
    (cellEquiv k z).1 = (correctedQuotientRepresentative z.1.1)⁻¹ * z.2.1 := rfl

set_option maxRecDepth 100000 in
theorem fiber_card_length : ∀ k : Fin 12,
    (orbitCells k).card = 2 ^ correctedLength (orbitWeyl k) := by
  decide

noncomputable def inverseCellEquiv (w : SplitOctF2Aut) :
    concreteBruhatCell w ≃ concreteBruhatCell w⁻¹ where
  toFun g := ⟨g.1⁻¹, inverse_mem_cell g.2⟩
  invFun g := ⟨g.1⁻¹, by simpa only [inv_inv] using inverse_mem_cell g.2⟩
  left_inv g := Subtype.ext (inv_inv g.1)
  right_inv g := Subtype.ext (inv_inv g.1)

theorem cell_card (k : Fin 12) :
    Nat.card (concreteBruhatCell (orbitWeylRepresentative k)) =
      64 * 2 ^ correctedLength (orbitWeyl k) := by
  rw [Nat.card_congr (inverseCellEquiv _), ← Nat.card_congr (cellEquiv k),
    Nat.card_prod, unipotentSubgroup_card]
  have hf : Nat.card {i : Fin 189 // i ∈ orbitCells k} = (orbitCells k).card := by
    simp [Nat.card_eq_fintype_card]
  rw [hf, fiber_card_length, Nat.mul_comm]

theorem weyl_cell_card (p : WeylG2) :
    Nat.card (concreteBruhatCell (weylNF p.1 p.2)) =
      64 * 2 ^ correctedLength p := by
  obtain ⟨k, rfl⟩ := G2TitsRepresentativeInjectivity.orbitWeyl_bijective.2 p
  exact cell_card k

end InfoGeometry.Algebra.Zorn.G2CellwiseCoordinates
