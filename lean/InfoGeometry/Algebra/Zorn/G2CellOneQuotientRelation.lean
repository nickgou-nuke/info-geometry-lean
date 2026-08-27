import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellOne
import InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
import InfoGeometry.Algebra.Zorn.G2GapResidualPairCellAssembly
import InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe

/-!
# Exact quotient collision and 2-coset structure of Cell 1 in G₂(2)

This module formalizes the complete quotient structure of Cell 1 (`{24, 45, 73, 178}`):
1. Representatives 24 and 45 collide in `G ⧸ U₆` via right factor `(pcGenerator 1)⁻¹`.
2. Representatives 73 and 178 collide in `G ⧸ U₆` via right PC factor.
3. The pairs `{24, 45}` and `{73, 178}` are strictly separated.
4. Consequently, the 4 elements of Cell 1 project onto exactly 2 distinct cosets in `G ⧸ U₆`.
-/

namespace InfoGeometry.Algebra.Zorn.G2CellOneQuotientRelation

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellOne
open InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
open InfoGeometry.Algebra.Zorn.G2GapResidualPairCellAssembly
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- The exact right unipotent factor relating flag representatives 24 and 45. -/
theorem flagRepresentative_45_eq_24_mul_pc1 :
    flagRepresentative (45 : Fin 189) =
      flagRepresentative (24 : Fin 189) * (pcGenerator 1)⁻¹ := by
  apply autMatrix_injective
  decide

/-- Flag representatives 24 and 45 represent the same coset in `G ⧸ U₆`. -/
theorem quotientRepresentative_24_eq_45 :
    quotientRepresentative (24 : Fin 189) =
      quotientRepresentative (45 : Fin 189) := by
  have hpc1 : (pcGenerator 1)⁻¹ ∈ unipotentSubgroup := by
    rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
    apply Subgroup.inv_mem
    apply Subgroup.subset_closure
    exact ⟨1, rfl⟩
  exact quotientRepresentative_eq_of_right_factor 24 45 (pcGenerator 1)⁻¹ hpc1
    flagRepresentative_45_eq_24_mul_pc1

set_option maxRecDepth 100000 in
/-- Flag representatives 73 and 178 represent the same coset in `G ⧸ U₆`. -/
theorem quotientRepresentative_73_eq_178 :
    quotientRepresentative (73 : Fin 189) =
      quotientRepresentative (178 : Fin 189) := by
  obtain ⟨e, he⟩ : ∃ e : G2TwoSylowSubgroup.PCWordExp,
      autMatrix ((flagRepresentative 73)⁻¹ * flagRepresentative 178) =
        autMatrix (G2TwoSylowSubgroup.pcWord e) := by
    decide
  exact quotientRepresentative_eq_of_pc_matrix_factor 73 178 e he

/-- The Bruhat residual pair coordinates of 24 and 45 are strictly distinct. -/
theorem gapResidualPair_24_ne_45 :
    gapResidualPair 1 (24 : Fin 189) ≠ gapResidualPair 1 (45 : Fin 189) := by
  intro h
  have h24 : (24 : Fin 189) ∈ orbitCells 1 := by decide
  have h45 : (45 : Fin 189) ∈ orbitCells 1 := by decide
  have hinj := gapResidualPair_injective_on_cell 1 24 45 h24 h45 h
  revert hinj
  decide

/-- The Bruhat residual pair coordinates of 73 and 178 are strictly distinct. -/
theorem gapResidualPair_73_ne_178 :
    gapResidualPair 1 (73 : Fin 189) ≠ gapResidualPair 1 (178 : Fin 189) := by
  intro h
  have h73 : (73 : Fin 189) ∈ orbitCells 1 := by decide
  have h178 : (178 : Fin 189) ∈ orbitCells 1 := by decide
  have hinj := gapResidualPair_injective_on_cell 1 73 178 h73 h178 h
  revert hinj
  decide

/-- THEOREM: Naive quotient injectivity on Cell 1 fails due to the exact
    right unipotent translation `g₄₅ = g₂₄ * (pcGenerator 1)⁻¹`. -/
theorem cell_one_quotient_collision :
    quotientRepresentative (24 : Fin 189) = quotientRepresentative (45 : Fin 189) ∧
    gapResidualPair 1 (24 : Fin 189) ≠ gapResidualPair 1 (45 : Fin 189) :=
  ⟨quotientRepresentative_24_eq_45, gapResidualPair_24_ne_45⟩

set_option maxRecDepth 100000 in
/-- A constant-size matrix separator for the `24/73` cross-pair at `(3, 3)`. -/
theorem matrix_entry_24_73_separates_pc_words :
    ∀ e : PCWordExp,
      autMatrix ((flagRepresentative 24)⁻¹ * flagRepresentative 73) 3 3 ≠
        autMatrix (G2TwoSylowSubgroup.pcWord e) 3 3 := by
  decide

set_option maxRecDepth 100000 in
/-- A constant-size matrix separator for the `24/178` cross-pair at `(6, 5)`. -/
theorem matrix_entry_24_178_separates_pc_words :
    ∀ e : PCWordExp,
      autMatrix ((flagRepresentative 24)⁻¹ * flagRepresentative 178) 6 5 ≠
        autMatrix (G2TwoSylowSubgroup.pcWord e) 6 5 := by
  decide

set_option maxRecDepth 100000 in
/-- Representatives 24 and 73 are strictly distinct in `G ⧸ U₆`. -/
theorem quotientRepresentative_24_ne_73 :
    quotientRepresentative (24 : Fin 189) ≠ quotientRepresentative (73 : Fin 189) := by
  intro hquot
  obtain ⟨e, he⟩ := quotient_equality_has_pc_factor 24 73 hquot
  exact matrix_entry_24_73_separates_pc_words e
    (congrArg (fun M => M 3 3) he)

set_option maxRecDepth 100000 in
/-- Representatives 24 and 178 are strictly distinct in `G ⧸ U₆`. -/
theorem quotientRepresentative_24_ne_178 :
    quotientRepresentative (24 : Fin 189) ≠ quotientRepresentative (178 : Fin 189) := by
  intro hquot
  obtain ⟨e, he⟩ := quotient_equality_has_pc_factor 24 178 hquot
  exact matrix_entry_24_178_separates_pc_words e
    (congrArg (fun M => M 6 5) he)

/-- Representatives 45 and 73 are strictly distinct in `G ⧸ U₆`. -/
theorem quotientRepresentative_45_ne_73 :
    quotientRepresentative (45 : Fin 189) ≠ quotientRepresentative (73 : Fin 189) := by
  intro h
  rw [← quotientRepresentative_24_eq_45] at h
  exact quotientRepresentative_24_ne_73 h

/-- Representatives 45 and 178 are strictly distinct in `G ⧸ U₆`. -/
theorem quotientRepresentative_45_ne_178 :
    quotientRepresentative (45 : Fin 189) ≠ quotientRepresentative (178 : Fin 189) := by
  intro h
  rw [← quotientRepresentative_24_eq_45] at h
  exact quotientRepresentative_24_ne_178 h

/-- THEOREM: Complete 6-pair classification for Cell 1:
    - (24, 45) and (73, 178) are the two exact collisions in `G ⧸ U₆`.
    - All cross-pair comparisons are strictly separated. -/
theorem cell_one_full_six_pair_classification :
    quotientRepresentative (24 : Fin 189) = quotientRepresentative (45 : Fin 189) ∧
    quotientRepresentative (73 : Fin 189) = quotientRepresentative (178 : Fin 189) ∧
    quotientRepresentative (24 : Fin 189) ≠ quotientRepresentative (73 : Fin 189) ∧
    quotientRepresentative (24 : Fin 189) ≠ quotientRepresentative (178 : Fin 189) ∧
    quotientRepresentative (45 : Fin 189) ≠ quotientRepresentative (73 : Fin 189) ∧
    quotientRepresentative (45 : Fin 189) ≠ quotientRepresentative (178 : Fin 189) :=
  ⟨quotientRepresentative_24_eq_45,
   quotientRepresentative_73_eq_178,
   quotientRepresentative_24_ne_73,
   quotientRepresentative_24_ne_178,
   quotientRepresentative_45_ne_73,
   quotientRepresentative_45_ne_178⟩

/-- THEOREM: The 4 elements of Cell 1 project onto exactly the 2 distinct
    cosets `{[24] = [45], [73] = [178]}` in `G ⧸ U₆`. -/
theorem cell_one_quotient_subset_two_values (i : Fin 189) (hi : i ∈ orbitCells 1) :
    quotientRepresentative i = quotientRepresentative 24 ∨
    quotientRepresentative i = quotientRepresentative 73 := by
  simp [orbitCells, flagCells] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl quotientRepresentative_24_eq_45.symm
  · exact Or.inr quotientRepresentative_73_eq_178.symm
  · exact Or.inr rfl

/-! The preceding range theorem and the four pairwise comparisons give the
    exact equality relation on this cell.  This is deliberately scoped to
    `orbitCells 1`; it is not a statement about the whole quotient table. -/
set_option linter.unusedSimpArgs false in
theorem cell_one_quotient_eq_iff_same_pair
    {i j : Fin 189}
    (hi : i ∈ orbitCells 1) (hj : j ∈ orbitCells 1) :
    quotientRepresentative i = quotientRepresentative j ↔
      (i = 24 ∧ j = 24) ∨ (i = 24 ∧ j = 45) ∨
      (i = 45 ∧ j = 24) ∨ (i = 45 ∧ j = 45) ∨
      (i = 73 ∧ j = 73) ∨ (i = 73 ∧ j = 178) ∨
      (i = 178 ∧ j = 73) ∨ (i = 178 ∧ j = 178) := by
  constructor
  · intro hij
    have hi' : i = 24 ∨ i = 45 ∨ i = 178 ∨ i = 73 := by
      simpa [orbitCells, flagCells] using hi
    have hj' : j = 24 ∨ j = 45 ∨ j = 178 ∨ j = 73 := by
      simpa [orbitCells, flagCells] using hj
    rcases hi' with rfl | rfl | rfl | rfl <;>
      rcases hj' with rfl | rfl | rfl | rfl <;>
      simp_all [quotientRepresentative_24_eq_45,
        quotientRepresentative_73_eq_178,
        quotientRepresentative_24_ne_73,
        quotientRepresentative_24_ne_178,
        quotientRepresentative_45_ne_73,
        quotientRepresentative_45_ne_178]
    all_goals exact quotientRepresentative_45_ne_178 hij.symm
  · intro h
    rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact quotientRepresentative_24_eq_45
    · exact quotientRepresentative_24_eq_45.symm
    · rfl
    · rfl
    · exact quotientRepresentative_73_eq_178
    · exact quotientRepresentative_73_eq_178.symm
    · rfl

set_option maxRecDepth 100000 in
theorem cell_one_quotient_image_eq_two_values :
    Set.range (fun i : {i : Fin 189 // i ∈ orbitCells 1} =>
      quotientRepresentative i.1) =
      {quotientRepresentative (24 : Fin 189),
       quotientRepresentative (73 : Fin 189)} := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    rcases cell_one_quotient_subset_two_values i.1 i.2 with h | h
    · exact (Set.mem_insert_iff.mpr (Or.inl h))
    · exact (Set.mem_insert_iff.mpr (Or.inr h))
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact ⟨⟨24, by decide⟩, rfl⟩
    · exact ⟨⟨73, by decide⟩, rfl⟩

set_option maxRecDepth 100000 in
theorem cell_one_quotient_image_card :
    Nat.card (Set.range (fun i : {i : Fin 189 // i ∈ orbitCells 1} =>
      quotientRepresentative i.1)) = 2 := by
  rw [cell_one_quotient_image_eq_two_values]
  rw [Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem]
  · simp
  · intro h
    exact quotientRepresentative_24_ne_73 h

end InfoGeometry.Algebra.Zorn.G2CellOneQuotientRelation
