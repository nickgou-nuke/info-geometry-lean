import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessRows
import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2FlagQuotientProvenance
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
import InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate
import InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity
import InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity
import InfoGeometry.Algebra.Zorn.G2PCMatrixSeparationBridge
import InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTwo
import InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly

namespace InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessReadback
open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessRows
open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagQuotientProvenance
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity
open InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne

theorem orbitCells_eq_flagCells :
    orbitCells = flagCells := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_gapWitnessMatrixSound
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    gapWitnessMatrixSound k i := by
  change i ∈ flagCells k at hi
  fin_cases k <;>
    simp [flagCells] at hi ⊢ <;>
    aesop

theorem quotientRowWitness_of_gap_witness_rows
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    QuotientRowWitness k i := by
  exact quotientRowWitness_of_all_gapWitness_matrix_sound
    (fun k i hi => all_gapWitnessMatrixSound k i hi) k i hi

theorem all_gapWitnessFactorization
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (gapLeftWitness k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (gapRightWitness k i) := by
  exact gapWitness_group_factorization k i (all_gapWitnessMatrixSound k i hi)

theorem flagRepresentative_mem_concreteBruhatCell
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i ∈
      G2TwoBruhatClassification.concreteBruhatCell
        (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  have hfac := all_gapWitnessFactorization k i hi
  rw [G2TwoBruhatClassification.concreteBruhatCell]
  refine ⟨collect (gapLeftWitness k i), collect (gapRightWitness k i), ?_, ?_, hfac⟩
  · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact gapLeftWitness_mem_unipotentSubgroup k i
  · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact gapRightWitness_mem_unipotentSubgroup k i

theorem quotient_alignment_of_gap_witness_rows
    (hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (hresidual_align : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
          residualWord k i = residualWord k j := by
  exact quotient_alignment_of_cell_separation
    (fun k i hi => flagRepresentative_mem_concreteBruhatCell k i hi)
    hdisj
    hresidual_align

theorem quotientRepresentative_common_cell_of_cell_disjoint
    (hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2))) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k := by
  exact quotient_common_cell_of_cell_separation
    (fun k i hi => flagRepresentative_mem_concreteBruhatCell k i hi)
    hdisj

/-! The row certificate supplies the cell-membership half of quotient
    injectivity.  The remaining coordinate alignment is kept explicit rather
    than inferred from the quotient equality. -/
theorem quotientRepresentative_injective_of_gap_witness_rows
    (hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (halign : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j)
    (hintra : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j) :
    Function.Injective quotientRepresentative := by
  apply quotientRepresentative_injective_of_residual_alignment hintra
  exact quotient_alignment_of_gap_witness_rows hdisj halign

/-! The first nontrivial cell has a native residual-coordinate readback.  This
    local theorem uses it without pretending that the same coordinates are
    faithful on every cell. -/
theorem quotientRepresentative_injective_on_cell_one
    (halign : ∀ (i j : Fin 189),
      i ∈ orbitCells 1 → j ∈ orbitCells 1 →
      quotientRepresentative i = quotientRepresentative j →
      residualWord 1 i = residualWord 1 j) :
    ∀ (i j : Fin 189),
      i ∈ orbitCells 1 → j ∈ orbitCells 1 →
      quotientRepresentative i = quotientRepresentative j → i = j := by
  intro i j hi hj hq
  exact residualWord_injective_on_cell_one i j hi hj
    (halign i j hi hj hq)

theorem quotientRepresentative_injective_on_cell_zero :
    ∀ (i j : Fin 189),
      i ∈ orbitCells 0 → j ∈ orbitCells 0 →
      quotientRepresentative i = quotientRepresentative j → i = j := by
  intro i j hi hj _
  have hi0 : i = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hi
  have hj0 : j = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hj
  exact hi0.trans hj0.symm

/-! The raw residual coordinate is not injective on cell two.  The
    two-sided pair coordinate is the first truthful replacement. -/
theorem quotientRepresentative_injective_on_cell_two_of_pair_alignment
    (halign : ∀ (i j : Fin 189),
      i ∈ orbitCells 2 → j ∈ orbitCells 2 →
      quotientRepresentative i = quotientRepresentative j →
      G2ResidualPairCoordinateCellTwo.residualPair 2 i =
        G2ResidualPairCoordinateCellTwo.residualPair 2 j) :
    ∀ (i j : Fin 189),
      i ∈ orbitCells 2 → j ∈ orbitCells 2 →
      quotientRepresentative i = quotientRepresentative j → i = j := by
  intro i j hi hj hq
  apply G2ResidualPairCoordinateCellTwo.residualPair_injective_on_cell_two i j hi hj
  exact halign i j hi hj hq

theorem gapResidualPair_two_eq_cell_two_residualPair (i : Fin 189) :
    G2GapResidualPairAssembly.gapResidualPair 2 i =
      G2ResidualPairCoordinateCellTwo.residualPair 2 i := by
  rfl

theorem quotientRowWitness_cell_two
    (i : Fin 189) (hi : i ∈ orbitCells 2) :
    QuotientRowWitness 2 i := by
  exact quotientRowWitness_of_gap_witness_rows 2 i hi

theorem orbitEnum_mem_quotientOrbit_cell_two
    (i : Fin 189) (hi : i ∈ orbitCells 2) :
    orbitEnum i ∈
      G2BNPair.quotientOrbit unipotentSubgroup
        (weylNF (orbitWeyl 2).1 (orbitWeyl 2).2) := by
  exact G2TitsRepresentativeInjectivity.quotientOrbit_mem_of_witness
    (quotientRowWitness_cell_two i hi)

theorem quotientRepresentative_injective_of_quotientOrbit_disjoint
    (hsep : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (halign : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j)
    (hintra : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j) :
    Function.Injective quotientRepresentative := by
  have hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2)) := by
    intro k l hkl
    exact concreteBruhatCell_disjoint_of_quotientOrbit_separation _ _ (hsep k l hkl)
  exact quotientRepresentative_injective_of_gap_witness_rows hdisj halign hintra

/-! Native matrix separation is the preferred input form for the preceding
    quotient-separation edge.  Faithfulness and quotient transport are supplied
    by the existing matrix bridge; no ambient enumeration is used. -/
theorem quotientRepresentative_injective_of_matrix_separation
    (hmatrix : ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : G2TwoSylowSubgroup.PCWordExp,
        autMatrix (pcWord c *
          G2QuotientOrbitSeparation.orbitWeylRepresentative l) ≠
          autMatrix (pcWord a *
            G2QuotientOrbitSeparation.orbitWeylRepresentative k *
              pcWord d))
    (halign : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j)
    (hintra : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j) :
    Function.Injective quotientRepresentative := by
  have hsep : ∀ {k l : Fin 12}, k ≠ l →
      Disjoint
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (G2QuotientOrbitSeparation.orbitWeylRepresentative k))
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (G2QuotientOrbitSeparation.orbitWeylRepresentative l)) :=
    G2PCMatrixSeparationBridge.quotientOrbit_disjoint_of_matrix_separation
      hmatrix
  have hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl l).1 (orbitWeyl l).2)) := by
    intro k l hkl
    simpa [G2QuotientOrbitSeparation.orbitWeylRepresentative] using
      hsep hkl
  exact quotientRepresentative_injective_of_quotientOrbit_disjoint
    hdisj
    halign hintra

theorem concreteBruhatCovering_eq_univ_of_gap_witness_rows
    (enum : Fin 189 ≃ G2NativeQuotientRepresentative.CarrierQuotient)
    (henum : ∀ i : Fin 189, enum i = orbitEnum i) :
    G2TwoBruhatClassification.concreteBruhatCovering = Set.univ := by
  apply covering_eq_univ enum orbitWeyl orbitCells
  · intro k i hi
    obtain ⟨b, hb, hq⟩ := quotientRowWitness_of_gap_witness_rows k i hi
    exact ⟨b, hb, (henum i).trans hq⟩
  · exact orbitCells_partition

noncomputable def quotientEnumeration_of_injective_and_ambient_order
    (hinj : Function.Injective quotientRepresentative)
    (hG : Nat.card OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut = 12096) :
    Fin 189 ≃ G2NativeQuotientRepresentative.CarrierQuotient := by
  apply Equiv.ofBijective quotientRepresentative
  exact ⟨hinj, quotientRepresentative_surjective_of_ambient_order hinj hG⟩

theorem concreteBruhatCovering_eq_univ_of_gap_witness_rows_of_injective_and_ambient_order
    (hinj : Function.Injective quotientRepresentative)
    (hG : Nat.card OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut = 12096) :
    G2TwoBruhatClassification.concreteBruhatCovering = Set.univ := by
  let enum := quotientEnumeration_of_injective_and_ambient_order hinj hG
  exact concreteBruhatCovering_eq_univ_of_gap_witness_rows enum (by
    intro i
    change quotientRepresentative i = orbitEnum i
    rfl)

noncomputable def quotientEnumeration_of_gap_witness_rows
    (hsep : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (halign : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j)
    (hintra : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j)
    (hG : Nat.card OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut = 12096) :
    Fin 189 ≃ G2NativeQuotientRepresentative.CarrierQuotient := by
  apply quotientEnumeration_of_injective_and_ambient_order
    (quotientRepresentative_injective_of_quotientOrbit_disjoint hsep halign hintra)
    hG

theorem concreteBruhatCovering_eq_univ_of_gap_witness_rows_and_alignment
    (hsep : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          G2TwoPCSubgroupClosure.unipotentSubgroup
          (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (halign : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j)
    (hintra : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j)
    (hG : Nat.card OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut = 12096) :
    G2TwoBruhatClassification.concreteBruhatCovering = Set.univ := by
  let enum := quotientEnumeration_of_gap_witness_rows hsep halign hintra hG
  exact concreteBruhatCovering_eq_univ_of_gap_witness_rows enum (by
    intro i
    change quotientRepresentative i = orbitEnum i
    rfl)

end InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly
