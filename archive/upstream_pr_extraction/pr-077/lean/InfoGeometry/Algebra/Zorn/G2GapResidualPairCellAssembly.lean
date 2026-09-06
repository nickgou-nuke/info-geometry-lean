import InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellZero
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellOne
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTwo
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellThree
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellFour
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellFive
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellSix
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellSeven
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellEight
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellNine
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTen
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellEleven
import InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity
import InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe

namespace InfoGeometry.Algebra.Zorn.G2GapResidualPairCellAssembly

open InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity
open InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe

set_option maxRecDepth 100000 in
theorem gapResidualPair_injective_on_cell :
    ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      gapResidualPair k i = gapResidualPair k j → i = j := by
  intro k i j hi hj h
  fin_cases k
  · exact G2ResidualPairCoordinateCellZero.residualPair_injective_on_cell_zero
      i j hi hj h
  · exact G2ResidualPairCoordinateCellOne.residualPair_injective_on_cell_one
      i j hi hj h
  · exact G2ResidualPairCoordinateCellTwo.residualPair_injective_on_cell_two
      i j hi hj h
  · exact G2ResidualPairCoordinateCellThree.residualPair_injective_on_cell_three
      i j hi hj h
  · exact G2ResidualPairCoordinateCellFour.residualPair_injective_on_cell_four
      i j hi hj h
  · exact G2ResidualPairCoordinateCellFive.residualPair_injective_on_cell_five
      i j hi hj h
  · exact G2ResidualPairCoordinateCellSix.residualPair_injective_on_cell_six
      i j hi hj h
  · exact G2ResidualPairCoordinateCellSeven.residualPair_injective_on_cell_seven
      i j hi hj h
  · exact G2ResidualPairCoordinateCellEight.residualPair_injective_on_cell_eight
      i j hi hj h
  · exact G2ResidualPairCoordinateCellNine.residualPair_injective_on_cell_nine
      i j hi hj h
  · exact G2ResidualPairCoordinateCellTen.residualPair_injective_on_cell_ten
      i j hi hj h
  · exact G2ResidualPairCoordinateCellEleven.residualPair_injective_on_cell_eleven
      i j hi hj h

theorem gapResidualPair_alignment_on_cell_zero
    (i j : Fin 189)
    (hi : i ∈ orbitCells 0) (hj : j ∈ orbitCells 0)
    (_hq : quotientRepresentative i = quotientRepresentative j) :
    gapResidualPair 0 i = gapResidualPair 0 j := by
  have hi0 : i = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hi
  have hj0 : j = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hj
  have hij : i = j := hi0.trans hj0.symm
  rw [hij]

theorem quotientRepresentative_injective_of_all_gapResidualPair_alignment
    (halign : ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j) :
    Function.Injective quotientRepresentative := by
  exact quotientRepresentative_injective_of_gapResidualPair_alignment
    gapResidualPair_injective_on_cell halign

theorem quotientRepresentative_injective_of_distinct_gapResidualPair_alignment
    (halignDistinct : ∀ (i j : Fin 189), i ≠ j →
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j) :
    Function.Injective quotientRepresentative := by
  apply quotientRepresentative_injective_of_all_gapResidualPair_alignment
  intro i j hij
  by_cases hne : i = j
  · subst j
    have hi : i ∈ Finset.univ.biUnion orbitCells := by
      rw [orbitCells_partition]
      exact Finset.mem_univ i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hik⟩ := hi
    exact ⟨k, hik, hik, rfl⟩
  · exact halignDistinct i j hne hij

theorem gapResidualPair_diagonal_alignment (i : Fin 189) :
    ∃ k : Fin 12,
      i ∈ orbitCells k ∧ i ∈ orbitCells k ∧
        gapResidualPair k i = gapResidualPair k i := by
  have hi : i ∈ Finset.univ.biUnion orbitCells := by
    rw [orbitCells_partition]
    exact Finset.mem_univ i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hi
  obtain ⟨k, hik⟩ := hi
  exact ⟨k, hik, hik, rfl⟩

theorem gapResidualPair_alignment_iff_distinct
    (halignDistinct : ∀ (i j : Fin 189), i ≠ j →
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j := by
  intro i j hij
  by_cases hne : i = j
  · subst j
    exact gapResidualPair_diagonal_alignment i
  · exact halignDistinct i j hne hij

noncomputable def quotientRepresentativeEquiv_of_all_gapResidualPair_alignment
    (halign : ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j)
    (hG : Nat.card
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut =
        12096) :
    Fin 189 ≃ InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient := by
  apply Equiv.ofBijective quotientRepresentative
  refine ⟨quotientRepresentative_injective_of_all_gapResidualPair_alignment halign, ?_⟩
  exact quotientRepresentative_surjective_of_ambient_order
    (quotientRepresentative_injective_of_all_gapResidualPair_alignment halign) hG

end InfoGeometry.Algebra.Zorn.G2GapResidualPairCellAssembly
