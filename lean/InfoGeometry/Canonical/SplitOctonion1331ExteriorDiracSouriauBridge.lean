import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge

/-! Native exterior/Dirac--Souriau readout for the established `1+3+3+1`
Peirce ordering.  This file introduces no new carrier or multiplication law. -/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge

abbrev CZ := ZornMatrix ℝ

theorem exterior3BasisSigma_apply
    (k : ℕ) (s : Set.powersetCard (Fin 3) k) :
    exterior3BasisSigma ⟨k, s⟩ = degreeBasis3 k s := by
  unfold exterior3BasisSigma
  exact congrFun
    ((DirectSum.Decomposition.isInternal
      (ℳ := fun k : ℕ => ⋀[ℝ]^k V3)).collectedBasis_coe
      (fun k : ℕ => degreeBasis3 k)) ⟨k, s⟩

theorem exterior3PeirceBasis_apply (i : Fin 8) :
    exterior3PeirceBasis i = exterior3BasisFinset (peirceSubset i) := by
  rw [exterior3PeirceBasis, Module.Basis.reindex_apply]
  rfl

theorem exterior3BasisFinset_apply (s : Finset (Fin 3)) :
    exterior3BasisFinset s = degreeBasis3 s.card ⟨s, rfl⟩ := by
  unfold exterior3BasisFinset
  rw [Module.Basis.reindex_apply]
  exact exterior3BasisSigma_apply s.card ⟨s, rfl⟩

theorem degreeBasis3_apply
    (k : ℕ) (s : Set.powersetCard (Fin 3) k) :
    degreeBasis3 k s = ExteriorAlgebra.ιMulti_family ℝ k vBasis3 s := by
  simpa [degreeBasis3] using
    (exteriorPower.basis_apply (n := k) (b := vBasis3) (s := s))

theorem exterior3PeirceBasis_ιMulti (i : Fin 8) :
    exterior3PeirceBasis i =
      ExteriorAlgebra.ιMulti_family ℝ (peirceSubset i).card
        vBasis3 ⟨peirceSubset i, by simp⟩ := by
  rw [exterior3PeirceBasis_apply, exterior3BasisFinset_apply,
    degreeBasis3_apply]

theorem exterior3PeirceBasis_mem_exteriorPower (i : Fin 8) :
    exterior3PeirceBasis i ∈
      (⋀[ℝ]^(peirceSubset i).card (Fin 3 → ℝ)) := by
  rw [exterior3PeirceBasis_ιMulti]
  apply ExteriorAlgebra.ιMulti_range
  exact ⟨vBasis3 ∘ (Set.powersetCard.ofFinEmbEquiv.symm
      ⟨peirceSubset i, by simp⟩), rfl⟩

theorem degreeBasis3_listProduct (k : ℕ)
    (s : Set.powersetCard (Fin 3) k) :
    degreeBasis3 k s =
      ExteriorAlgebra.ιMulti ℝ k
        (vBasis3 ∘ (Set.powersetCard.ofFinEmbEquiv.symm s)) := by
  rw [degreeBasis3_apply]

theorem degreeBasis3_zero (s : Set.powersetCard (Fin 3) 0) :
    degreeBasis3 0 s = (1 : Exterior3) := by
  rw [degreeBasis3_listProduct, ExteriorAlgebra.ιMulti_apply]
  simp

theorem orderEmbOfFin_singleton_zero (i : Fin 3) :
    (({i} : Finset (Fin 3)).orderEmbOfFin (k := 1) (by simp) 0) = i := by
  apply Finset.mem_singleton.mp
  exact Finset.orderEmbOfFin_mem ({i} : Finset (Fin 3)) (by simp) 0

def exteriorDegree1331 : Fin 8 → ℕ
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1
  | 4 => 3 | 5 => 2 | 6 => 2 | 7 => 2

theorem exteriorDegree1331_eq_card_peirceSubset (i : Fin 8) :
    exteriorDegree1331 i = (peirceSubset i).card := by
  fin_cases i <;> rfl

theorem exterior_basis_1331_packet (i : Fin 8) :
    exterior3CircularPeirceEquiv (exterior3PeirceBasis i) =
        circularPeirceBasis i ∧
      exteriorDegree1331 i = (peirceSubset i).card := by
  exact ⟨exterior3CircularPeirceEquiv_basis i,
    exteriorDegree1331_eq_card_peirceSubset i⟩

theorem exterior3PeirceBasis_zero :
    exterior3PeirceBasis 0 = (1 : Exterior3) := by
  rw [exterior3PeirceBasis_apply, peirceSubset_scalarPlus,
    exterior3BasisFinset_apply]
  exact degreeBasis3_zero _

theorem exteriorWedge3_basis_zero (i : Fin 3) :
    exteriorWedge3 (Pi.single i 1) (exterior3PeirceBasis 0) =
      exterior3PeirceBasis ⟨i.val + 1, by omega⟩ := by
  rw [exterior3PeirceBasis_zero]
  rw [exteriorWedge3_apply, mul_one]
  rw [exterior3PeirceBasis_apply, peirceSubset_rootPlus]
  rw [exterior3BasisFinset_apply, degreeBasis3_apply]
  fin_cases i <;>
    simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
      vBasis3, Pi.basisFun, Set.powersetCard.ofFinEmbEquiv_symm_apply] <;>
    congr 1 <;>
    exact (orderEmbOfFin_singleton_zero _).symm

theorem toDiracSouriauSector_eq_1331_entries (z1 z2 : CZ) :
    toDiracSouriauSector z1 z2 =
      !![(degreeZero z1).a,
          dot (degreeOne z1).x (degreeTwo z2).y;
         dot (degreeTwo z1).y (degreeOne z2).x,
          (degreeThree z2).b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toDiracSouriauSector, degreeZero_apply, degreeThree_apply,
      degreeOne, degreeTwo, colorProject_apply, anticolorProject_apply]

theorem toDiracSouriauSector_factor_through_1331 (z1 z2 : CZ) :
    toDiracSouriauSector z1 z2 =
      toDiracSouriauSector
        (degreeZero z1 + degreeOne z1 + degreeTwo z1)
        (degreeOne z2 + degreeTwo z2 + degreeThree z2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toDiracSouriauSector, degreeZero_apply, degreeThree_apply,
      degreeOne, degreeTwo, colorProject_apply, anticolorProject_apply,
      dot]

theorem coarseGrain_and_diracSouriau_1331_packet (z1 z2 : CZ) :
    coarseGrain z1 = coarseGrain (degreeZero z1 + degreeThree z1) ∧
    toDiracSouriauSector z1 z2 =
      toDiracSouriauSector
        (degreeZero z1 + degreeOne z1 + degreeTwo z1)
        (degreeOne z2 + degreeTwo z2 + degreeThree z2) := by
  exact ⟨coarseGrain_eq_diagonal_degrees z1,
    toDiracSouriauSector_factor_through_1331 z1 z2⟩

end InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
