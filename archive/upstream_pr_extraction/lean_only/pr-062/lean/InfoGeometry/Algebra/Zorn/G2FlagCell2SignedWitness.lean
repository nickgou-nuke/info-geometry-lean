import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

namespace InfoGeometry.Algebra.Zorn.G2FlagCell2SignedWitness

open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def signedTerm : Fin 6 × Bool → SplitOctF2Aut :=
  fun x => if x.2 then pcGenerator x.1 else (pcGenerator x.1)⁻¹

def signedWord : List (Fin 6 × Bool) → SplitOctF2Aut :=
  List.prod ∘ List.map signedTerm

theorem signedTerm_mem_unipotent (x : Fin 6 × Bool) :
    signedTerm x ∈ unipotentSubgroup := by
  rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
  dsimp [signedTerm]
  split_ifs
  · exact Subgroup.subset_closure ⟨x.1, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨x.1, rfl⟩)

theorem signedWord_mem_unipotent (l : List (Fin 6 × Bool)) :
    signedWord l ∈ unipotentSubgroup := by
  induction l with
  | nil => simp [signedWord, unipotentSubgroup]
  | cons x xs ih =>
      simp only [signedWord, List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ (signedTerm_mem_unipotent x) ih

def cell2Left : Fin 189 → List (Fin 6 × Bool)
  | 3 => []
  | 57 => [(1, true), (0, true), (3, true)]
  | 185 => [(3, true), (2, true)]
  | 83 => [(4, true), (3, true)]
  | 96 => [(5, true)]
  | 173 => [(2, true), (1, true)]
  | 12 => [(3, true), (1, true)]
  | 122 => [(4, true), (1, true)]
  | 170 => [(2, false), (3, true)]
  | 175 => [(4, true), (2, true)]
  | 55 => [(1, true), (4, true)]
  | 167 => [(0, true), (4, true), (0, true), (2, true)]
  | 49 => [(5, true), (4, true), (3, true)]
  | 106 => [(2, false), (1, true)]
  | 79 => [(4, true), (0, true), (1, true)]
  | 163 => [(4, true), (0, true), (1, false)]
  | _ => []

set_option maxRecDepth 100000 in
theorem hcell_two_signed (i : Fin 189) (hi : i ∈ orbitCells 2) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk (weylNF (orbitWeyl 2).1 (orbitWeyl 2).2) :
            CarrierQuotient) := by
  have hi' : i = 3 ∨ i = 57 ∨ i = 185 ∨ i = 83 ∨ i = 96 ∨
      i = 173 ∨ i = 12 ∨ i = 122 ∨ i = 170 ∨ i = 175 ∨
      i = 55 ∨ i = 167 ∨ i = 49 ∨ i = 106 ∨ i = 79 ∨ i = 163 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with h3 | h57 | h185 | h83 | h96 | h173 | h12 | h122 |
      h170 | h175 | h55 | h167 | h49 | h106 | h79 | h163
  all_goals
    refine ⟨signedWord (cell2Left i), signedWord_mem_unipotent _, ?_⟩
    apply quotientRepresentative_eq_left_smul_of_pc_matrix
    subst i
    decide

end InfoGeometry.Algebra.Zorn.G2FlagCell2SignedWitness
