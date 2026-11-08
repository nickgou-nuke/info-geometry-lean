import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2FactorizationFromQuotient

namespace InfoGeometry.Algebra.Zorn.G2FlagCell2SignedWitness

open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2FactorizationFromQuotient
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
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
      simp only [signedWord]
      exact Subgroup.mul_mem _ (signedTerm_mem_unipotent x) ih

@[simp] theorem signedWord_nil :
    signedWord [] = 1 := by
  rfl

@[simp] theorem signedWord_cons
    (x : Fin 6 × Bool) (l : List (Fin 6 × Bool)) :
    signedWord (x :: l) = signedTerm x * signedWord l := by
  rfl

theorem signedWord_append
    (l₁ l₂ : List (Fin 6 × Bool)) :
    signedWord (l₁ ++ l₂) = signedWord l₁ * signedWord l₂ := by
  induction l₁ with
  | nil => simp [signedWord]
  | cons x xs ih =>
      simp only [List.cons_append, signedWord_cons, ih, mul_assoc]

theorem signedWord_append_mem_unipotent
    (l₁ l₂ : List (Fin 6 × Bool)) :
    signedWord (l₁ ++ l₂) ∈ unipotentSubgroup := by
  exact signedWord_mem_unipotent _

theorem signedTerm_inv (x : Fin 6 × Bool) :
    (signedTerm x)⁻¹ = signedTerm (x.1, !x.2) := by
  rcases x with ⟨i, b⟩
  cases b <;> simp [signedTerm]

theorem signedWord_reverse_inv
    (l : List (Fin 6 × Bool)) :
    signedWord (l.reverse.map (fun x => (x.1, !x.2))) =
      (signedWord l)⁻¹ := by
  induction l with
  | nil => simp [signedWord]
  | cons x xs ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, signedWord_append, signedWord_cons,
        signedWord_nil, ih, mul_inv_rev, signedTerm_inv]
      simp

theorem signedWord_reverse_inv_mem_unipotent
    (l : List (Fin 6 × Bool)) :
    signedWord (l.reverse.map (fun x => (x.1, !x.2))) ∈
      unipotentSubgroup := by
  rw [signedWord_reverse_inv]
  exact unipotentSubgroup.inv_mem (signedWord_mem_unipotent l)

/-! A proof-producing interface for cell `2`.  The matrix residual is the
only certificate input; the quotient witness and subgroup membership are
derived internally. -/

structure CellTwoWordCertificate where
  word : Fin 189 → List (Fin 6 × Bool)
  residual : ∀ (i : Fin 189), i ∈ orbitCells 2 →
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative i)⁻¹ *
        (signedWord (word i) *
          weylNF (orbitWeyl 2).1 (orbitWeyl 2).2)) =
        autMatrix (G2TwoSylowSubgroup.pcWord e)

theorem hcell_two_signed_of_certificate
    (C : CellTwoWordCertificate) (i : Fin 189)
    (hi : i ∈ orbitCells 2) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 2).1 (orbitWeyl 2).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  refine ⟨signedWord (C.word i), signedWord_mem_unipotent _, ?_⟩
  apply quotientRepresentative_eq_left_smul_of_pc_matrix
  exact C.residual i hi

theorem exact_factorization_exists_cell_two_of_certificate
    (C : CellTwoWordCertificate) (i : Fin 189)
    (hi : i ∈ orbitCells 2) :
    ∃ b u : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧ u ∈ unipotentSubgroup ∧
        flagRepresentative i =
          b * weylNF (orbitWeyl 2).1 (orbitWeyl 2).2 * u := by
  let b := signedWord (C.word i)
  have hb : b ∈ unipotentSubgroup := signedWord_mem_unipotent _
  have hq : quotientRepresentative i =
      b • (QuotientGroup.mk
        (weylNF (orbitWeyl 2).1 (orbitWeyl 2).2) :
          G2FlagCellQuotientWitness.CarrierQuotient) := by
    apply quotientRepresentative_eq_left_smul_of_pc_matrix
    exact C.residual i hi
  obtain ⟨u, hu, hfac⟩ := factorization_of_quotient_witness i b
    (weylNF (orbitWeyl 2).1 (orbitWeyl 2).2) hq
  exact ⟨b, u, hb, hu, hfac⟩

end InfoGeometry.Algebra.Zorn.G2FlagCell2SignedWitness
