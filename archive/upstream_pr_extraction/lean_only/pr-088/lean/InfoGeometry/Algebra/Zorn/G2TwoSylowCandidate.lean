import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup

namespace InfoGeometry.Algebra.Zorn.G2TwoSylowCandidate

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl

def sylowBasis : Fin 5 → Fin 7 → SplitOctF2
  | 0 => ![⟨false, true, false, false, false, false, false, true⟩,
           ⟨false, false, false, false, false, false, false, true⟩,
           ⟨false, false, false, false, false, false, true, false⟩,
           ⟨false, false, false, false, false, true, false, false⟩,
           ⟨false, false, false, false, true, false, false, false⟩,
           ⟨false, false, false, true, false, false, false, false⟩,
           ⟨false, false, true, false, false, false, false, false⟩]
  | 1 => ![⟨false, true, false, false, false, false, false, true⟩,
           ⟨false, false, false, false, false, false, false, true⟩,
           ⟨false, false, false, false, false, false, true, true⟩,
           ⟨false, false, false, false, false, true, true, true⟩,
           ⟨false, false, false, false, true, false, false, true⟩,
           ⟨false, false, true, true, false, false, false, false⟩,
           ⟨false, false, true, false, false, false, false, false⟩]
  | 2 => ![⟨true, true, true, false, false, false, false, true⟩,
           ⟨true, false, true, false, false, false, false, true⟩,
           ⟨false, false, false, false, false, false, false, true⟩,
           ⟨false, false, true, false, true, false, false, true⟩,
           ⟨true, true, false, true, false, true, true, true⟩,
           ⟨true, true, false, false, true, true, false, true⟩,
           ⟨false, false, true, false, false, false, false, false⟩]
  | 3 => ![⟨true, false, false, false, false, false, false, false⟩,
           ⟨false, false, false, false, true, false, false, false⟩,
           ⟨false, false, false, true, false, false, false, false⟩,
           ⟨false, false, false, true, true, false, false, false⟩,
           ⟨false, false, false, false, false, true, false, false⟩,
           ⟨false, false, false, false, false, false, true, true⟩,
           ⟨false, false, false, false, false, false, false, true⟩]
  | 4 => ![⟨true, false, false, false, false, false, false, true⟩,
           ⟨false, false, false, false, true, false, false, true⟩,
           ⟨false, false, false, true, false, false, false, false⟩,
           ⟨true, true, false, false, true, false, false, true⟩,
           ⟨false, false, false, true, false, true, false, false⟩,
           ⟨false, false, true, false, false, true, false, false⟩,
           ⟨false, false, false, false, false, false, false, true⟩]

noncomputable def sylowGenerator (i : Fin 5)
    (h : admissibleBasis7 (sylowBasis i)) : SplitOctF2Aut :=
  admissibleBasis7_to_aut (sylowBasis i) h

@[simp] theorem sylowGenerator_on_basis7 (i : Fin 5)
    (h : admissibleBasis7 (sylowBasis i)) (j : Fin 7) :
    (sylowGenerator i h).1 (basis7 j) = sylowBasis i j := by
  fin_cases j
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 0) = _
    rw [extendBasisMap_basis]
    rfl
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 2) = _
    rw [extendBasisMap_basis]
    rfl
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 3) = _
    rw [extendBasisMap_basis]
    rfl
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 4) = _
    rw [extendBasisMap_basis]
    rfl
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 5) = _
    rw [extendBasisMap_basis]
    rfl
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 6) = _
    rw [extendBasisMap_basis]
    rfl
  · change extendBasisMap (basis8From7 (sylowBasis i)) (basis8 7) = _
    rw [extendBasisMap_basis]
    rfl

theorem sylowGenerator_ne_one (i : Fin 5)
    (h : admissibleBasis7 (sylowBasis i)) :
    sylowGenerator i h ≠ (1 : SplitOctF2Aut) := by
  intro hi
  fin_cases i
  · have hj := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) hi
    change (sylowGenerator 0 h).1 (basis7 0) =
      (1 : SplitOctF2Aut).1 (basis7 0) at hj
    rw [sylowGenerator_on_basis7] at hj
    change sylowBasis 0 0 = ePlus at hj
    have hy := congrArg (fun z : SplitOctF2 => z.y2) hj
    simp [sylowBasis, ePlus] at hy
  · have hj := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) hi
    change (sylowGenerator 1 h).1 (basis7 0) =
      (1 : SplitOctF2Aut).1 (basis7 0) at hj
    rw [sylowGenerator_on_basis7] at hj
    change sylowBasis 1 0 = ePlus at hj
    have hy := congrArg (fun z : SplitOctF2 => z.y2) hj
    simp [sylowBasis, ePlus] at hy
  · have hj := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) hi
    change (sylowGenerator 2 h).1 (basis7 0) =
      (1 : SplitOctF2Aut).1 (basis7 0) at hj
    rw [sylowGenerator_on_basis7] at hj
    change sylowBasis 2 0 = ePlus at hj
    have hy := congrArg (fun z : SplitOctF2 => z.y2) hj
    simp [sylowBasis, ePlus] at hy
  · have hj := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 3)) hi
    change (sylowGenerator 3 h).1 (basis7 3) =
      (1 : SplitOctF2Aut).1 (basis7 3) at hj
    rw [sylowGenerator_on_basis7] at hj
    change sylowBasis 3 3 = up2 at hj
    have hy := congrArg (fun z : SplitOctF2 => z.x1) hj
    simp [sylowBasis, up2] at hy
  · have hj := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) hi
    change (sylowGenerator 4 h).1 (basis7 0) =
      (1 : SplitOctF2Aut).1 (basis7 0) at hj
    rw [sylowGenerator_on_basis7] at hj
    change sylowBasis 4 0 = ePlus at hj
    have hy := congrArg (fun z : SplitOctF2 => z.y2) hj
    simp [sylowBasis, ePlus] at hy

theorem sylowGenerator_injective
    (h : ∀ i : Fin 5, admissibleBasis7 (sylowBasis i)) :
    Function.Injective (fun i : Fin 5 => sylowGenerator i (h i)) := by
  intro i j hij
  have he := congrArg (fun f : SplitOctF2Aut =>
      (f.1 (basis7 0), f.1 (basis7 2), f.1 (basis7 3),
        f.1 (basis7 4), f.1 (basis7 5), f.1 (basis7 6))) hij
  change
    ((sylowGenerator i (h i)).1 (basis7 0),
      (sylowGenerator i (h i)).1 (basis7 2),
      (sylowGenerator i (h i)).1 (basis7 3),
      (sylowGenerator i (h i)).1 (basis7 4),
      (sylowGenerator i (h i)).1 (basis7 5),
      (sylowGenerator i (h i)).1 (basis7 6)) =
    ((sylowGenerator j (h j)).1 (basis7 0),
      (sylowGenerator j (h j)).1 (basis7 2),
      (sylowGenerator j (h j)).1 (basis7 3),
      (sylowGenerator j (h j)).1 (basis7 4),
      (sylowGenerator j (h j)).1 (basis7 5),
      (sylowGenerator j (h j)).1 (basis7 6)) at he
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    simp only [sylowGenerator_on_basis7] at he
    revert he
    decide

noncomputable def sylowCandidateSubgroup
    (h : ∀ i : Fin 5, admissibleBasis7 (sylowBasis i)) :
    Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range (fun i : Fin 5 => sylowGenerator i (h i)))

noncomputable instance sylowCandidateSubgroup_finite
    (h : ∀ i : Fin 5, admissibleBasis7 (sylowBasis i)) :
    Finite (sylowCandidateSubgroup h) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance sylowCandidateSubgroup_fintype
    (h : ∀ i : Fin 5, admissibleBasis7 (sylowBasis i)) :
    Fintype (sylowCandidateSubgroup h) :=
  Fintype.ofFinite _

theorem sylowGenerator_mem_candidateSubgroup
    (h : ∀ i : Fin 5, admissibleBasis7 (sylowBasis i)) (i : Fin 5) :
    sylowGenerator i (h i) ∈ sylowCandidateSubgroup h := by
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem sylowCandidateSubgroup_card_lower_bound
    (h : ∀ i : Fin 5, admissibleBasis7 (sylowBasis i)) :
    5 ≤ Fintype.card (sylowCandidateSubgroup h) := by
  let f : Fin 5 → sylowCandidateSubgroup h := fun i =>
    ⟨sylowGenerator i (h i), sylowGenerator_mem_candidateSubgroup h i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply sylowGenerator_injective h
    exact congrArg Subtype.val hij
  have hc : Fintype.card (Fin 5) ≤
      Fintype.card (sylowCandidateSubgroup h) :=
    Fintype.card_le_of_injective f hf
  simpa using hc

end InfoGeometry.Algebra.Zorn.G2TwoSylowCandidate
