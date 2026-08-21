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

example : Decidable (admissibleBasis7 (sylowBasis 0)) := by
  unfold admissibleBasis7
  infer_instance
  | 4 => ![⟨true, false, false, false, false, false, false, true⟩,
           ⟨false, false, false, false, true, false, false, true⟩,
           ⟨false, false, false, true, false, false, false, false⟩,
           ⟨true, true, false, false, true, false, false, true⟩,
           ⟨false, false, false, true, false, true, false, false⟩,
           ⟨false, false, true, false, false, true, false, false⟩,
           ⟨false, false, false, false, false, false, false, true⟩]

noncomputable def casGenerator0Native : SplitOctF2Aut :=
  swapCartanAut * (cycle012Aut * cycle012Aut)

theorem casGenerator0Native_basis :
    basisRestriction7 casGenerator0Native = sylowBasis 0 := by
  funext i
  fin_cases i <;> decide

theorem sylowBasis0_admissible : admissibleBasis7 (sylowBasis 0) := by
  rw [← casGenerator0Native_basis]
  exact basisRestriction7_admissible casGenerator0Native

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

end InfoGeometry.Algebra.Zorn.G2TwoSylowCandidate
