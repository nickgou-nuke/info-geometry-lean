import InfoGeometry.Lie.SplitOctonionCartanSixWeights
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# Carrier weights and short adjoint roots

This owner compares the six circular carrier weights with the six short
weights in the concrete fourteen-dimensional adjoint spectrum.  It does not
identify the six-dimensional carrier with the full adjoint representation.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCartanCarrierAdjointRootBridge

open InfoGeometry.Lie.SplitOctonionCartanSixWeights
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

theorem weightFunctional_eq_coordWeight (i : Fin 3) :
    weightFunctional i = coordWeight i := by
  apply LinearMap.ext
  intro k
  rfl

def shortRootIndex := {j : Fin 14 // j ∈ shortRootIndices}

def shortIndexOf : Fin 2 → Fin 3 → Fin 14
  | 0, 0 => 10
  | 0, 1 => 9
  | 0, 2 => 4
  | 1, 0 => 0
  | 1, 1 => 3
  | 1, 2 => 8

def signedWeightToShortIndex (p : SignedWeightIndex) : shortRootIndex :=
  ⟨shortIndexOf p.1 p.2, by
    rcases p with ⟨s, i⟩
    fin_cases s <;> fin_cases i <;> simp [shortIndexOf, shortRootIndices]⟩

def signedOfShort : Fin 14 → SignedWeightIndex
  | 0 => (1, 0)
  | 3 => (1, 1)
  | 4 => (0, 2)
  | 8 => (1, 2)
  | 9 => (0, 1)
  | 10 => (0, 0)
  | _ => (0, 0)

def shortRootIndexToSignedWeight (j : shortRootIndex) : SignedWeightIndex :=
  signedOfShort j.1

def shortRootIndexEquiv : SignedWeightIndex ≃ shortRootIndex where
  toFun := signedWeightToShortIndex
  invFun := shortRootIndexToSignedWeight
  left_inv := by
    intro p
    rcases p with ⟨s, i⟩
    fin_cases s <;> fin_cases i <;> rfl
  right_inv := by
    intro j
    rcases j with ⟨j, hj⟩
    fin_cases j <;> simp [shortRootIndices, shortIndexOf] at hj ⊢ <;> rfl

theorem rootWeight_signedWeightToShortIndex (p : SignedWeightIndex) :
    rootWeight (signedWeightToShortIndex p).1 = signedWeight p := by
  rcases p with ⟨s, i⟩
  fin_cases s <;> fin_cases i <;>
    simp [signedWeightToShortIndex, shortIndexOf, signedWeight,
      rootWeight, coordWeight, weightFunctional]

theorem signedWeight_injective :
    Function.Injective signedWeight := by
  intro p q h
  have hroot :
      rootWeight (signedWeightToShortIndex p).1 =
        rootWeight (signedWeightToShortIndex q).1 := by
    rw [rootWeight_signedWeightToShortIndex,
      rootWeight_signedWeightToShortIndex, h]
  apply shortRootIndexEquiv.injective
  apply Subtype.ext
  by_contra hne
  let i : nonzeroIndex :=
    ⟨(signedWeightToShortIndex p).1,
      by
        have hp := rootWeight_short_indices_nonzero _
          (signedWeightToShortIndex p).2
        constructor
        · intro h6
          apply hp
          exact (rootWeight_eq_zero_iff _).2 (Or.inl h6)
        · intro h13
          apply hp
          exact (rootWeight_eq_zero_iff _).2 (Or.inr h13)⟩
  let j : nonzeroIndex :=
    ⟨(signedWeightToShortIndex q).1,
      by
        have hq := rootWeight_short_indices_nonzero _
          (signedWeightToShortIndex q).2
        constructor
        · intro h6
          apply hq
          exact (rootWeight_eq_zero_iff _).2 (Or.inl h6)
        · intro h13
          apply hq
          exact (rootWeight_eq_zero_iff _).2 (Or.inr h13)⟩
  have hij : i ≠ j := by
    intro hij
    apply hne
    change i.1 = j.1
    exact congrArg Subtype.val hij
  exact rootWeight_injective_on_nonzero i j hij hroot

theorem signedWeight_range_eq_shortRootWeights :
    Set.range signedWeight = shortRootWeights := by
  ext α
  constructor
  · rintro ⟨p, rfl⟩
    rw [← rootWeight_signedWeightToShortIndex p]
    simp only [shortRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases p with ⟨s, i⟩
    fin_cases s <;> fin_cases i <;>
      simp [signedWeightToShortIndex, shortIndexOf, rootWeight, coordWeight]

  · intro hα
    simp only [shortRootWeights, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 0), by simp [signedWeight, weightFunctional_eq_coordWeight]
      ⟩
    · exact ⟨(1, 0), by simp [signedWeight, weightFunctional_eq_coordWeight]
      ⟩
    · exact ⟨(0, 1), by simp [signedWeight, weightFunctional_eq_coordWeight]
      ⟩
    · exact ⟨(1, 1), by simp [signedWeight, weightFunctional_eq_coordWeight]
      ⟩
    · exact ⟨(0, 2), by simp [signedWeight, weightFunctional_eq_coordWeight]
      ⟩
    · exact ⟨(1, 2), by simp [signedWeight, weightFunctional_eq_coordWeight]
      ⟩

end InfoGeometry.Lie.SplitOctonionCartanCarrierAdjointRootBridge
