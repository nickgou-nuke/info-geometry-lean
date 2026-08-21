import InfoGeometry.Lie.CanonicalZornRootSystemComparison

/-!
# The six positive native `G₂` roots

The finite Chevalley unipotent radical has six root coordinates.  This file
identifies those coordinates with the six positive roots in the canonical
native root owner.
-/

namespace InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev NativeRootIndex :=
  InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nonzeroIndex

def positiveNativeIndex : Fin 6 → NativeRootIndex :=
  ![nativeShortSimpleIndex,
    nativeLongSimpleIndex,
    ⟨9, by decide, by decide⟩,
    ⟨8, by decide, by decide⟩,
    ⟨11, by decide, by decide⟩,
    ⟨12, by decide, by decide⟩]

@[simp] theorem positiveNativeIndex_zero :
    positiveNativeIndex 0 = nativeShortSimpleIndex := by rfl

@[simp] theorem positiveNativeIndex_one :
    positiveNativeIndex 1 = nativeLongSimpleIndex := by rfl

theorem positiveNativeIndex_injective :
    Function.Injective positiveNativeIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    try { rfl }
  all_goals
    have h' := congrArg (fun k : NativeRootIndex => k.1) h
    simp [positiveNativeIndex, nativeShortSimpleIndex, nativeLongSimpleIndex] at h'

noncomputable def positiveNativeIndexEquiv :
    Fin 6 ≃ Set.range positiveNativeIndex :=
  Equiv.ofBijective
    (fun i => ⟨positiveNativeIndex i, ⟨i, rfl⟩⟩)
    ⟨(fun i j h => positiveNativeIndex_injective (congrArg Subtype.val h)), by
      intro y
      rcases y.2 with ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩

theorem positiveNativeRootCount :
    Fintype.card (Set.range positiveNativeIndex) = 6 := by
  rw [← Fintype.card_congr positiveNativeIndexEquiv]
  rfl

end InfoGeometry.Lie.CanonicalZornRootSystemComparison
