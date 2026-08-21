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
    norm_num at h'

end InfoGeometry.Lie.CanonicalZornRootSystemComparison
