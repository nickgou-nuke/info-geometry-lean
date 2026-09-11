import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornRootSystemComparison

/-!
# The six positive native `G₂` roots

The finite Chevalley unipotent radical has six root coordinates.  This file
identifies those coordinates with the six positive roots in the canonical
native root owner.
-/

namespace InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev F2 := ZMod 2

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

abbrev PositiveNativeRoot := Set.range positiveNativeIndex
abbrev PositiveNativeCoordinates := PositiveNativeRoot → F2

def nativeRootCoordinate (r : PositiveNativeRoot) (t : F2) :
    PositiveNativeCoordinates :=
  fun s => if s = r then t else 0

def nativeRootSubgroup (r : PositiveNativeRoot) :
    F2 →+ PositiveNativeCoordinates where
  toFun := nativeRootCoordinate r
  map_zero' := by
    funext s
    by_cases h : s = r <;> simp [nativeRootCoordinate, h]
  map_add' s t := by
    funext u
    by_cases h : u = r <;> simp [nativeRootCoordinate, h]

theorem nativeRootSubgroup_apply (r : PositiveNativeRoot) (t : F2) :
    nativeRootSubgroup r t = nativeRootCoordinate r t :=
  rfl

theorem nativeRootSubgroup_injective (r : PositiveNativeRoot) :
    Function.Injective (nativeRootSubgroup r) := by
  intro s t h
  have h_at := congrFun h r
  simpa [nativeRootSubgroup, nativeRootCoordinate] using h_at

theorem nativeRootCoordinate_sum (x : PositiveNativeCoordinates) :
    (∑ r : PositiveNativeRoot, nativeRootCoordinate r (x r)) = x := by
  funext s
  simp [nativeRootCoordinate]

theorem nativeRootCoordinate_sum_unique (x : PositiveNativeCoordinates)
    (c : PositiveNativeRoot → F2)
    (h : (∑ r : PositiveNativeRoot, nativeRootCoordinate r (c r)) = x) :
    c = x := by
  funext r
  have hr := congrFun h r
  simpa [nativeRootCoordinate] using hr

theorem positiveNativeCoordinates_card :
    Fintype.card PositiveNativeCoordinates = 64 := by
  have hcard : Fintype.card PositiveNativeRoot = 6 := positiveNativeRootCount
  simp only [PositiveNativeCoordinates, Fintype.card_fun, ZMod.card, hcard]
  rfl

end InfoGeometry.Lie.CanonicalZornRootSystemComparison
