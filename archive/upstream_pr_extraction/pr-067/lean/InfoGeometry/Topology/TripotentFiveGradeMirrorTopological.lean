import Mathlib
import InfoGeometry.Topology.TripotentFiveGradeSymbolicLatentCompHaus

/-!
# Topological grade-reversal readout

The real grade-reversing mirror acts on the finite five-grade symbolic
carrier by `-2 ↔ 2`, `-1 ↔ 1`, and `0 ↔ 0`.  This owner records only the
finite topological shadow: continuity of the induced coordinate action,
equivariance of the one-hot observation map, and invariance of its compact
range.  It does not identify this finite action with an operator-level
Clifford mirror.
-/

namespace InfoGeometry.Topology.TripotentFiveGradeMirrorTopological

open CategoryTheory
open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent
open InfoGeometry.Topology.TripotentFiveGradeSymbolicLatentCompHaus

noncomputable section

local instance : TopologicalSpace FiveGrade := ⊥
local instance : DiscreteTopology FiveGrade := discreteTopology_bot FiveGrade

def fiveGradeMirror : FiveGrade → FiveGrade
  | .negTwo => .posTwo
  | .negOne => .posOne
  | .zero => .zero
  | .posOne => .negOne
  | .posTwo => .negTwo

@[simp] theorem fiveGradeMirror_involutive (k : FiveGrade) :
    fiveGradeMirror (fiveGradeMirror k) = k := by
  cases k <;> rfl

@[simp] theorem fiveGradeValue_mirror (k : FiveGrade) :
    fiveGradeValue (fiveGradeMirror k) = -fiveGradeValue k := by
  cases k <;> rfl

def fiveGradeMirrorEquiv : FiveGrade ≃ FiveGrade where
  toFun := fiveGradeMirror
  invFun := fiveGradeMirror
  left_inv := fiveGradeMirror_involutive
  right_inv := fiveGradeMirror_involutive

def fiveGradeMirrorHomeomorph : FiveGrade ≃ₜ FiveGrade where
  toEquiv := fiveGradeMirrorEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

structure SymbolicLatentIndexedHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (T : FiniteSymbolicLatentSystem Y ι) where
  latent : X ≃ₜ Y
  index : ι ≃ ι
  intertwines : ∀ (i : ι) (x : X),
    (T.observable (index i)) (latent x) = (S.observable i) x

theorem SymbolicLatentIndexedHomeomorph.observationMap_intertwines
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) (x : X) :
    (fun i => (T.observable (F.index i)) (F.latent x)) =
      symbolicObservationMap S x := by
  funext i
  exact F.intertwines i x

def fiveGradeIndexedMirror :
    SymbolicLatentIndexedHomeomorph fiveGradeSystem fiveGradeSystem where
  latent := fiveGradeMirrorHomeomorph
  index := fiveGradeMirrorEquiv
  intertwines := by
    intro i x
    cases i <;> cases x <;> rfl

theorem fiveGradeIndexedMirror_observationMap_intertwines (x : FiveGrade) :
    (fun i =>
        (fiveGradeSystem.observable (fiveGradeIndexedMirror.index i))
          (fiveGradeIndexedMirror.latent x)) =
      symbolicObservationMap fiveGradeSystem x := by
  exact fiveGradeIndexedMirror.observationMap_intertwines x

def coordinateMirror (f : FiveGrade → ℝ) : FiveGrade → ℝ :=
  fun k => f (fiveGradeMirror k)

theorem continuous_coordinateMirror :
    Continuous coordinateMirror := by
  unfold coordinateMirror
  exact continuous_pi (fun k =>
    (continuous_apply (fiveGradeMirror k)))

def coordinateMirrorHomeomorph :
    (FiveGrade → ℝ) ≃ₜ (FiveGrade → ℝ) where
  toEquiv :=
    { toFun := coordinateMirror
      invFun := coordinateMirror
      left_inv := by
        intro f
        funext k
        simp [coordinateMirror]
      right_inv := by
        intro f
        funext k
        simp [coordinateMirror] }
  continuous_toFun := continuous_coordinateMirror
  continuous_invFun := continuous_coordinateMirror

@[simp] theorem coordinateMirror_apply (f : FiveGrade → ℝ) (k : FiveGrade) :
    coordinateMirror f k = f (fiveGradeMirror k) := rfl

theorem fiveGradeObservationMap_mirror_equivariant (k : FiveGrade) :
    coordinateMirror
        (symbolicObservationMap fiveGradeSystem (fiveGradeMirror k)) =
      symbolicObservationMap fiveGradeSystem k := by
  funext g
  cases k <;> cases g <;> rfl

theorem fiveGradeObservationRange_mirror_invariant :
    Set.image coordinateMirror
        (Set.range (symbolicObservationMap fiveGradeSystem)) =
      Set.range (symbolicObservationMap fiveGradeSystem) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨fiveGradeMirror x, ?_⟩
    simpa [coordinateMirror] using
      (fiveGradeObservationMap_mirror_equivariant (fiveGradeMirror x)).symm
  · rintro ⟨x, rfl⟩
    refine ⟨symbolicObservationMap fiveGradeSystem (fiveGradeMirror x),
      ⟨fiveGradeMirror x, rfl⟩, ?_⟩
    exact fiveGradeObservationMap_mirror_equivariant x

noncomputable def fiveGradeObservationRangeHomeomorph :
    Set.range (symbolicObservationMap fiveGradeSystem) ≃ₜ
      Set.range (symbolicObservationMap fiveGradeSystem) :=
  coordinateMirrorHomeomorph.subtype (by
    intro f
    constructor
    · intro hf
      have hf' :
          coordinateMirror f ∈
            Set.image coordinateMirror
              (Set.range (symbolicObservationMap fiveGradeSystem)) :=
        ⟨f, hf, rfl⟩
      exact (Set.ext_iff.mp fiveGradeObservationRange_mirror_invariant
        (coordinateMirror f)).mp hf'
    · intro hf
      have hf' :
          f ∈ Set.image coordinateMirror
            (Set.range (symbolicObservationMap fiveGradeSystem)) := by
        refine ⟨coordinateMirror f, hf, ?_⟩
        funext k
        simp [coordinateMirror]
      exact (Set.ext_iff.mp fiveGradeObservationRange_mirror_invariant f).mp hf')

theorem continuous_coordinateMirrorHomeomorph_toFun :
    Continuous (coordinateMirrorHomeomorph :
      (FiveGrade → ℝ) → (FiveGrade → ℝ)) :=
  continuous_coordinateMirror

noncomputable def fiveGradeObservationRangeCompHausIso :
    fiveGradeObservationRangeCompHaus ≅
      fiveGradeObservationRangeCompHaus := by
  let e := fiveGradeObservationRangeHomeomorph
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e.symm (e y) = y
        exact e.symm_apply_apply y
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem fiveGradeObservationRangeCompHausIso_apply
    (y : Set.range (symbolicObservationMap fiveGradeSystem)) :
    ((fiveGradeObservationRangeCompHausIso.hom y).1) =
      coordinateMirror y.1 := rfl

end

end InfoGeometry.Topology.TripotentFiveGradeMirrorTopological
