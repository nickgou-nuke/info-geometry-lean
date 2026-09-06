import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularOrbitTopCat
import InfoGeometry.Topology.SymbolicLatentOrbitClosure

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` packaging of modular-flow orbit closures

The closure is treated as the native closed subset `closure (orbit x)`.  The
maps below record the orbit-to-closure inclusion and its evaluation
factorization, without adding recurrence or compactness assumptions.
-/

abbrev SymbolicLatentModularOrbitClosure
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :=
  {y // y ∈ Φ.orbitClosure x}

def SymbolicLatentModularFlow.orbitClosureInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    TopCat.of (SymbolicLatentModularOrbitClosure Φ x) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentModularFlow.orbitToClosureTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    TopCat.of (Φ.orbit x) ⟶
      TopCat.of (SymbolicLatentModularOrbitClosure Φ x) :=
  TopCat.ofHom
    { toFun := fun y => ⟨y.1, Φ.orbit_subset_orbitClosure x y.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk
        (fun y => Φ.orbit_subset_orbitClosure x y.2) }

def SymbolicLatentModularFlow.orbitClosureEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    TopCat.of ℝ ⟶ TopCat.of (SymbolicLatentModularOrbitClosure Φ x) :=
  TopCat.ofHom
    { toFun := fun t =>
        ⟨Φ.act t x, Φ.orbit_subset_orbitClosure x ⟨t, rfl⟩⟩
      continuous_toFun :=
        Φ.continuous_orbit x |>.subtype_mk
          (fun t => Φ.orbit_subset_orbitClosure x ⟨t, rfl⟩) }

theorem SymbolicLatentModularFlow.orbitAmbientEvaluationTopCatHom_add
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) (s t : ℝ) :
    Φ.orbitAmbientEvaluationTopCatHom x (t + s) =
      Φ.orbitAmbientEvaluationTopCatHom (Φ.act s x) t := by
  simpa [SymbolicLatentModularFlow.orbitAmbientEvaluationTopCatHom] using
    (Φ.add_apply t s x)

theorem SymbolicLatentModularFlow.orbit_toClosure_factorization
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbitToClosureTopCatHom x ≫
        Φ.orbitClosureInclusionTopCatHom x =
      Φ.orbitInclusionTopCatHom x := by
  ext y
  rfl

theorem SymbolicLatentModularFlow.orbitClosure_evaluation_factorization
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbitClosureEvaluationTopCatHom x ≫
        Φ.orbitClosureInclusionTopCatHom x =
      Φ.orbitAmbientEvaluationTopCatHom x := by
  ext t
  rfl

theorem SymbolicLatentModularFlow.orbit_evaluation_toClosure_factorization
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbitEvaluationTopCatHom x ≫ Φ.orbitToClosureTopCatHom x =
      Φ.orbitClosureEvaluationTopCatHom x := by
  ext t
  rfl

theorem SymbolicLatentModularFlow.orbit_evaluation_toClosure_unique
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X)
  {u : TopCat.of (Φ.orbit x) ⟶ TopCat.of (SymbolicLatentModularOrbitClosure Φ x)}
  (hu : Φ.orbitEvaluationTopCatHom x ≫ u =
      Φ.orbitClosureEvaluationTopCatHom x) :
    u = Φ.orbitToClosureTopCatHom x := by
  apply TopCat.hom_ext
  ext y
  rcases y with ⟨z, hz⟩
  rcases hz with ⟨t, rfl⟩
  have ht := congrArg (fun m => m t) hu
  simpa [SymbolicLatentModularFlow.orbitEvaluationTopCatHom,
    SymbolicLatentModularFlow.orbitToClosureTopCatHom,
    SymbolicLatentModularFlow.orbitClosureEvaluationTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using congrArg Subtype.val ht

theorem SymbolicLatentModularFlow.orbitClosure_isClosedEmbedding
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Topology.IsClosedEmbedding
      (Subtype.val : SymbolicLatentModularOrbitClosure Φ x → X) := by
  exact (Φ.isClosed_orbitClosure x).isClosedEmbedding_subtypeVal

theorem SymbolicLatentModularFlow.isCompact_orbitClosure
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    IsCompact (Φ.orbitClosure x) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (Φ.isClosed_orbitClosure x) (Set.subset_univ _)

end InfoGeometry.Topology
