import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularFlowTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` factorization of a modular-flow orbit

The orbit is a range subtype of the native continuous trajectory.  This file
packages its evaluation map and ambient inclusion without asserting that the
orbit is closed or that the flow is a homeomorphism at each time.
-/

def SymbolicLatentModularFlow.orbitEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    TopCat.of ℝ ⟶ TopCat.of (Φ.orbit x) :=
  TopCat.ofHom
    { toFun := fun t => ⟨Φ.act t x, ⟨t, rfl⟩⟩
      continuous_toFun :=
        Φ.continuous_orbit x |>.subtype_mk (fun t => ⟨t, rfl⟩) }

def SymbolicLatentModularFlow.orbitInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    TopCat.of (Φ.orbit x) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentModularFlow.orbitAmbientEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    TopCat.of ℝ ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun t => Φ.act t x
      continuous_toFun := Φ.continuous_orbit x }

@[simp] theorem SymbolicLatentModularFlow.orbitEvaluationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    Φ.orbitEvaluationTopCatHom x t = ⟨Φ.act t x, ⟨t, rfl⟩⟩ :=
  rfl

theorem SymbolicLatentModularFlow.orbit_evaluation_factorization
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbitEvaluationTopCatHom x ≫ Φ.orbitInclusionTopCatHom x =
      Φ.orbitAmbientEvaluationTopCatHom x := by
  ext t
  rfl

theorem SymbolicLatentModularFlow.orbit_evaluation_factorization_unique
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X)
    {u : TopCat.of ℝ ⟶ TopCat.of (Φ.orbit x)}
    (hu : u ≫ Φ.orbitInclusionTopCatHom x =
      Φ.orbitAmbientEvaluationTopCatHom x) :
    u = Φ.orbitEvaluationTopCatHom x := by
  apply TopCat.hom_ext
  ext t
  have ht := congrArg (fun m => m t) hu
  simpa [SymbolicLatentModularFlow.orbitEvaluationTopCatHom,
    SymbolicLatentModularFlow.orbitInclusionTopCatHom,
    SymbolicLatentModularFlow.orbitAmbientEvaluationTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using ht

theorem SymbolicLatentModularFlow.orbit_initial_point
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbitAmbientEvaluationTopCatHom x 0 = x := by
  exact Φ.zero_apply x

end InfoGeometry.Topology
