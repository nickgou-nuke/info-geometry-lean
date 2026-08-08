import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureTopCat
import InfoGeometry.Topology.SymbolicLatentModularFlowHomeomorphTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Modular-flow transport of orbit closures

The orbit closure is a native closed subtype.  A time slice of the modular
flow transports it to the closure of the translated orbit; no recurrence or
minimality property is introduced.
-/

theorem SymbolicLatentModularFlow.actHomeomorph_image_orbit
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.actHomeomorph t '' Φ.orbit x = Φ.orbit (Φ.act t x) := by
  change (fun z => Φ.act t z) '' Set.range (fun s : ℝ => Φ.act s x) =
    Set.range (fun s : ℝ => Φ.act s (Φ.act t x))
  apply Set.Subset.antisymm
  · rintro y ⟨z, ⟨s, hs⟩, hy⟩
    subst z
    subst y
    refine ⟨s, ?_⟩
    calc
      Φ.act s (Φ.act t x) = Φ.act (s + t) x := (Φ.add_apply s t x).symm
      _ = Φ.act (t + s) x := by rw [add_comm]
      _ = Φ.act t (Φ.act s x) := Φ.add_apply t s x
  · rintro y ⟨s, hy⟩
    subst y
    refine ⟨Φ.act s x, ⟨s, rfl⟩, ?_⟩
    calc
      Φ.act t (Φ.act s x) = Φ.act (t + s) x := (Φ.add_apply t s x).symm
      _ = Φ.act (s + t) x := by rw [add_comm]
      _ = Φ.act s (Φ.act t x) := Φ.add_apply s t x

theorem SymbolicLatentModularFlow.actHomeomorph_image_orbitClosure
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.actHomeomorph t '' Φ.orbitClosure x =
      Φ.orbitClosure (Φ.act t x) := by
  rw [show Φ.orbitClosure x = closure (Φ.orbit x) by rfl]
  rw [Φ.actHomeomorph t |>.image_closure]
  rw [show Φ.orbitClosure (Φ.act t x) = closure (Φ.orbit (Φ.act t x)) by rfl]
  simpa using
    congrArg closure (SymbolicLatentModularFlow.actHomeomorph_image_orbit (Φ := Φ) t x)

def SymbolicLatentModularFlow.orbitClosureFlowTopCatHom
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    TopCat.of (SymbolicLatentModularOrbitClosure Φ x) ⟶
      TopCat.of (SymbolicLatentModularOrbitClosure Φ (Φ.act t x)) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨Φ.act t y.1, by
          rw [← Φ.actHomeomorph_image_orbitClosure t x]
          exact ⟨y.1, y.2, rfl⟩⟩
      continuous_toFun :=
        ((Φ.actHomeomorph t).continuous_toFun.comp continuous_subtype_val).subtype_mk _ }

theorem SymbolicLatentModularFlow.orbitClosureFlowTopCatHom_natural
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.orbitClosureFlowTopCatHom t x ≫
        Φ.orbitClosureInclusionTopCatHom (Φ.act t x) =
      Φ.orbitClosureInclusionTopCatHom x ≫ Φ.actTopCatHom t := by
  ext y
  rfl

theorem SymbolicLatentModularFlow.orbitClosureFlowTopCatHom_zero_natural
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbitClosureFlowTopCatHom 0 x ≫
        Φ.orbitClosureInclusionTopCatHom (Φ.act 0 x) =
      Φ.orbitClosureInclusionTopCatHom x := by
  ext y
  simp [SymbolicLatentModularFlow.orbitClosureFlowTopCatHom,
    SymbolicLatentModularFlow.orbitClosureInclusionTopCatHom,
    SymbolicLatentModularFlow.zero_apply]

theorem SymbolicLatentModularFlow.orbitClosureFlowTopCatHom_comp_apply
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (x : X) (s t : ℝ) :
    ∀ y : SymbolicLatentModularOrbitClosure Φ x,
      ((Φ.orbitClosureFlowTopCatHom t x ≫
          Φ.orbitClosureFlowTopCatHom s (Φ.act t x)) y).1 =
        Φ.act (t + s) y.1 := by
  intro y
  change Φ.act s (Φ.act t y.1) = Φ.act (t + s) y.1
  simpa [add_comm] using (Φ.add_apply s t y.1).symm

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowTopCatHom_zero_apply
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    ∀ y : SymbolicLatentModularOrbitClosure Φ x,
      (Φ.orbitClosureFlowTopCatHom 0 x y).1 = y.1 := by
  intro y
  change Φ.act 0 y.1 = y.1
  simpa using Φ.zero_apply y.1

end InfoGeometry.Topology
