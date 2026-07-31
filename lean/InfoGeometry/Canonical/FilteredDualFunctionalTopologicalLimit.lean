import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Topological inverse limits of dual-functional stages

This owner supplies the missing topological projection for a filtered family
of dual/function spaces.  The restriction maps and their continuity are
explicit data; the inverse limit is then the native `TopCat` limit.  No norm,
completion, or infinite-dimensional duality theorem is inferred.
-/

noncomputable section

namespace FilteredColimit.Native.TopologicalDual

open CategoryTheory CategoryTheory.Limits
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I]
variable (Dual : I → Type u) [∀ i, TopologicalSpace (Dual i)]

/-- A contravariant topological family over a filtered preorder. -/
structure DualRestrictionSystem where
  restriction : ∀ {i j : I}, i ≤ j → ContinuousMap (Dual j) (Dual i)
  restriction_id : ∀ i,
    restriction (le_refl i) = ContinuousMap.id (Dual i)
  restriction_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
      (x : Dual k),
      restriction hij (restriction hjk x) =
        restriction (hij.trans hjk) x

variable (sys : DualRestrictionSystem Dual)

/-- The arrow in the order-dual category corresponding to an original
order relation. -/
def dualHom {i j : I} (hij : i ≤ j) :
    (j : Iᵒᵈ) ⟶ (i : Iᵒᵈ) :=
  homOfLE (show (j : Iᵒᵈ) ≤ (i : Iᵒᵈ) from hij)

/-- The inverse-direction `TopCat` diagram, indexed by the order dual. -/
def dualTopologicalDiagram : Iᵒᵈ ⥤ TopCat.{u} where
  obj i := TopCat.of (Dual i)
  map f :=
    TopCat.ofHom
      (sys.restriction (leOfHom f))
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun g => g x) (sys.restriction_id i)
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change sys.restriction (leOfHom g)
        (sys.restriction (leOfHom f) x) =
      sys.restriction (leOfHom (f ≫ g)) x
    exact (sys.restriction_comp (leOfHom g) (leOfHom f) x).symm

/-- The native categorical inverse limit of the dual-functional stages. -/
abbrev dualTopologicalLimit : TopCat.{u} :=
  limit (dualTopologicalDiagram Dual sys)

/-- Projection from the dual-functional limit to stage `i`. -/
def dualTopologicalProjection (i : I) :
    dualTopologicalLimit Dual sys ⟶ TopCat.of (Dual i) :=
  limit.π (dualTopologicalDiagram Dual sys) (i : Iᵒᵈ)

theorem dualTopologicalProjection_naturality
    {i j : I} (hij : i ≤ j) :
  dualTopologicalProjection Dual sys j ≫
        (dualTopologicalDiagram Dual sys).map
          (dualHom hij) =
      dualTopologicalProjection Dual sys i := by
  exact limit.w (dualTopologicalDiagram Dual sys)
    (dualHom hij)

theorem dualTopologicalProjection_naturality_apply
    {i j : I} (hij : i ≤ j)
    (x : dualTopologicalLimit Dual sys) :
    sys.restriction hij
        (dualTopologicalProjection Dual sys j x) =
      dualTopologicalProjection Dual sys i x := by
  exact congrArg (fun f => f x)
    (dualTopologicalProjection_naturality Dual sys hij)

/-! A compatible family of continuous coordinates gives a canonical point in
the inverse limit through `limit.lift`. -/
structure CompatibleDualFamily (X : TopCat.{u}) where
  coordinate : ∀ i : I, X ⟶ TopCat.of (Dual i)
  compatible : ∀ {i j : I} (hij : i ≤ j),
    coordinate j ≫
        (dualTopologicalDiagram Dual sys).map
          (dualHom hij) =
      coordinate i

variable {X : TopCat.{u}}

def compatibleDualFamilyCone
    (c : CompatibleDualFamily Dual sys X) :
    Cone (dualTopologicalDiagram Dual sys) where
  pt := X
  π :=
    { app := fun i => c.coordinate i
      naturality := by
        intro i j f
        exact c.compatible (leOfHom f) }

/-- Lift a compatible dual-functional family into the native inverse limit. -/
def compatibleDualFamilyLift
    (c : CompatibleDualFamily Dual sys X) :
    X ⟶ dualTopologicalLimit Dual sys :=
  limit.lift (dualTopologicalDiagram Dual sys)
    (compatibleDualFamilyCone Dual sys c)

theorem compatibleDualFamilyLift_projection
    (c : CompatibleDualFamily Dual sys X) (i : I) :
    compatibleDualFamilyLift Dual sys c ≫
        dualTopologicalProjection Dual sys i = c.coordinate i := by
  exact limit.lift_π
    (compatibleDualFamilyCone Dual sys c) i

theorem compatibleDualFamilyLift_unique
    (c : CompatibleDualFamily Dual sys X)
    (f : X ⟶ dualTopologicalLimit Dual sys)
    (h : ∀ i, f ≫ dualTopologicalProjection Dual sys i = c.coordinate i) :
    f = compatibleDualFamilyLift Dual sys c := by
  apply limit.hom_ext
  intro i
  change f ≫ dualTopologicalProjection Dual sys (i : I) =
    compatibleDualFamilyLift Dual sys c ≫
      dualTopologicalProjection Dual sys (i : I)
  rw [h (i : I), compatibleDualFamilyLift_projection]

end FilteredColimit.Native.TopologicalDual
