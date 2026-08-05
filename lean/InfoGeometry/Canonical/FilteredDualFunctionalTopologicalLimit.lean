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
    (Opposite.op j) ⟶ (Opposite.op i) :=
  (homOfLE hij).op

/-- The inverse-direction `TopCat` diagram, indexed by the order dual. -/
def dualTopologicalDiagram : Iᵒᵖ ⥤ TopCat.{u} where
  obj i := TopCat.of (Dual i.unop)
  map f :=
    TopCat.ofHom
      (sys.restriction (leOfHom f.unop))
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun g => g x) (sys.restriction_id i.unop)
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rw [TopCat.comp_app]
    change sys.restriction (leOfHom (f ≫ g).unop) x =
      sys.restriction (leOfHom g.unop)
        (sys.restriction (leOfHom f.unop) x)
    exact Eq.symm (sys.restriction_comp (leOfHom g.unop) (leOfHom f.unop) x)

/-- The native categorical inverse limit of the dual-functional stages. -/
abbrev dualTopologicalLimit : TopCat.{u} :=
  limit (dualTopologicalDiagram Dual sys)

/-- Projection from the dual-functional limit to stage `i`. -/
def dualTopologicalProjection (i : I) :
    dualTopologicalLimit Dual sys ⟶ TopCat.of (Dual i) :=
  limit.π (dualTopologicalDiagram Dual sys) (Opposite.op i)

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

/-- A natural endomorphism of the restriction diagram induces a continuous
endomorphism of its native inverse limit. -/
def dualTopologicalLimitMap
    (α : dualTopologicalDiagram Dual sys ⟶
      dualTopologicalDiagram Dual sys) :
    dualTopologicalLimit Dual sys ⟶ dualTopologicalLimit Dual sys :=
  (limit.isLimit (dualTopologicalDiagram Dual sys)).map
    (limit.cone (dualTopologicalDiagram Dual sys)) α

theorem dualTopologicalLimitMap_projection
    (α : dualTopologicalDiagram Dual sys ⟶
      dualTopologicalDiagram Dual sys) (i : I) :
    dualTopologicalLimitMap Dual sys α ≫
        dualTopologicalProjection Dual sys i =
      dualTopologicalProjection Dual sys i ≫ α.app (Opposite.op i) := by
  exact IsLimit.map_π (limit.cone (dualTopologicalDiagram Dual sys))
    (limit.isLimit (dualTopologicalDiagram Dual sys)) α (Opposite.op i)

theorem dualTopologicalLimitMap_projection_apply
    (α : dualTopologicalDiagram Dual sys ⟶
      dualTopologicalDiagram Dual sys) (i : I)
    (x : dualTopologicalLimit Dual sys) :
    dualTopologicalProjection Dual sys i
        (dualTopologicalLimitMap Dual sys α x) =
      α.app (Opposite.op i)
        (dualTopologicalProjection Dual sys i x) := by
  exact congrArg (fun f => f x)
    (dualTopologicalLimitMap_projection Dual sys α i)

/-! A compatible family of continuous coordinates gives a canonical point in
the inverse limit through `limit.lift`. -/
abbrev CompatibleDualFamily (X : TopCat.{u}) :=
  ∀ i : I, X ⟶ TopCat.of (Dual i)

variable {X : TopCat.{u}}

def compatibleDualFamilyCone
    (c : CompatibleDualFamily Dual X)
    (hc : ∀ {i j : I} (hij : i ≤ j),
      c j ≫
          (dualTopologicalDiagram Dual sys).map (dualHom hij) =
        c i) :
    Cone (dualTopologicalDiagram Dual sys) where
  pt := X
  π :=
    { app := fun i => c i.unop
      naturality := by
        intro i j f
        dsimp
        rw [Category.id_comp]
        exact Eq.symm (hc (leOfHom f.unop)) }

/-- Lift a compatible dual-functional family into the native inverse limit. -/
def compatibleDualFamilyLift
    (c : CompatibleDualFamily Dual X)
    (hc : ∀ {i j : I} (hij : i ≤ j),
      c j ≫
          (dualTopologicalDiagram Dual sys).map (dualHom hij) =
        c i) :
    X ⟶ dualTopologicalLimit Dual sys :=
  limit.lift (dualTopologicalDiagram Dual sys)
    (compatibleDualFamilyCone Dual sys c hc)

theorem compatibleDualFamilyLift_projection
    (c : CompatibleDualFamily Dual X)
    (hc : ∀ {i j : I} (hij : i ≤ j),
      c j ≫
          (dualTopologicalDiagram Dual sys).map (dualHom hij) =
        c i) (i : I) :
    compatibleDualFamilyLift Dual sys c hc ≫
        dualTopologicalProjection Dual sys i = c i := by
  exact limit.lift_π
    (compatibleDualFamilyCone Dual sys c hc) (Opposite.op i)

theorem compatibleDualFamilyLift_unique
    (c : CompatibleDualFamily Dual X)
    (hc : ∀ {i j : I} (hij : i ≤ j),
      c j ≫
          (dualTopologicalDiagram Dual sys).map (dualHom hij) =
        c i)
    (f : X ⟶ dualTopologicalLimit Dual sys)
    (h : ∀ i, f ≫ dualTopologicalProjection Dual sys i = c i) :
    f = compatibleDualFamilyLift Dual sys c hc := by
  apply limit.hom_ext
  intro i
  change f ≫ dualTopologicalProjection Dual sys i.unop =
    compatibleDualFamilyLift Dual sys c hc ≫
      dualTopologicalProjection Dual sys i.unop
  rw [h i.unop, compatibleDualFamilyLift_projection Dual sys c hc]

theorem compatibleDualFamilyLift_map_fixed
    (c : CompatibleDualFamily Dual X)
    (hc : ∀ {i j : I} (hij : i ≤ j),
      c j ≫
          (dualTopologicalDiagram Dual sys).map (dualHom hij) =
        c i)
    (α : dualTopologicalDiagram Dual sys ⟶
      dualTopologicalDiagram Dual sys)
    (hα : ∀ i : I,
      c i ≫ α.app (Opposite.op i) = c i) :
    compatibleDualFamilyLift Dual sys c hc ≫
        dualTopologicalLimitMap Dual sys α =
    compatibleDualFamilyLift Dual sys c hc := by
  apply limit.hom_ext
  intro i
  calc
    compatibleDualFamilyLift Dual sys c hc ≫
        dualTopologicalLimitMap Dual sys α ≫
          dualTopologicalProjection Dual sys i.unop =
          compatibleDualFamilyLift Dual sys c hc ≫
          dualTopologicalProjection Dual sys i.unop ≫
            α.app (Opposite.op i.unop) := by
              rw [dualTopologicalLimitMap_projection]
    _ = c i.unop ≫ α.app (Opposite.op i.unop) := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ α.app (Opposite.op i.unop))
              (compatibleDualFamilyLift_projection Dual sys c hc i.unop)
    _ = c i.unop := hα i.unop
    _ = compatibleDualFamilyLift Dual sys c hc ≫
        dualTopologicalProjection Dual sys i.unop := by
          exact (compatibleDualFamilyLift_projection Dual sys c hc i.unop).symm

end FilteredColimit.Native.TopologicalDual
