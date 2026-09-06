import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Generic continuous involution readout for a filtered star colimit

Every finite stage of a `ContinuousStarInductiveSystem` has a continuous star
map, and every transition is a star homomorphism. The topological colimit
therefore carries a canonical continuous readout of the involution.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalStarReadout

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

def continuousStageStar (i : I) :
    ContinuousMap (Stage i) (Stage i) :=
  { toFun := star
    continuous_toFun := ContinuousStar.continuous_star }

def stageStar (i : I) (x : Stage i) : Stage i := star x

def topologicalStarCocone :
    Cocone (topologicalDiagram Stage sys) where
  pt := topologicalColimit Stage sys
  ι :=
    { app := fun i =>
        TopCat.ofHom (continuousStageStar Stage i) ≫
          topologicalInjection Stage sys i
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        simp [topologicalDiagram, transitionContinuousMap,
          continuousStageStar]
        change topologicalInjection Stage sys j
            (stageStar Stage j (sys.map (leOfHom f) (x : Stage i))) =
          topologicalInjection Stage sys i
            (stageStar Stage i (x : Stage i))
        have hmap :
            stageStar Stage j (sys.map (leOfHom f) (x : Stage i)) =
              sys.map (leOfHom f) (stageStar Stage i (x : Stage i)) := by
          simpa [stageStar] using
            (map_star (sys.map (leOfHom f)) (x : Stage i)).symm
        rw [hmap]
        exact topologicalInjection_transition Stage sys
          (leOfHom f) (stageStar Stage i (x : Stage i)) }

noncomputable def topologicalStarReadout :
    topologicalColimit Stage sys ⟶ topologicalColimit Stage sys :=
  colimit.desc (topologicalDiagram Stage sys)
    (topologicalStarCocone Stage sys)

omit [Nonempty I] [IsDirectedOrder I] in
theorem topologicalStarReadout_stage (i : I) (x : Stage i) :
    topologicalStarReadout Stage sys
        (topologicalInjection Stage sys i x) =
      topologicalInjection Stage sys i (stageStar Stage i x) := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram Stage sys) (topologicalStarCocone Stage sys) i
  exact congrArg (fun f => f x) h

omit [Nonempty I] [IsDirectedOrder I] in
theorem topologicalStarReadout_unique
    (f : topologicalColimit Stage sys ⟶ topologicalColimit Stage sys)
    (hf : ∀ (i : I) (x : Stage i),
      f (topologicalInjection Stage sys i x) =
        topologicalInjection Stage sys i (stageStar Stage i x)) :
    f = topologicalStarReadout Stage sys := by
  apply topologicalDirectDescend_unique
    (topologicalDiagram Stage sys) (topologicalStarCocone Stage sys) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change f (topologicalInjection Stage sys i x) =
    topologicalInjection Stage sys i (stageStar Stage i x)
  exact hf i x

omit [Nonempty I] [IsDirectedOrder I] in
theorem topologicalStarReadout_involutive :
    topologicalStarReadout Stage sys ≫
        topologicalStarReadout Stage sys = 𝟙 _ := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  let x' : Stage i := x
  change topologicalStarReadout Stage sys
      (topologicalStarReadout Stage sys
        (topologicalInjection Stage sys i x')) =
    topologicalInjection Stage sys i x'
  rw [topologicalStarReadout_stage,
    topologicalStarReadout_stage]
  simp [stageStar, x']

end CStarStateColimit.Native.FilteredStarAlgebraTopologicalStarReadout
