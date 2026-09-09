import InfoGeometry.Canonical.FilteredGNSTomitaClosedTransport
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Topological colimit of closed Tomita domains

The closed Tomita operator itself may be unbounded.  This owner therefore
records only the continuous transport of its closed domains, which is already
induced by the completed-GNS isometries.  The resulting `TopCat` diagram and
its categorical colimit do not assert boundedness or continuity of the
unbounded operator.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

def closedDomainContinuousMap {i j : I} (hij : i ≤ j) :
    ContinuousMap (closedTomitaDomain (ω.state i))
      (closedTomitaDomain (ω.state j)) :=
  { toFun := filteredClosedTomitaDomainMap Stage sys ω hij
    continuous_toFun := by
      apply Continuous.subtype_mk
      have h := (filteredGNSMapCLM Stage sys ω hij).continuous.comp
        (continuous_subtype_val :
          Continuous (fun x : closedTomitaDomain (ω.state i) => x.1))
      simpa [Function.comp_def, filteredGNSMapCLM_apply] using h }

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
@[simp] theorem closedDomainContinuousMap_apply
    {i j : I} (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    closedDomainContinuousMap Stage sys ω hij x =
      filteredClosedTomitaDomainMap Stage sys ω hij x :=
  rfl

def topologicalDiagram : I ⥤ TopCat where
  obj i := TopCat.of (closedTomitaDomain (ω.state i))
  map f := TopCat.ofHom
    (closedDomainContinuousMap Stage sys ω (leOfHom f))
  map_id i := by
    apply TopCat.hom_ext
    ext x
    rw [TopCat.id_app]
    change (closedDomainContinuousMap Stage sys ω (le_refl i) x).1 = x.1
    rw [closedDomainContinuousMap_apply]
    exact congrArg Subtype.val
      (congrArg (fun f => f x)
        (filteredClosedTomitaDomainMap_id Stage sys ω i))
  map_comp f g := by
    apply TopCat.hom_ext
    ext x
    rw [TopCat.comp_app]
    change (closedDomainContinuousMap Stage sys ω
        (le_trans (leOfHom f) (leOfHom g)) x).1 =
      (closedDomainContinuousMap Stage sys ω (leOfHom g)
        (closedDomainContinuousMap Stage sys ω (leOfHom f) x)).1
    rw [closedDomainContinuousMap_apply, closedDomainContinuousMap_apply,
      closedDomainContinuousMap_apply]
    exact congrArg Subtype.val
      (congrArg (fun f => f x)
        (filteredClosedTomitaDomainMap_comp Stage sys ω
          (leOfHom f) (leOfHom g)).symm)

abbrev topologicalColimit : TopCat :=
  topologicalDirectColimit (topologicalDiagram Stage sys ω)

def topologicalInjection (i : I) :
    (topologicalDiagram Stage sys ω).obj i ⟶ topologicalColimit Stage sys ω :=
  topologicalDirectInjection (topologicalDiagram Stage sys ω) i

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
theorem topologicalInjection_transition
    {i j : I} (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    topologicalInjection Stage sys ω j
        (filteredClosedTomitaDomainMap Stage sys ω hij x) =
      topologicalInjection Stage sys ω i x := by
  have h := (colimit.cocone (topologicalDiagram Stage sys ω)).w
    (homOfLE hij)
  exact congrArg (fun f => f x) h

end CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit
