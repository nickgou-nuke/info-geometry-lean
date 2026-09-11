import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.HasLimits

namespace InfoGeometry.Topology

open CategoryTheory Limits

/-!
# Transport of compatible observables through a `TopCat` colimit

This is a generic bridge only.  It does not construct a spectrum diagram or
identify a colimit with a continuum; it packages the native `IsColimit.desc`,
factorization, and uniqueness APIs for a compatible family of continuous
observables.
-/

variable {J : Type*} [Category J]
variable (SpectrumDiagram : J ⥤ TopCat)
variable (C : Cocone SpectrumDiagram)
variable (hC : IsColimit C)
variable (TargetObservableSpace : TopCat)
variable (localObservables : (j : J) → SpectrumDiagram.obj j ⟶
  TargetObservableSpace)
variable (hCompatible : ∀ {i j : J} (f : i ⟶ j),
  SpectrumDiagram.map f ≫ localObservables j = localObservables i)

noncomputable def observableCocone : Cocone SpectrumDiagram where
  pt := TargetObservableSpace
  ι :=
    { app := localObservables
      naturality := by
        intro i j f
        exact hCompatible f }

noncomputable def globalObservable : C.pt ⟶ TargetObservableSpace :=
  hC.desc (observableCocone SpectrumDiagram TargetObservableSpace
    localObservables hCompatible)

theorem globalObservable_restricts_to_local (j : J) :
    C.ι.app j ≫ globalObservable SpectrumDiagram C hC
        TargetObservableSpace localObservables hCompatible =
      localObservables j :=
  hC.fac (observableCocone SpectrumDiagram TargetObservableSpace
    localObservables hCompatible) j

theorem globalObservable_unique
    (m : C.pt ⟶ TargetObservableSpace)
    (hm : ∀ j : J, C.ι.app j ≫ m = localObservables j) :
    m = globalObservable SpectrumDiagram C hC TargetObservableSpace
      localObservables hCompatible := by
  apply hC.uniq
    (observableCocone SpectrumDiagram TargetObservableSpace
      localObservables hCompatible)
    m
  intro j
  change C.ι.app j ≫ m = localObservables j
  exact hm j

end InfoGeometry.Topology
