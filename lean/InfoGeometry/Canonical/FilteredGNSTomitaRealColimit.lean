import InfoGeometry.Canonical.FilteredGNSTomitaDomainColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real colimit descent of filtered closed Tomita operators

A closed Tomita operator is conjugate-linear over `ℂ`, hence it is not a
morphism in `ModuleCat ℂ`.  Complex conjugation fixes real scalars, however,
so every closed Tomita operator is canonically real-linear.

This file:

* restricts the filtered closed-domain and GNS transition maps to `ℝ`;
* builds the corresponding native `ModuleCat ℝ` diagrams;
* turns the compatible closed Tomita operators into a natural transformation;
* obtains the colimit Tomita operator through Mathlib's `colim.map`;
* proves its compatibility with every stage inclusion.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaRealColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CategoryTheory CategoryTheory.Limits

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)
variable
  (hclos :
    ∀ i, IsClosableTomitaCore (ω.state i))

/-- A closed conjugate-linear Tomita operator is canonically real-linear. -/
def closedTomitaOperatorRealLinearMap
    (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      (ω.state i).functional.GNS where
  toFun :=
    closedTomitaOperator
      (ω.state i) (hclos i)
  map_add' := by
    intro x y
    exact
      (closedTomitaOperator
        (ω.state i) (hclos i)).map_add x y
  map_smul' := by
    intro r x
    have h :=
      (closedTomitaOperator
        (ω.state i) (hclos i)).map_smulₛₗ
          (r : ℂ) x
    simpa using h

/-- Explicit real-linear restriction of a filtered closed-domain map. -/
def filteredClosedTomitaDomainRealMap
    {i j : I} (hij : i ≤ j) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      closedTomitaDomain (ω.state j) where
  toFun :=
    filteredClosedTomitaDomainMap
      Stage sys ω hij
  map_add' := by
    intro x y
    exact
      (filteredClosedTomitaDomainMap
        Stage sys ω hij).map_add x y
  map_smul' := by
    intro r x
    have h :=
      (filteredClosedTomitaDomainMap
        Stage sys ω hij).map_smul (r : ℂ) x
    simpa using h

/-- Explicit real-linear restriction of a filtered completed-GNS map. -/
def filteredGNSRealMap
    {i j : I} (hij : i ≤ j) :
    (ω.state i).functional.GNS →ₗ[ℝ]
      (ω.state j).functional.GNS where
  toFun :=
    filteredGNSMap Stage sys ω hij
  map_add' := by
    intro x y
    simpa only [filteredGNSMapCLM_apply] using
      (filteredGNSMapCLM
        Stage sys ω hij).map_add x y
  map_smul' := by
    intro r x
    have h :=
      (filteredGNSMapCLM
        Stage sys ω hij).map_smul (r : ℂ) x
    simpa only [filteredGNSMapCLM_apply] using h

/-- Real-linear filtered direct system of closed Tomita domains. -/
def closedTomitaDomainRealDirectSystem :
    FilteredColimit.DirectInductiveSystem
      ℝ I (fun i => closedTomitaDomain (ω.state i)) where
  f := fun hij =>
    filteredClosedTomitaDomainRealMap
      Stage sys ω hij
  f_id := by
    intro i
    ext x
    exact congrFun
      (filteredGNSMap_id Stage sys ω i) x.1
  f_comp := by
    intro i j k hij hjk
    ext x
    exact congrFun
      (filteredGNSMap_comp
        Stage sys ω hij hjk) x.1

/-- Real-linear filtered direct system of completed GNS spaces. -/
def gnsRealDirectSystem :
    FilteredColimit.DirectInductiveSystem
      ℝ I (fun i => (ω.state i).functional.GNS) where
  f := fun hij =>
    filteredGNSRealMap
      Stage sys ω hij
  f_id := by
    intro i
    ext x
    exact congrFun
      (filteredGNSMap_id Stage sys ω i) x
  f_comp := by
    intro i j k hij hjk
    ext x
    exact congrFun
      (filteredGNSMap_comp
        Stage sys ω hij hjk) x

/-- Native real `ModuleCat` diagram of the closed Tomita domains. -/
def closedTomitaDomainRealDiagram :
    I ⥤ ModuleCat.{u} ℝ where
  obj i :=
    ModuleCat.of ℝ
      (closedTomitaDomain (ω.state i))
  map f :=
    ModuleCat.ofHom
      ((closedTomitaDomainRealDirectSystem
        Stage sys ω).f (leOfHom f))
  map_id i := by
    apply ModuleCat.hom_ext
    change
      (closedTomitaDomainRealDirectSystem
        Stage sys ω).f (le_refl i) =
          LinearMap.id
    exact
      (closedTomitaDomainRealDirectSystem
        Stage sys ω).f_id i
  map_comp f g := by
    apply ModuleCat.hom_ext
    change
      (closedTomitaDomainRealDirectSystem
          Stage sys ω).f
          (le_trans (leOfHom f) (leOfHom g)) =
        ((closedTomitaDomainRealDirectSystem
          Stage sys ω).f (leOfHom g)).comp
          ((closedTomitaDomainRealDirectSystem
            Stage sys ω).f (leOfHom f))
    exact
      ((closedTomitaDomainRealDirectSystem
        Stage sys ω).f_comp
          (leOfHom f) (leOfHom g)).symm

/-- Native real `ModuleCat` diagram of the completed GNS spaces. -/
def gnsRealDiagram :
    I ⥤ ModuleCat.{u} ℝ where
  obj i :=
    ModuleCat.of ℝ
      ((ω.state i).functional.GNS)
  map f :=
    ModuleCat.ofHom
      ((gnsRealDirectSystem
        Stage sys ω).f (leOfHom f))
  map_id i := by
    apply ModuleCat.hom_ext
    change
      (gnsRealDirectSystem
        Stage sys ω).f (le_refl i) =
          LinearMap.id
    exact
      (gnsRealDirectSystem
        Stage sys ω).f_id i
  map_comp f g := by
    apply ModuleCat.hom_ext
    change
      (gnsRealDirectSystem
          Stage sys ω).f
          (le_trans (leOfHom f) (leOfHom g)) =
        ((gnsRealDirectSystem
          Stage sys ω).f (leOfHom g)).comp
          ((gnsRealDirectSystem
            Stage sys ω).f (leOfHom f))
    exact
      ((gnsRealDirectSystem
        Stage sys ω).f_comp
          (leOfHom f) (leOfHom g)).symm

/-- The compatible closed Tomita operators form a natural transformation
between the realified domain and GNS diagrams. -/
def closedTomitaOperatorNatTrans :
    closedTomitaDomainRealDiagram Stage sys ω ⟶
      gnsRealDiagram Stage sys ω where
  app i :=
    ModuleCat.ofHom
      (closedTomitaOperatorRealLinearMap
        Stage sys ω hclos i)
  naturality := by
    intro i j f
    apply ModuleCat.hom_ext
    change
      (closedTomitaOperatorRealLinearMap
          Stage sys ω hclos j).comp
          (filteredClosedTomitaDomainRealMap
            Stage sys ω (leOfHom f)) =
        (filteredGNSRealMap
          Stage sys ω (leOfHom f)).comp
          (closedTomitaOperatorRealLinearMap
            Stage sys ω hclos i)
    ext x
    exact
      (filteredGNSMap_intertwines_closedTomitaOperator
        Stage sys ω (leOfHom f)
        (hclos i) (hclos j) x).symm

/-- Real categorical colimit of the closed Tomita domains. -/
noncomputable abbrev ClosedTomitaDomainRealColimit :
    Type u :=
  (colimit
    (closedTomitaDomainRealDiagram
      Stage sys ω) :
    ModuleCat.{u} ℝ)

/-- Real categorical colimit of the completed GNS spaces. -/
noncomputable abbrev GNSRealColimit :
    Type u :=
  (colimit
    (gnsRealDiagram Stage sys ω) :
    ModuleCat.{u} ℝ)

/-- Closed Tomita operator on the realified categorical colimits. -/
noncomputable def closedTomitaRealColimitOperator :
    ClosedTomitaDomainRealColimit
        Stage sys ω →ₗ[ℝ]
      GNSRealColimit Stage sys ω :=
  (colim.map
    (closedTomitaOperatorNatTrans
      Stage sys ω hclos)).hom

/-- Canonical real-linear inclusion of a closed stage domain. -/
noncomputable def closedTomitaDomainRealInclusion
    (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      ClosedTomitaDomainRealColimit
        Stage sys ω :=
  (colimit.ι
    (closedTomitaDomainRealDiagram
      Stage sys ω) i).hom

/-- Canonical real-linear inclusion of a completed stage GNS space. -/
noncomputable def gnsRealInclusion
    (i : I) :
    (ω.state i).functional.GNS →ₗ[ℝ]
      GNSRealColimit Stage sys ω :=
  (colimit.ι
    (gnsRealDiagram Stage sys ω) i).hom

/-- The real colimit Tomita operator agrees with every closed stage operator
after canonical inclusion. -/
theorem closedTomitaRealColimitOperator_inclusion
    (i : I)
    (x : closedTomitaDomain (ω.state i)) :
    closedTomitaRealColimitOperator
        Stage sys ω hclos
        (closedTomitaDomainRealInclusion
          Stage sys ω i x) =
      gnsRealInclusion Stage sys ω i
        (closedTomitaOperator
          (ω.state i) (hclos i) x) := by
  have hι :=
    colimit.ι_map
      (closedTomitaOperatorNatTrans
        Stage sys ω hclos) i
  exact congrArg
    (fun f :
      (closedTomitaDomainRealDiagram
        Stage sys ω).obj i ⟶
        colimit (gnsRealDiagram Stage sys ω) =>
      f x)
    hι

end CStarStateColimit.Native.FilteredGNSTomitaRealColimit
