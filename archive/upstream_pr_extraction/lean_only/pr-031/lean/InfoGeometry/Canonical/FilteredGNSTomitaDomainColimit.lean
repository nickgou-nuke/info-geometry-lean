import InfoGeometry.Canonical.FilteredGNSTomitaClosedTransport

/-!
# Native colimit of filtered closed Tomita domains

The closed Tomita domains form a direct system of complex modules under the
filtered GNS transitions.  This file promotes that system to a genuine
`ModuleCat ℂ` diagram and uses Mathlib's categorical colimit.

Only the domains and their complex-linear transition maps are assembled here.
The closed Tomita operators are conjugate-linear, so their descent is not
misrepresented as a morphism in `ModuleCat ℂ`.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaDomainColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
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

/-- The closed Tomita domains and their filtered transports form a direct
inductive system of complex modules. -/
def closedTomitaDomainDirectInductiveSystem :
    FilteredColimit.DirectInductiveSystem
      ℂ I (fun i => closedTomitaDomain (ω.state i)) where
  f := fun hij =>
    filteredClosedTomitaDomainMap
      Stage sys ω hij
  f_id := by
    intro i
    exact
      filteredClosedTomitaDomainMap_id
        Stage sys ω i
  f_comp := by
    intro i j k hij hjk
    exact
      filteredClosedTomitaDomainMap_comp
        Stage sys ω hij hjk

/-- Native `ModuleCat ℂ` diagram of the filtered closed Tomita domains. -/
def closedTomitaDomainModuleDiagram :
    I ⥤ ModuleCat.{u} ℂ where
  obj i :=
    ModuleCat.of ℂ
      (closedTomitaDomain (ω.state i))
  map f :=
    ModuleCat.ofHom
      ((closedTomitaDomainDirectInductiveSystem
        Stage sys ω).f (leOfHom f))
  map_id i := by
    apply ModuleCat.hom_ext
    change
      (closedTomitaDomainDirectInductiveSystem
        Stage sys ω).f (le_refl i) =
          LinearMap.id
    exact
      (closedTomitaDomainDirectInductiveSystem
        Stage sys ω).f_id i
  map_comp f g := by
    apply ModuleCat.hom_ext
    change
      (closedTomitaDomainDirectInductiveSystem
          Stage sys ω).f (le_trans (leOfHom f) (leOfHom g)) =
        ((closedTomitaDomainDirectInductiveSystem
          Stage sys ω).f (leOfHom g)).comp
          ((closedTomitaDomainDirectInductiveSystem
            Stage sys ω).f (leOfHom f))
    exact
      ((closedTomitaDomainDirectInductiveSystem
        Stage sys ω).f_comp
          (leOfHom f) (leOfHom g)).symm

/-- Native categorical colimit carrier of the closed Tomita domains. -/
noncomputable abbrev ClosedTomitaDomainColimit : Type u :=
  (colimit
    (closedTomitaDomainModuleDiagram
      Stage sys ω) :
    ModuleCat.{u} ℂ)

/-- Canonical inclusion of every closed Tomita domain into the native
categorical colimit. -/
noncomputable def closedTomitaDomainColimitInclusion
    (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℂ]
      ClosedTomitaDomainColimit Stage sys ω :=
  (colimit.ι
    (closedTomitaDomainModuleDiagram
      Stage sys ω) i).hom

/-- Stage inclusions commute with every filtered closed-domain transition. -/
theorem closedTomitaDomainColimitInclusion_transition
    {i j : I} (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    closedTomitaDomainColimitInclusion
        Stage sys ω i x =
      closedTomitaDomainColimitInclusion
        Stage sys ω j
        (filteredClosedTomitaDomainMap
          Stage sys ω hij x) := by
  let F :=
    closedTomitaDomainModuleDiagram
      Stage sys ω
  have hw := colimit.w F (homOfLE hij)
  have hx := congrArg
    (fun k : F.obj i ⟶ colimit F => k x)
    hw.symm
  simpa [F, closedTomitaDomainColimitInclusion,
    closedTomitaDomainModuleDiagram,
    closedTomitaDomainDirectInductiveSystem] using hx

/-- A compatible cocone of linear maps out of all closed Tomita domains. -/
structure ClosedTomitaDomainCocone
    (Z : Type u)
    [AddCommGroup Z] [Module ℂ Z] where
  leg :
    ∀ i, closedTomitaDomain (ω.state i) →ₗ[ℂ] Z
  natural :
    ∀ {i j : I} (hij : i ≤ j),
      (leg j).comp
          (filteredClosedTomitaDomainMap
            Stage sys ω hij) =
        leg i

/-- Native categorical cocone associated to a compatible family of target
maps. -/
def ClosedTomitaDomainCocone.toModuleCocone
    {Z : Type u}
    [AddCommGroup Z] [Module ℂ Z]
    (C : ClosedTomitaDomainCocone
      Stage sys ω Z) :
    Cocone
      (closedTomitaDomainModuleDiagram
        Stage sys ω) where
  pt := ModuleCat.of ℂ Z
  ι :=
    { app := fun i =>
        ModuleCat.ofHom (C.leg i)
      naturality := by
        intro i j f
        ext x
        exact LinearMap.congr_fun
          (C.natural (leOfHom f)) x }

/-- Universal descent from the native closed-domain colimit. -/
noncomputable def ClosedTomitaDomainCocone.desc
    {Z : Type u}
    [AddCommGroup Z] [Module ℂ Z]
    (C : ClosedTomitaDomainCocone
      Stage sys ω Z) :
    ClosedTomitaDomainColimit Stage sys ω →ₗ[ℂ] Z :=
  (colimit.desc
    (closedTomitaDomainModuleDiagram
      Stage sys ω)
    C.toModuleCocone).hom

/-- Universal descent agrees with every supplied cocone leg. -/
theorem ClosedTomitaDomainCocone.desc_inclusion
    {Z : Type u}
    [AddCommGroup Z] [Module ℂ Z]
    (C : ClosedTomitaDomainCocone
      Stage sys ω Z)
    (i : I)
    (x : closedTomitaDomain (ω.state i)) :
    ClosedTomitaDomainCocone.desc
        Stage sys ω C
        (closedTomitaDomainColimitInclusion
          Stage sys ω i x) =
      C.leg i x := by
  have hι :=
    colimit.ι_desc
      (ClosedTomitaDomainCocone.toModuleCocone
        Stage sys ω C) i
  exact congrArg
    (fun f :
      (closedTomitaDomainModuleDiagram
        Stage sys ω).obj i ⟶
        (ClosedTomitaDomainCocone.toModuleCocone
          Stage sys ω C).pt =>
      f x)
    hι

end CStarStateColimit.Native.FilteredGNSTomitaDomainColimit
