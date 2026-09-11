import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# InfoGeometry.Categorical.FilteredDirectLimitOwner

Category-filtered direct-limit owner module for finite-tower to $\text{UHF}(2^\infty)$ promotion.

This file provides the category-theoretic owner layer for filtered inductive colimits of
modules and rings using `Mathlib.CategoryTheory.Limits.colimit`. It establishes the universal
property and stage-injection commutativity for promoting finite-stage observables
$\text{DiagAlg}(n)$ to the infinite $\text{UHF}(2^\infty)$ algebra boundary.
-/

namespace InfoGeometry.Categorical.FilteredDirectLimitOwner

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

universe u

variable (R : Type u) [CommRing R]
variable {J : Type u} [Category.{u} J]

section ModuleColimit
variable [IsFiltered J]

/-- The category-filtered direct limit of an $R$-module diagram $F : J \to \mathbf{Module}_R$. -/
noncomputable def DirectLimitModule (F : J ⥤ ModuleCat.{u} R) : ModuleCat.{u} R :=
  colimit F

/-- Canonical stage injection from stage $j \in J$ into the filtered direct limit module. -/
noncomputable def directLimitInjection (F : J ⥤ ModuleCat.{u} R) (j : J) :
    F.obj j ⟶ DirectLimitModule R F :=
  colimit.ι F j

/--
**Universal Property of Filtered Direct Limits:**
Every compatible cocone $t$ of maps from $F$ to a target module $V$ descends uniquely
to a morphism $\overline{t} : \operatorname{DirectLimitModule}(F) \to V$.
-/
noncomputable def descendDirectLimit (F : J ⥤ ModuleCat.{u} R) (t : Cocone F) :
    DirectLimitModule R F ⟶ t.pt :=
  colimit.desc F t

end ModuleColimit

/--
**Stage Injection Commutativity:**
The descended map $\overline{t}$ commutes with every stage injection $\iota_j$.
-/
@[reassoc]
theorem directLimit_desc_commutes (F : J ⥤ ModuleCat.{u} R) (t : Cocone F) (j : J) :
    directLimitInjection R F j ≫ descendDirectLimit R F t = t.ι.app j :=
  colimit.ι_desc t j

/-- The category-filtered direct limit of a ring diagram $F : J \to \mathbf{Ring}$. -/
noncomputable def DirectLimitRing (F_ring : J ⥤ RingCat.{u}) [HasColimit F_ring] : RingCat.{u} :=
  colimit F_ring

/-- Stage injection into the filtered direct limit algebra. -/
noncomputable def directLimitRingInjection (F_ring : J ⥤ RingCat.{u}) [HasColimit F_ring] (j : J) :
    F_ring.obj j ⟶ DirectLimitRing F_ring :=
  colimit.ι F_ring j

/-- Descend a compatible cocone of noncommutative ring homomorphisms through
the categorical ring colimit. -/
noncomputable def descendDirectLimitRing
    (F_ring : J ⥤ RingCat.{u}) [HasColimit F_ring] (t : Cocone F_ring) :
    DirectLimitRing F_ring ⟶ t.pt :=
  colimit.desc F_ring t

/-- The descended ring homomorphism agrees with every stage map. -/
@[reassoc]
theorem directLimitRing_desc_commutes
    (F_ring : J ⥤ RingCat.{u}) [HasColimit F_ring]
    (t : Cocone F_ring) (j : J) :
    directLimitRingInjection F_ring j ≫ descendDirectLimitRing F_ring t =
      t.ι.app j :=
  colimit.ι_desc t j

/-- The RingCat colimit descent is unique among maps with the same stage laws. -/
theorem descendDirectLimitRing_unique
    (F_ring : J ⥤ RingCat.{u}) [HasColimit F_ring]
    (t : Cocone F_ring)
    (f : DirectLimitRing F_ring ⟶ t.pt)
    (h : ∀ j : J,
      directLimitRingInjection F_ring j ≫ f = t.ι.app j) :
    f = descendDirectLimitRing F_ring t := by
  apply colimit.hom_ext
  intro j
  change directLimitRingInjection F_ring j ≫ f =
    directLimitRingInjection F_ring j ≫ descendDirectLimitRing F_ring t
  rw [h j, directLimitRing_desc_commutes]

/--
**Finite-Tower to UHF Algebra Promotion:**
Stage-local diagonal observables $f \in \text{DiagAlg}(n)$ map into the category-filtered
inductive limit algebra through the stage injection.
-/
theorem stage_observable_promotes_to_direct_limit
    (F_ring : J ⥤ RingCat.{u}) [HasColimit F_ring] (j : J) (x : F_ring.obj j) :
    directLimitRingInjection F_ring j x = colimit.ι F_ring j x :=
  rfl

end InfoGeometry.Categorical.FilteredDirectLimitOwner
