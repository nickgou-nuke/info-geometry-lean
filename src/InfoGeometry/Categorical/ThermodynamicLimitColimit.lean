/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Filtered.Basic

universe u v w

namespace InfoGeometry.Categorical

open CategoryTheory
open CategoryTheory.Limits

/-
The category of finite causal wedges/subcomplexes is modeled as a filtered category.
A functor `F : J ⥤ C` assigns a local observable algebra or state space to each finite wedge.
-/
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {C : Type u} [Category.{v} C]
variable (F : J ⥤ C) [HasColimit F]

/--
We define the infinite (thermodynamic / geometric limit) as the direct colimit
over the filtered poset/category of finite subregions.
-/
noncomputable def ThermodynamicLimit : C :=
  colimit F

/--
The canonical cocone associated with the thermodynamic limit, packaging the local-to-global inclusions.
-/
noncomputable def ThermodynamicLimitCocone : Cocone F :=
  colimit.cocone F

/--
The universal property of the thermodynamic limit: it is the initial cocone.
-/
noncomputable def ThermodynamicLimitIsColimit : IsColimit (ThermodynamicLimitCocone F) :=
  colimit.isColimit F

theorem thermodynamicLimit_desc_unique
    (t : Cocone F)
    (f : ThermodynamicLimit F ⟶ t.pt)
    (h : ∀ j,
      (ThermodynamicLimitCocone F).ι.app j ≫ f = t.ι.app j) :
    f = (ThermodynamicLimitIsColimit F).desc t := by
  exact (ThermodynamicLimitIsColimit F).uniq t f h

end InfoGeometry.Categorical
