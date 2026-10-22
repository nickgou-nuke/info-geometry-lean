/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Algebraic Operator Colimit Comparison

This file defines an algebraic observable carrier as the categorical direct colimit
in `RingCat` of a diagram of finite-stage algebras.

We define a functor `F : J ⥤ RingCat` (where `J` is the filtered poset of finite sub-regions)
and instantiate the carrier as `colimit F`. When a natural isomorphism to a
second diagram is supplied, Mathlib transports it across the colimit and exposes
the resulting stage-compatibility equations.

This file does not construct a von Neumann algebra, a commutant, or an analytic
Tomita--Takesaki modular flow.

## Audit Protocol Map

- **BUCKET 1: CLOSED CATEGORICAL THEOREMS**:
  - `tomita_takesaki_colimit_ι_hom` and `tomita_takesaki_colimit_ι_inv`:
    the canonical colimit comparison satisfies the exact stage triangles.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT DATA**:
  - `tomita_takesaki_colimit` is conditional on the supplied natural isomorphism
    `tomita_takesaki : F ≅ F_commutant`.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - Construction of the operator-algebraic commutant and analytic modular theory.
-/

namespace InfoGeometry.Categorical.OperatorAlgebraColimit

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J] [IsFiltered J]

-- The directed diagram of finite sub-region operator algebras.
variable (F : J ⥤ RingCat.{u})

/-- The infinite-dimensional observable algebra is the colimit of the finite sub-regions diagram. -/
noncomputable def infiniteObservableAlgebra [HasColimit F] : RingCat.{u} := colimit F

-- Functor representing the commutant (e.g., opposite ring) diagram of the finite sub-regions.
variable (F_commutant : J ⥤ RingCat.{u})

-- Tomita-Takesaki modular conjugation provides an isomorphism between the algebra
-- and its commutant for each finite sub-region.
variable (tomita_takesaki : F ≅ F_commutant)

/--
The commutant maps across the colimit: the Tomita-Takesaki reflection
extends to an isomorphism of the infinite-dimensional algebras.
-/
noncomputable def tomita_takesaki_colimit [HasColimit F] [HasColimit F_commutant] :
    infiniteObservableAlgebra F ≅ infiniteObservableAlgebra F_commutant :=
  HasColimit.isoOfNatIso tomita_takesaki

/-- The colimit comparison agrees with the finite-stage Tomita maps. -/
theorem tomita_takesaki_colimit_ι_hom
    [HasColimit F] [HasColimit F_commutant] (j : J) :
    colimit.ι F j ≫ (tomita_takesaki_colimit F F_commutant tomita_takesaki).hom =
      (tomita_takesaki.app j).hom ≫ colimit.ι F_commutant j := by
  exact HasColimit.ι_isoOfNatIso_hom tomita_takesaki j

/-- The inverse colimit comparison agrees with the inverse finite-stage maps. -/
theorem tomita_takesaki_colimit_ι_inv
    [HasColimit F] [HasColimit F_commutant] (j : J) :
    colimit.ι F_commutant j ≫ (tomita_takesaki_colimit F F_commutant tomita_takesaki).inv =
      (tomita_takesaki.app j).inv ≫ colimit.ι F j := by
  exact HasColimit.ι_isoOfNatIso_inv tomita_takesaki j

end InfoGeometry.Categorical.OperatorAlgebraColimit
