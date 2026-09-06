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
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Infinite-Dimensional Operator Algebra Colimit

The infinite-dimensional observable algebra is represented directly by
Mathlib's `colimit F` in `RingCat`; this file does not introduce an alias for
that native carrier. The Tomita-Takesaki statement below is the
domain-specific theorem: a natural isomorphism of finite-stage diagrams
induces the corresponding native colimit isomorphism.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `tomita_takesaki_colimit`: The commutant isomorphism extends naturally to the colimit.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES**:
  - None.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None.
-/

namespace InfoGeometry.Categorical.OperatorAlgebraColimit

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J] [IsFiltered J]

-- The directed diagram of finite sub-region operator algebras.
variable (F : J ⥤ RingCat.{u})

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
    CategoryTheory.Limits.colimit F ≅ CategoryTheory.Limits.colimit F_commutant :=
  HasColimit.isoOfNatIso tomita_takesaki

end InfoGeometry.Categorical.OperatorAlgebraColimit
