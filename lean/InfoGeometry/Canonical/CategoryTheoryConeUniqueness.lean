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
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Cone Uniqueness for Limits and Colimits

This file records the mathlib-native cone information used by the categorical
direct-limit lanes in the repository.  A limiting cone over a fixed diagram has
an apex unique up to mutually inverse morphisms, and the dual statement holds
for colimiting cocones.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `limitCone_apex_inversePair`: limiting cones over the same diagram have
    mutually inverse apex morphisms.
  - `colimitCocone_apex_inversePair`: colimiting cocones over the same diagram
    have mutually inverse apex morphisms.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES**:
  - None.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None.
-/

namespace InfoGeometry.Canonical.CategoryTheoryConeUniqueness

open CategoryTheory
open CategoryTheory.Limits

universe vJ vC uJ uC

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Limiting cones over the same diagram have mutually inverse apex morphisms. -/
theorem limitCone_apex_inversePair {F : J ⥤ C} {s t : Cone F}
    (hs : IsLimit s) (ht : IsLimit t) :
    ∃ (f : s.pt ⟶ t.pt) (g : t.pt ⟶ s.pt),
      f ≫ g = 𝟙 s.pt ∧ g ≫ f = 𝟙 t.pt := by
  refine ⟨(IsLimit.conePointUniqueUpToIso hs ht).hom,
    (IsLimit.conePointUniqueUpToIso hs ht).inv, ?_, ?_⟩
  · simp
  · simp

/-- Colimiting cocones over the same diagram have mutually inverse apex morphisms. -/
theorem colimitCocone_apex_inversePair {F : J ⥤ C} {s t : Cocone F}
    (hs : IsColimit s) (ht : IsColimit t) :
    ∃ (f : s.pt ⟶ t.pt) (g : t.pt ⟶ s.pt),
      f ≫ g = 𝟙 s.pt ∧ g ≫ f = 𝟙 t.pt := by
  refine ⟨(IsColimit.coconePointUniqueUpToIso hs ht).hom,
    (IsColimit.coconePointUniqueUpToIso hs ht).inv, ?_, ?_⟩
  · simp
  · simp

end InfoGeometry.Canonical.CategoryTheoryConeUniqueness
