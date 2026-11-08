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

import InfoGeometry.Categorical.TypedCategoryArchetype

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoGeometry.Categorical

/-!
# Concrete Instances of Categorical Data Theorems

This module is a thin compatibility surface that exposes the native theorems proved in
`InfoGeometry.Categorical.TypedCategoryArchetype` under the historical instance names:
1. `discharge_colimit`: apex isomorphism uniqueness for direct limits.
2. `discharge_braided`: crossing invertibility in braided monoidal categories.
3. `discharge_grothendieck`: universal factoring through Grothendieck group completions.
4. `discharge_convex_duality`: Legendre–Fenchel moment pairing.
-/

section Colimit
variable {C : Type u} [Category.{v} C]

/-- Apex isomorphism uniqueness for a pair of colimiting cocones over one diagram. -/
theorem discharge_colimit (D : ColimitCoconePairDatum C) :
    let _ := D.instJ
    ∃ (f : D.s.pt ⟶ D.t.pt) (g : D.t.pt ⟶ D.s.pt),
      f ≫ g = 𝟙 D.s.pt ∧ g ≫ f = 𝟙 D.t.pt :=
  colimitCoconePairDatum_apex_inversePair D

end Colimit

section Braided
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Crossing invertibility in a braided monoidal category. -/
theorem discharge_braided (D : BraidedCrossingDatum C) :
    (β_ D.X D.Y).hom ≫ (β_ D.X D.Y).inv = 𝟙 (D.X ⊗ D.Y) :=
  braidedCrossingDatum_hom_inv_id D

end Braided

section Grothendieck

/-- Universal factoring through the Grothendieck group completion. -/
theorem discharge_grothendieck (D : GrothendieckCompletionDatum.{u}) :
    let _ := D.instM
    ∃ (G : Type u) (_ : AddCommGroup G) (f : D.M →+ G),
      ∀ (H : Type u) (_ : AddCommGroup H) (g : D.M →+ H),
        ∃! (u : G →+ H), u.comp f = g :=
  grothendieckCompletionDatum_lift_unique D

end Grothendieck

section Convex

/-- Legendre–Fenchel moment pairing for a convex potential. -/
theorem discharge_convex_duality (D : ConvexDualityDatum) :
    D.psi D.theta + InfoGeometry.Probability.FisherRaoMadelungIsometry.legendreDual D.psi D.theta D.eta =
      D.theta * D.eta :=
  convexDualityDatum_legendre_pairing D

end Convex

end InfoGeometry.Categorical
