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
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import InfoGeometry.Canonical.CategoryTheoryConeUniqueness
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Information.MasterArchetypeConvexDuality
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoGeometry.Categorical

/-- Type-level development-stage marker for a categorical construction.
It is a plain marker carrying no propositions; no declaration in this module
uses it as a proof carrier. -/
inductive ArchetypeStatus where
  | candidate
  | validated
  | proved
  deriving DecidableEq, Repr, Inhabited

/-!
# Categorical Data Structures and Native Theorems

Every mathematical statement in this module is a standalone Lean theorem proved over a
plain data structure. No proposition is stored in a structure field and no projection
discharges a proof on a caller's behalf.
-/

/-!
## 1. Colimit Cocone Apex Uniqueness
-/

/-- Data for a diagram and a pair of colimiting cocones in category C. -/
structure ColimitCoconePairDatum (C : Type u) [Category.{v} C] where
  {J : Type v}
  instJ : Category.{v} J
  F : J ⥤ C
  s : Cocone F
  t : Cocone F
  hs : IsColimit s
  ht : IsColimit t

/-- Trivial one-object category instance on `PUnit.{v + 1}` for witnessing `ColimitCoconePairDatum`. -/
instance punitCategory : Category.{v} PUnit.{v + 1} where
  Hom _ _ := PUnit.{v + 1}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- Constant cocone colimit witness on `PUnit.{1}` for `ColimitCoconePairDatum PUnit.{1}`. -/
def colimitCoconePairDatumPUnit : ColimitCoconePairDatum PUnit.{1} :=
  let F : PUnit.{1} ⥤ PUnit.{1} :=
    { obj := fun _ => PUnit.unit
      map := fun _ => PUnit.unit }
  let c : Cocone F :=
    { pt := PUnit.unit
      ι := { app := fun _ => PUnit.unit } }
  let hc : IsColimit c :=
    { desc := fun _ => PUnit.unit
      fac := fun _ _ => rfl
      uniq := fun _ _ _ => rfl }
  { J := PUnit.{1}
    instJ := punitCategory
    F := F
    s := c
    t := c
    hs := hc
    ht := hc }

instance : Inhabited (ColimitCoconePairDatum PUnit.{1}) :=
  ⟨colimitCoconePairDatumPUnit⟩

/-- Two colimiting cocones over the same diagram have mutually inverse apex isomorphisms. -/
theorem colimitCoconePairDatum_apex_inversePair {C : Type u} [Category.{v} C]
    (D : ColimitCoconePairDatum C) :
    let _ := D.instJ
    ∃ (f : D.s.pt ⟶ D.t.pt) (g : D.t.pt ⟶ D.s.pt),
      f ≫ g = 𝟙 D.s.pt ∧ g ≫ f = 𝟙 D.t.pt := by
  let _ := D.instJ
  exact InfoGeometry.Canonical.CategoryTheoryConeUniqueness.colimitCocone_apex_inversePair D.hs D.ht

/-!
## 2. Braided Monoidal Crossing
-/

/-- Data for a pair of objects in a braided monoidal category. -/
structure BraidedCrossingDatum (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] where
  X : C
  Y : C
  deriving Inhabited

/-- The braiding morphism is a left inverse of the braiding in the opposite order. -/
theorem braidedCrossingDatum_hom_inv_id {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] (D : BraidedCrossingDatum C) :
    (β_ D.X D.Y).hom ≫ (β_ D.X D.Y).inv = 𝟙 (D.X ⊗ D.Y) :=
  (β_ D.X D.Y).hom_inv_id

/-!
## 3. Grothendieck Group Completion
-/

/-- Data for an additive commutative monoid Grothendieck completion. -/
structure GrothendieckCompletionDatum where
  M : Type u
  instM : AddCommMonoid M

/-- Concrete `ℕ` model for `GrothendieckCompletionDatum`. -/
def grothendieckCompletionDatumNat : GrothendieckCompletionDatum :=
  ⟨ℕ, inferInstance⟩

instance instInhabitedGrothendieckCompletionDatum : Inhabited GrothendieckCompletionDatum :=
  ⟨grothendieckCompletionDatumNat⟩

/-- Every additive commutative monoid has an abelian group completion through which
every homomorphism into an abelian group factors uniquely. -/
theorem grothendieckCompletionDatum_lift_unique (D : GrothendieckCompletionDatum.{u}) :
    let _ := D.instM
    ∃ (G : Type u) (_ : AddCommGroup G) (f : D.M →+ G),
      ∀ (H : Type u) (_ : AddCommGroup H) (g : D.M →+ H),
        ∃! (u : G →+ H), u.comp f = g := by
  let _ := D.instM
  refine ⟨Grothendieck D.M, inferInstance, grothendieckMap D.M, ?_⟩
  intro H _instH g
  refine ⟨grothendieckLift g, ?_, ?_⟩
  · ext m
    exact grothendieckLift_comp g m
  · intro u hu
    ext x
    apply grothendieckLift_unique g u
    intro m
    have := congr_arg (fun (f : D.M →+ H) => f m) hu
    exact this

/-!
## 4. Convex Duality Pairing
-/

/-- Data for a real convex potential and primal/dual coordinates. -/
structure ConvexDualityDatum where
  psi : ℝ → ℝ
  theta : ℝ
  eta : ℝ

instance : Inhabited ConvexDualityDatum :=
  ⟨⟨fun _ => 0, 0, 0⟩⟩

/-- The Legendre–Fenchel pairing of a convex potential with its dual recovers the
moment coupling `psi theta + psi* theta eta = theta * eta`. -/
theorem convexDualityDatum_legendre_pairing (D : ConvexDualityDatum) :
    D.psi D.theta + InfoGeometry.Probability.FisherRaoMadelungIsometry.legendreDual D.psi D.theta D.eta =
      D.theta * D.eta :=
  InfoGeometry.Information.MasterArchetypeConvexDuality.universal_legendre_fenchel_pairing
    D.psi D.theta D.eta

/-!
## 5. Non-Commutative Operator Realization of `ArchetypeStatus` over `[Ring B]`
-/

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `ArchetypeStatus` stage
to its canonical Peirce operator in `[Ring B]`. -/
def archetypeStatusOperator (P A C : B) : ArchetypeStatus → B
  | .candidate => genPhi P A C
  | .validated => genJ P A C
  | .proved => genV P A C

/-- **Theorem (Non-Commutative Operator Realization of `ArchetypeStatus` over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the candidate
generator `Φ = a₊ + c₋` and validated generator `J = a₊ - c₋` anticommute (`{Φ, J} = 0`)
and square to the proved central operator `±V` (`Φ² = V`, `J² = -V`). -/
theorem archetypeStatus_operator_identities {P : B} (hP : P * P = P) (A C : B) :
    archetypeStatusOperator P A C .candidate *
      archetypeStatusOperator P A C .candidate =
      archetypeStatusOperator P A C .proved ∧
    archetypeStatusOperator P A C .validated *
      archetypeStatusOperator P A C .validated =
      -archetypeStatusOperator P A C .proved ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm
      (archetypeStatusOperator P A C .candidate)
      (archetypeStatusOperator P A C .validated) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (archetypeStatusOperator P A C .candidate)
      (archetypeStatusOperator P A C .validated) = -((2 : ℤ) • genSig P A C) := by
  dsimp only [archetypeStatusOperator]
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
    ⟨_, _, hPhiSq, hJSq, _, _, _, hAnti, _, _, _, _, _, _, _⟩
  exact ⟨hPhiSq, hJSq, hAnti,
    (archetype_A7_so12_lie_brackets_and_cubic_inversions (P := P) hP A C).1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Categorical
