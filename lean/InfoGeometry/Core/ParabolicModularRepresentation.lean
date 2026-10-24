/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.ParabolicShearRelations
import Mathlib.GroupTheory.PresentedGroup

/-!
# A native representation of the two-generator modular relations

This constructs the presented group and its homomorphism into ambient units.
It does not identify the presented group with SL(2,Z), or claim faithfulness
for an arbitrary ring pair. The concrete integral generation theorem is separate.
-/
namespace InfoGeometry.Core.ParabolicModularRepresentation

open InfoGeometry.Core.ParabolicShearRelations

/-- The relation set `s^4=1`, `s^2=u^3`. -/
def modularRelations : Set (FreeGroup Bool) :=
  {FreeGroup.of false ^ 4,
    FreeGroup.of false ^ 2 * (FreeGroup.of true ^ 3)⁻¹}

/-- Native quotient of the free group by the normal closure of the two relations. -/
abbrev ModularRelationsGroup := PresentedGroup modularRelations

/-- Assign false to the quartic generator and true to the sextic generator. -/
def generatorMap {G : Type*} (s u : G) : Bool → G := fun i => if i then u else s

/-- Extend any pair satisfying these relations by the universal property. -/
def ofRelations {G : Type*} [Group G] (s u : G)
    (hs : s ^ 4 = 1) (hsu : s ^ 2 = u ^ 3) : ModularRelationsGroup →* G :=
  PresentedGroup.toGroup (f := generatorMap s u) (by
    intro r hr
    rcases hr with rfl | hr
    · simpa [generatorMap] using hs
    · rcases hr with rfl
      simp [generatorMap, hsu])

@[simp] theorem ofRelations_s {G : Type*} [Group G] (s u : G)
    (hs : s ^ 4 = 1) (hsu : s ^ 2 = u ^ 3) :
    ofRelations s u hs hsu (PresentedGroup.of false) = s := by
  simp [ofRelations, generatorMap]

@[simp] theorem ofRelations_u {G : Type*} [Group G] (s u : G)
    (hs : s ^ 4 = 1) (hsu : s ^ 2 = u ^ 3) :
    ofRelations s u hs hsu (PresentedGroup.of true) = u := by
  simp [ofRelations, generatorMap]

variable {A : Type*} [Ring A] {d b : A}

/-- Native unit whose value is the ordered double shear. -/
def doubleUnit (hd : d * d = 0) (hb : b * b = 0) : Aˣ :=
  shearUnit d hd * (shearUnit b hb)⁻¹

/-- Native unit whose value is the ordered triple shear. -/
def tripleUnit (hd : d * d = 0) (hb : b * b = 0) : Aˣ :=
  doubleUnit hd hb * shearUnit d hd

@[simp] theorem doubleUnit_val (hd : d * d = 0) (hb : b * b = 0) :
    (doubleUnit hd hb : A) = doubleShear d b := rfl

@[simp] theorem tripleUnit_val (hd : d * d = 0) (hb : b * b = 0) :
    (tripleUnit hd hb : A) = tripleShear d b := rfl

/-- Both defining relations hold in the actual ambient unit group. -/
theorem unit_relations (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    tripleUnit hd hb ^ 4 = 1 ∧ tripleUnit hd hb ^ 2 = doubleUnit hd hb ^ 3 := by
  constructor
  · apply Units.ext
    change tripleShear d b ^ 4 = 1
    exact (power_relations hd hb hdb hbd).1
  · apply Units.ext
    change tripleShear d b ^ 2 = doubleShear d b ^ 3
    rw [triple_square hd hb hdb hbd, double_cube hd hb hdb hbd]

/-- The ring pair defines a group homomorphism, not merely a list of identities. -/
def representation (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) : ModularRelationsGroup →* Aˣ :=
  ofRelations (tripleUnit hd hb) (doubleUnit hd hb)
    (unit_relations hd hb hdb hbd).1 (unit_relations hd hb hdb hbd).2

/-- The common square/cube commutes with both generators. -/
theorem shared_sign_commutes (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) :
    Commute (tripleUnit hd hb ^ 2) (tripleUnit hd hb) ∧
    Commute (tripleUnit hd hb ^ 2) (doubleUnit hd hb) := by
  constructor
  · exact (Commute.refl _).pow_left 2
  · rw [(unit_relations hd hb hdb hbd).2]
    exact (Commute.refl _).pow_left 3

/-- The common sign commutes with every element in the represented group. -/
theorem sign_commutes_with_representation (hd : d * d = 0) (hb : b * b = 0)
    (hdb : d * b * d = d) (hbd : b * d * b = b) (g : ModularRelationsGroup) :
    Commute (tripleUnit hd hb ^ 2) (representation hd hb hdb hbd g) := by
  let C : Subgroup Aˣ :=
    { carrier := {x | Commute (tripleUnit hd hb ^ 2) x}
      one_mem' := Commute.one_right _
      mul_mem' := fun hx hy => hx.mul_right hy
      inv_mem' := fun hx => hx.inv_right }
  have hgen : ∀ i : Bool,
      (PresentedGroup.of i : ModularRelationsGroup) ∈
        C.comap (representation hd hb hdb hbd) := by
    intro i
    change Commute (tripleUnit hd hb ^ 2)
      (representation hd hb hdb hbd (PresentedGroup.of i))
    cases i
    · simpa [representation] using (shared_sign_commutes hd hb hdb hbd).1
    · simpa [representation] using (shared_sign_commutes hd hb hdb hbd).2
  exact PresentedGroup.generated_by modularRelations
    (C.comap (representation hd hb hdb hbd)) hgen g

end InfoGeometry.Core.ParabolicModularRepresentation
