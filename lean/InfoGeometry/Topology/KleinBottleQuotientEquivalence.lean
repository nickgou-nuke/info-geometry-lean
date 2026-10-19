/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleOrbitQuotient

/-!
# Equivalent quotient presentations of the Klein orbit carrier

The orbit relation for the involutive torus glide is already an equivalence
relation.  This file records, constructively, that replacing its one-step
presentation by the reflexive-symmetric-transitive closure does not change the
quotient carrier.  The resulting equivalence is the canonical comparison map
between the two quotient presentations.
-/

noncomputable section

namespace KleinBottleOrbitQuotient

open KleinBrillouinBase

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Mathlib's canonical compact interval presentation of the momentum circle. -/
def momentumCircleIccHomeo :
    MomentumCircle ≃ₜ Quot (AddCircle.EndpointIdent (2 * Real.pi) 0) := by
  exact AddCircle.homeoIccQuot (2 * Real.pi) 0

/-- The torus carrier admits the corresponding product presentation. -/
def brillouinTorusIccEquiv :
    BrillouinTorus ≃ Quot (AddCircle.EndpointIdent (2 * Real.pi) 0) × MomentumCircle :=
  Equiv.prodCongr momentumCircleIccHomeo.toEquiv (Equiv.refl MomentumCircle)


/-- The one-step glide relation, viewed independently of the quotient setoid. -/
def glideStep (x y : BrillouinTorus) : Prop :=
  y = x ∨ y = torusGlide x

/-- The reflexive-symmetric-transitive closure of the one-step glide relation. -/
def glideGeneratedSetoid : Setoid BrillouinTorus where
  r := Relation.EqvGen glideStep
  iseqv := Relation.EqvGen.is_equivalence glideStep

private theorem glideStep_iff_glideSetoid (x y : BrillouinTorus) :
    glideStep x y ↔ glideSetoid.r x y := by
  rfl

private theorem glideGenerated_iff_glide (x y : BrillouinTorus) :
    @Setoid.r BrillouinTorus glideGeneratedSetoid x y ↔
      glideSetoid.r x y := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
        rcases hab with rfl | hab
        · exact Or.inl rfl
        · exact Or.inr hab
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
        rcases ih with rfl | h
        · exact Or.inl rfl
        · right
          rw [h, torusGlide_involutive]
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | h₁
        · exact ih₂
        · rcases ih₂ with rfl | h₂
          · exact Or.inr h₁
          · left
            rw [h₂, h₁, torusGlide_involutive]
  · intro h
    exact Relation.EqvGen.rel _ _ h

/-- The quotient comparison induced by the identity on the torus. -/
def generatedToOrbit :
    Quotient glideGeneratedSetoid ≃ KleinBrillouinQuotient where
  toFun := Quotient.lift (@Quotient.mk BrillouinTorus glideSetoid)
    (by
      intro x y h
      apply Quotient.sound
      exact (glideGenerated_iff_glide x y).mp h)
  invFun := Quotient.lift (@Quotient.mk BrillouinTorus glideGeneratedSetoid)
    (by
      intro x y h
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ ((glideStep_iff_glideSetoid x y).mpr h))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

@[simp] theorem generatedToOrbit_apply (x : BrillouinTorus) :
    generatedToOrbit (@Quotient.mk BrillouinTorus glideGeneratedSetoid x) = quotientMap x :=
  rfl

/-- The comparison is exactly compatible with the canonical projection maps. -/
theorem generatedToOrbit_comp_mk :
    generatedToOrbit ∘ (@Quotient.mk BrillouinTorus glideGeneratedSetoid) =
      quotientMap := by
  funext x
  rfl

end KleinBottleOrbitQuotient

end noncomputable section
