/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11TensorTowerLimit
import Mathlib.Algebra.Star.StarAlgHom

/-!
# The universal real star-algebra map of the full matrix tower

The carrier, ring structure, real scalar action, and star are the existing
`Cl11TensorTowerLimit` structures. The ring universal map is upgraded by proving
its scalar and star laws. No compatibility-only cocone is declared universal.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11StarAlgebraColimit

open Cl11TensorTower Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The existing faithful stage map, with its real algebra and star laws bundled. -/
def ofStageStarAlgHom (n : ℕ) : Stage n →⋆ₐ[ℝ] Limit where
  toRingHom := ofStage n
  commutes' r := (realAlgebraMap_stage n r).symm
  map_star' := ofStage_star n

@[simp] theorem ofStageStarAlgHom_apply (n : ℕ) (A : Stage n) :
    ofStageStarAlgHom n A = ofStage n A := rfl

/-- The existing quotient star respects the existing real scalar action. -/
instance limitStarModule : StarModule ℝ Limit where
  star_smul r x := by
    induction x using DirectLimit.induction with
    | _ n A =>
      change star (r • ofStageStarAlgHom n A) =
        star r • star (ofStageStarAlgHom n A)
      rw [← map_smul (ofStageStarAlgHom n) r A, ← map_star,
        star_smul, map_smul, map_star]

theorem ofStage_injective (n : ℕ) : Function.Injective (ofStage n) :=
  directLimitOf_injective stageBond (fun k => matStageEmbed_injective k) n

theorem ofStageStarAlgHom_injective (n : ℕ) :
    Function.Injective (ofStageStarAlgHom n) := ofStage_injective n

@[simp] theorem ofStage_eq_zero_iff (n : ℕ) (A : Stage n) :
    ofStage n A = 0 ↔ A = 0 := by
  rw [← map_zero (ofStage n), (ofStage_injective n).eq_iff]

section Universal

variable {B : Type} [Ring B] [Algebra ℝ B] [StarRing B]
variable (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
variable (hf : ∀ n A, f (n + 1) (stageEmbed n A) = f n A)

/-- The universal map is the existing ring lift, with the two additional laws proved. -/
def lift : Limit →⋆ₐ[ℝ] B where
  toRingHom := directLimitLift stageBond (fun n => (f n).toAlgHom.toRingHom) hf
  commutes' r := by
    change directLimitLift stageBond (fun n => (f n).toAlgHom.toRingHom) hf
      (ofStage 0 (algebraMap ℝ (Stage 0) r)) = algebraMap ℝ B r
    exact (f 0).commutes r
  map_star' x := by
    induction x using DirectLimit.induction with
    | _ n A =>
      change f n (star A) = star (f n A)
      exact map_star (f n) A

@[simp] theorem lift_ofStage (n : ℕ) (A : Stage n) :
    lift f hf (ofStage n A) = f n A := rfl

/-- Star-algebra maps from the quotient are determined on the actual matrix stages. -/
@[ext] theorem hom_ext {g h : Limit →⋆ₐ[ℝ] B}
    (hstage : ∀ n A, g (ofStage n A) = h (ofStage n A)) : g = h := by
  ext x
  induction x using DirectLimit.induction with
  | _ n A => exact hstage n A

theorem lift_unique (g : Limit →⋆ₐ[ℝ] B)
    (hg : ∀ n A, g (ofStage n A) = f n A) : g = lift f hf := by
  apply hom_ext
  intro n A
  exact hg n A

include hf in
/-- Existence and uniqueness are proved, rather than stored in a supplied cone. -/
theorem existsUnique_lift :
    ∃! g : Limit →⋆ₐ[ℝ] B, ∀ n A, g (ofStage n A) = f n A := by
  refine ⟨lift f hf, lift_ofStage f hf, ?_⟩
  intro g hg
  exact lift_unique f hf g hg

/-- Faithfulness of the induced representation is exactly faithfulness at every stage. -/
theorem lift_injective_iff :
    Function.Injective (lift f hf) ↔ ∀ n, Function.Injective (f n) := by
  constructor
  · intro h n A B hAB
    apply ofStage_injective n
    apply h
    exact hAB
  · intro h x y
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
      intro hAB
      exact congrArg (ofStage n) (h n hAB)

/-- Surjectivity requires every target operator to be represented at a finite stage. -/
theorem lift_surjective_iff :
    Function.Surjective (lift f hf) ↔ ∀ b, ∃ n A, f n A = b := by
  constructor
  · intro h b
    obtain ⟨x, hx⟩ := h b
    induction x using DirectLimit.induction with
    | _ n A => exact ⟨n, A, hx⟩
  · intro h b
    obtain ⟨n, A, hA⟩ := h b
    exact ⟨ofStage n A, hA⟩

end Universal

end InfoGeometry.Clifford.Cl11StarAlgebraColimit
