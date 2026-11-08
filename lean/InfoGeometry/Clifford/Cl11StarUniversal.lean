/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import Mathlib.Algebra.Star.StarAlgHom

/-!
# The real star-algebra universal property of the existing matrix tower

The carrier is `Cl11TensorTowerLimit.Limit`, the existing noncommutative
`DirectLimit` quotient of the real matrix tensor tower. Its ring operations,
real scalar action, involution and universal ring lift are reused unchanged.
The maps below expose the stronger native `StarAlgHom` universal property.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11StarUniversal

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The existing finite-stage inclusion preserves the real algebra and star. -/
def ofStageStarAlgHom (n : ℕ) : Stage n →⋆ₐ[ℝ] Limit where
  toAlgHom :=
    { ofStage n with
      commutes' := by
        intro r
        change ofStage n (algebraMap ℝ (Stage n) r) = realAlgebraMap r
        exact (realAlgebraMap_stage n r).symm }
  map_star' := ofStage_star n

@[simp]
theorem ofStageStarAlgHom_apply (n : ℕ) (x : Stage n) :
    ofStageStarAlgHom n x = ofStage n x := rfl

/-- The canonical star-algebra maps respect the actual tensor bonding maps. -/
theorem ofStageStarAlgHom_bond (n : ℕ) (x : Stage n) :
    ofStageStarAlgHom (n + 1) (stageEmbed n x) = ofStageStarAlgHom n x :=
  ofStage_apply_bond n x

/-- Faithful tensor bonding maps make every canonical inclusion injective. -/
theorem ofStageStarAlgHom_injective (n : ℕ) :
    Function.Injective (ofStageStarAlgHom n) := by
  change Function.Injective (directLimitOf stageBond n)
  apply directLimitOf_injective stageBond
  intro k
  change Function.Injective (matStageEmbed k)
  exact matStageEmbed_injective k

variable {B : Type} [Ring B] [StarRing B] [Algebra ℝ B]

/-- Star-algebra homomorphisms out of the quotient are determined on stages. -/
@[ext]
theorem hom_ext {g h : Limit →⋆ₐ[ℝ] B}
    (heq : ∀ n, g.comp (ofStageStarAlgHom n) = h.comp (ofStageStarAlgHom n)) :
    g = h := by
  apply StarAlgHom.ext
  intro x
  induction x using DirectLimit.induction with
  | _ n x => exact DFunLike.congr_fun (heq n) x

/-- The existing universal ring lift is also real-linear and star-preserving. -/
def lift (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hf : ∀ n x, f (n + 1) (stageEmbed n x) = f n x) :
    Limit →⋆ₐ[ℝ] B where
  toAlgHom :=
    { directLimitLift stageBond (fun n => (f n).toAlgHom.toRingHom) hf with
      commutes' := by
        intro r
        change f 0 (algebraMap ℝ (Stage 0) r) = algebraMap ℝ B r
        exact (f 0).toAlgHom.commutes r }
  map_star' := by
    intro x
    induction x using DirectLimit.induction with
    | _ n x =>
        change f n (star x) = star (f n x)
        exact map_star (f n) x

@[simp]
theorem lift_of (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hf : ∀ n x, f (n + 1) (stageEmbed n x) = f n x)
    (n : ℕ) (x : Stage n) :
    lift f hf (ofStageStarAlgHom n x) = f n x := rfl

/-- The universal map factors every component of the compatible family. -/
@[simp]
theorem lift_comp (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hf : ∀ n x, f (n + 1) (stageEmbed n x) = f n x) (n : ℕ) :
    (lift f hf).comp (ofStageStarAlgHom n) = f n := by
  ext x
  rfl

/-- Factorization on finite stages determines the universal map uniquely. -/
theorem lift_unique (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hf : ∀ n x, f (n + 1) (stageEmbed n x) = f n x)
    (g : Limit →⋆ₐ[ℝ] B)
    (hg : ∀ n, g.comp (ofStageStarAlgHom n) = f n) :
    g = lift f hf := by
  apply hom_ext
  intro n
  rw [hg n, lift_comp]

/-- Existence and uniqueness in the category of real unital star algebras. -/
theorem existsUnique_lift (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hf : ∀ n x, f (n + 1) (stageEmbed n x) = f n x) :
    ∃! g : Limit →⋆ₐ[ℝ] B, ∀ n, g.comp (ofStageStarAlgHom n) = f n := by
  exact ⟨lift f hf, lift_comp f hf, fun g hg => lift_unique f hf g hg⟩

/-- Compatibility is exactly the condition for unique star-algebra descent. -/
theorem existsUnique_lift_iff (f : ∀ n, Stage n →⋆ₐ[ℝ] B) :
    (∃! g : Limit →⋆ₐ[ℝ] B, ∀ n, g.comp (ofStageStarAlgHom n) = f n) ↔
      ∀ n x, f (n + 1) (stageEmbed n x) = f n x := by
  constructor
  · rintro ⟨g, hg, _⟩ n x
    calc
      f (n + 1) (stageEmbed n x) =
          g (ofStageStarAlgHom (n + 1) (stageEmbed n x)) :=
        (DFunLike.congr_fun (hg (n + 1)) (stageEmbed n x)).symm
      _ = g (ofStageStarAlgHom n x) :=
        congrArg g (ofStageStarAlgHom_bond n x)
      _ = f n x := DFunLike.congr_fun (hg n) x
  · exact existsUnique_lift f

end InfoGeometry.Clifford.Cl11StarUniversal
