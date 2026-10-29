/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import Mathlib.Algebra.Star.StarAlgHom

/-!
# Universal real star-algebra maps on the full matrix tensor limit

The carrier is exactly `Cl11TensorTowerLimit.Limit`. Its existing algebra
inclusions preserve star and are faithful. The existing universal ring map
therefore bundles as a native real `StarAlgHom`, uniquely determined by its
finite-stage values. Targets are in `Type`, matching the universe of the
existing one-step ring universal property.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11StarAlgebraColimit

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- The existing canonical inclusion as a native real star-algebra map. -/
def ofStageStarAlgHom (n : ℕ) : Stage n →⋆ₐ[ℝ] Limit :=
  { Cl11TensorInductiveLimit.ofStageAlgHom n with
    map_star' := ofStage_star n }

@[simp] theorem ofStageStarAlgHom_apply (n : ℕ) (x : Stage n) :
    ofStageStarAlgHom n x = ofStage n x := rfl

/-- Canonical star-algebra inclusions respect one tensor refinement. -/
@[simp] theorem ofStageStarAlgHom_bond (n : ℕ) (x : Stage n) :
    ofStageStarAlgHom (n + 1) (stageEmbed n x) = ofStageStarAlgHom n x :=
  ofStage_apply_bond n x

/-- Canonical inclusions identify every later representative of a stage element. -/
theorem ofStageStarAlgHom_bondMap (m n : ℕ) (h : m ≤ n) (x : Stage m) :
    ofStageStarAlgHom n (bondMap stageBond m n h x) = ofStageStarAlgHom m x :=
  directLimitOf_bondMap stageBond m n h x

/-- A compatible family on a cofinal tail has the image of its full-matrix seed. -/
theorem ofStageStarAlgHom_tail_eq (m : ℕ) (u : ∀ n, Stage (m + n))
    (hu : ∀ n, stageEmbed (m + n) (u n) = u (n + 1)) (n : ℕ) :
    ofStageStarAlgHom (m + n) (u n) = ofStageStarAlgHom m (u 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← hu n]
      exact (ofStageStarAlgHom_bond (m + n) (u n)).trans ih

/-- Every full matrix stage embeds faithfully in the existing real limit. -/
theorem ofStageStarAlgHom_injective (n : ℕ) :
    Function.Injective (ofStageStarAlgHom n) := by
  change Function.Injective (directLimitOf stageBond n)
  exact directLimitOf_injective stageBond (fun k => matStageEmbed_injective k) n

@[simp] theorem ofStageStarAlgHom_eq_zero_iff (n : ℕ) (x : Stage n) :
    ofStageStarAlgHom n x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply ofStageStarAlgHom_injective n
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero (ofStageStarAlgHom n)

/-- A nonzero matrix remains nonzero in the algebraic limit. -/
theorem ofStageStarAlgHom_ne_zero_iff (n : ℕ) (x : Stage n) :
    ofStageStarAlgHom n x ≠ 0 ↔ x ≠ 0 :=
  not_congr (ofStageStarAlgHom_eq_zero_iff n x)

/-- The canonical stage inclusion reflects as well as preserves commutation. -/
theorem ofStageStarAlgHom_commute_iff (n : ℕ) (x y : Stage n) :
    Commute (ofStageStarAlgHom n x) (ofStageStarAlgHom n y) ↔ Commute x y := by
  change (ofStageStarAlgHom n x * ofStageStarAlgHom n y =
    ofStageStarAlgHom n y * ofStageStarAlgHom n x) ↔ x * y = y * x
  rw [← map_mul (ofStageStarAlgHom n), ← map_mul (ofStageStarAlgHom n)]
  exact (ofStageStarAlgHom_injective n).eq_iff

/-- Canonical inclusions preserve the native associative-ring Lie bracket. -/
theorem ofStageStarAlgHom_lie (n : ℕ) (x y : Stage n) :
    ofStageStarAlgHom n ⁅x, y⁆ =
      ⁅ofStageStarAlgHom n x, ofStageStarAlgHom n y⁆ := by
  change ofStageStarAlgHom n (x * y - y * x) =
    ofStageStarAlgHom n x * ofStageStarAlgHom n y -
      ofStageStarAlgHom n y * ofStageStarAlgHom n x
  rw [map_sub, map_mul, map_mul]

/-- A native finite-stage commutator is nonzero exactly when its image is. -/
theorem ofStageStarAlgHom_lie_ne_zero_iff (n : ℕ) (x y : Stage n) :
    ⁅ofStageStarAlgHom n x, ofStageStarAlgHom n y⁆ ≠ 0 ↔ ⁅x, y⁆ ≠ 0 := by
  rw [← ofStageStarAlgHom_lie n x y]
  exact ofStageStarAlgHom_ne_zero_iff n ⁅x, y⁆

section UniversalProperty

variable {B : Type} [Ring B] [StarRing B] [Algebra ℝ B]

/-- The universal real star-algebra map induced by compatible stage maps. -/
def liftStarAlgHom
    (g : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hg : ∀ n (x : Stage n), g (n + 1) (stageEmbed n x) = g n x) :
    Limit →⋆ₐ[ℝ] B where
  toFun := directLimitLift stageBond (fun n => (g n).toAlgHom.toRingHom) hg
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := by
    intro r
    change directLimitLift stageBond (fun n => (g n).toAlgHom.toRingHom) hg
      (realAlgebraMap r) = algebraMap ℝ B r
    rw [realAlgebraMap_stage 0 r]
    change g 0 (algebraMap ℝ (Stage 0) r) = algebraMap ℝ B r
    exact (g 0).commutes r
  map_star' := by
    intro z
    induction z using DirectLimit.induction with
    | _ n x =>
        rw [limit_star_mk]
        change g n (star x) = star (g n x)
        exact map_star (g n) x

@[simp] theorem liftStarAlgHom_of
    (g : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hg : ∀ n (x : Stage n), g (n + 1) (stageEmbed n x) = g n x)
    (n : ℕ) (x : Stage n) :
    liftStarAlgHom g hg (ofStageStarAlgHom n x) = g n x := rfl

/-- The native star-algebra lift is unique by the existing ring universal property. -/
theorem liftStarAlgHom_unique
    (g : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hg : ∀ n (x : Stage n), g (n + 1) (stageEmbed n x) = g n x)
    (F : Limit →⋆ₐ[ℝ] B)
    (hF : ∀ n, F.comp (ofStageStarAlgHom n) = g n) :
    F = liftStarAlgHom g hg := by
  have hring : F.toAlgHom.toRingHom =
      directLimitLift stageBond (fun n => (g n).toAlgHom.toRingHom) hg := by
    apply directLimitLift_unique stageBond (fun n => (g n).toAlgHom.toRingHom) hg
    intro n
    ext x
    exact DFunLike.congr_fun (hF n) x
  apply StarAlgHom.ext
  intro x
  exact DFunLike.congr_fun hring x

/-- Compatible real star-algebra maps extend uniquely from all full matrix stages. -/
theorem existsUnique_liftStarAlgHom
    (g : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hg : ∀ n (x : Stage n), g (n + 1) (stageEmbed n x) = g n x) :
    ∃! F : Limit →⋆ₐ[ℝ] B, ∀ n, F.comp (ofStageStarAlgHom n) = g n := by
  refine ⟨liftStarAlgHom g hg, ?_, ?_⟩
  · intro n
    apply StarAlgHom.ext
    intro x
    exact liftStarAlgHom_of g hg n x
  · intro F hF
    exact liftStarAlgHom_unique g hg F hF

end UniversalProperty

end InfoGeometry.Canonical.Cl11StarAlgebraColimit
