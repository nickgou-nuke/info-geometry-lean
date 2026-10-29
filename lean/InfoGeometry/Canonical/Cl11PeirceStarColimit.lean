/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanSingleSquare
import InfoGeometry.Core.PeirceStarNaturality
import InfoGeometry.Canonical.Cl11StarAlgebraDimension

/-!
# Peirce reflection and adjoint-square transport in the real matrix colimit

The carrier is the existing native direct limit of full real matrix algebras.
The identities commute with its faithful inclusions, tensor refinement, and
the universal star-algebra map. The generic single-square theorems also apply
directly to arbitrary elements of this ring, without a fixed stage hypothesis.

The quadratic coefficient remains an operator. These algebraic identities do
not supply an ordered completion or a scalar spectral lower bound.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11PeirceStarColimit

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.Core.PeirceStarNaturality
open InfoGeometry.Core.LieJordanSingleSquare
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower (stageEmbed)
open Cl11StarAlgebraColimit

local notation "ι" => ofStageStarAlgHom

theorem ofStage_component10_sq_zero (n : ℕ) {p : Stage n}
    (hp : IsIdempotentElem p) (x : Stage n) :
    (ι n (component10 p x)) ^ 2 = 0 := by
  rw [← map_pow]
  exact (congrArg (ι n) (corners_sq_zero hp x).1).trans (map_zero _)

theorem ofStage_component01_sq_zero (n : ℕ) {p : Stage n}
    (hp : IsIdempotentElem p) (x : Stage n) :
    (ι n (component01 p x)) ^ 2 = 0 := by
  rw [← map_pow]
  exact (congrArg (ι n) (corners_sq_zero hp x).2).trans (map_zero _)

theorem ofStage_sum_parity (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection (ι n p) * (ι n u + ι n v) * reflection (ι n p) =
      -(ι n u + ι n v) :=
  coupled_conjugation (hp.map (ι n))
    (map_mem_peirce10 (ι n).toAlgHom.toRingHom hu)
    (map_mem_peirce01 (ι n).toAlgHom.toRingHom hv)

theorem ofStage_difference_parity (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection (ι n p) * (ι n u - ι n v) * reflection (ι n p) =
      -(ι n u - ι n v) :=
  difference_conjugation (hp.map (ι n))
    (map_mem_peirce10 (ι n).toAlgHom.toRingHom hu)
    (map_mem_peirce01 (ι n).toAlgHom.toRingHom hv)

theorem ofStage_quadratic_parity (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection (ι n p) * (ι n u * ι n v + ι n v * ι n u) * reflection (ι n p) =
      ι n u * ι n v + ι n v * ι n u :=
  jordan_conjugation (hp.map (ι n))
    (map_mem_peirce10 (ι n).toAlgHom.toRingHom hu)
    (map_mem_peirce01 (ι n).toAlgHom.toRingHom hv)

theorem ofStage_bracket_parity (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection (ι n p) * ⁅ι n u, ι n v⁆ * reflection (ι n p) = ⁅ι n u, ι n v⁆ :=
  bracket_conjugation (hp.map (ι n))
    (map_mem_peirce10 (ι n).toAlgHom.toRingHom hu)
    (map_mem_peirce01 (ι n).toAlgHom.toRingHom hv)

theorem ofStage_reflection_quadratic (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection (ι n p) * (ι n u * ι n v + ι n v * ι n u) = ⁅ι n u, ι n v⁆ :=
  reflection_mul_jordan (hp.map (ι n))
    (map_mem_peirce10 (ι n).toAlgHom.toRingHom hu)
    (map_mem_peirce01 (ι n).toAlgHom.toRingHom hv)

/-- The star-square identity holds inside the actual limit star ring. -/
theorem ofStage_reflected_star_anticommutator (n : ℕ) {p u : Stage n}
    (hp : IsStarProjection p) (hu : u ∈ peirce10 p) :
    -((reflection (ι n p) * star (ι n u) * reflection (ι n p)) * ι n u +
        ι n u * (reflection (ι n p) * star (ι n u) * reflection (ι n p))) =
      ι n u * star (ι n u) + star (ι n u) * ι n u :=
  reflected_star_anticommutator (hp.map (ι n))
    (map_mem_peirce10 (ι n).toAlgHom.toRingHom hu)

theorem ofStage_neg_ad_sum_sq (n : ℕ) (u v x : Stage n) :
    ι n ((-(LieAlgebra.ad ℝ (Stage n) (u + v) ^ 2)) x) =
      (-(LieAlgebra.ad ℝ Limit (ι n u + ι n v) ^ 2)) (ι n x) :=
  map_neg_ad_sum_sq (ι n).toAlgHom u v x

theorem ofStage_ad_sub_sq (n : ℕ) (u v x : Stage n) :
    ι n ((LieAlgebra.ad ℝ (Stage n) (u - v) ^ 2) x) =
      (LieAlgebra.ad ℝ Limit (ι n u - ι n v) ^ 2) (ι n x) :=
  map_ad_sub_sq (ι n).toAlgHom u v x

/-- Refinement compatibility compares the two actual stage expressions. -/
theorem neg_ad_sum_sq_refinement (n : ℕ) (u v x : Stage n) :
    ι (n + 1) ((-(LieAlgebra.ad ℝ (Stage (n + 1))
        (stageEmbed n u + stageEmbed n v) ^ 2)) (stageEmbed n x)) =
      ι n ((-(LieAlgebra.ad ℝ (Stage n) (u + v) ^ 2)) x) := by
  rw [← map_neg_ad_sum_sq (stageEmbed n), ofStageStarAlgHom_bond]

theorem ad_sub_sq_refinement (n : ℕ) (u v x : Stage n) :
    ι (n + 1) ((LieAlgebra.ad ℝ (Stage (n + 1))
        (stageEmbed n u - stageEmbed n v) ^ 2) (stageEmbed n x)) =
      ι n ((LieAlgebra.ad ℝ (Stage n) (u - v) ^ 2) x) := by
  rw [← map_ad_sub_sq (stageEmbed n), ofStageStarAlgHom_bond]

/-- A compatible family on an arbitrary cofinal tail defines one adjoint-square
endomorphism on the whole limit. Its seed belongs to the full stage `m`. -/
theorem existsUnique_neg_ad_sum_sq
    (m : ℕ) (u v : ∀ n, Stage (m + n))
    (hu : ∀ n, stageEmbed (m + n) (u n) = u (n + 1))
    (hv : ∀ n, stageEmbed (m + n) (v n) = v (n + 1)) :
    ∃! D : Module.End ℝ Limit, ∀ n x,
      D (ι (m + n) x) =
        ι (m + n) ((-(LieAlgebra.ad ℝ (Stage (m + n)) (u n + v n) ^ 2)) x) := by
  have hU := ofStageStarAlgHom_tail_eq m u hu
  have hV := ofStageStarAlgHom_tail_eq m v hv
  refine ⟨-(LieAlgebra.ad ℝ Limit (ι m (u 0) + ι m (v 0)) ^ 2), ?_, ?_⟩
  · intro n x
    rw [ofStage_neg_ad_sum_sq, hU n, hV n]
  · intro D hD
    apply LinearMap.ext
    intro z
    induction z using DirectLimit.induction with
    | _ k x =>
        change D (ι k x) =
          (-(LieAlgebra.ad ℝ Limit (ι m (u 0) + ι m (v 0)) ^ 2)) (ι k x)
        have hx := ofStageStarAlgHom_bondMap k (m + k) (by omega) x
        rw [← hx, hD, ofStage_neg_ad_sum_sq, hU k, hV k]

theorem existsUnique_ad_sub_sq
    (m : ℕ) (u v : ∀ n, Stage (m + n))
    (hu : ∀ n, stageEmbed (m + n) (u n) = u (n + 1))
    (hv : ∀ n, stageEmbed (m + n) (v n) = v (n + 1)) :
    ∃! D : Module.End ℝ Limit, ∀ n x,
      D (ι (m + n) x) =
        ι (m + n) ((LieAlgebra.ad ℝ (Stage (m + n)) (u n - v n) ^ 2) x) := by
  have hU := ofStageStarAlgHom_tail_eq m u hu
  have hV := ofStageStarAlgHom_tail_eq m v hv
  refine ⟨LieAlgebra.ad ℝ Limit (ι m (u 0) - ι m (v 0)) ^ 2, ?_, ?_⟩
  · intro n x
    rw [ofStage_ad_sub_sq, hU n, hV n]
  · intro D hD
    apply LinearMap.ext
    intro z
    induction z using DirectLimit.induction with
    | _ k x =>
        change D (ι k x) =
          (LieAlgebra.ad ℝ Limit (ι m (u 0) - ι m (v 0)) ^ 2) (ι k x)
        have hx := ofStageStarAlgHom_bondMap k (m + k) (by omega) x
        rw [← hx, hD, ofStage_ad_sub_sq, hU k, hV k]

section Universal

variable {B : Type} [Ring B] [StarRing B] [Algebra ℝ B]
    (g : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hg : ∀ n x, g (n + 1) (stageEmbed n x) = g n x)

/-- The compatible cone is consumed by the genuine universal lift. -/
theorem lift_neg_ad_sum_sq (n : ℕ) (u v x : Stage n) :
    liftStarAlgHom g hg
        ((-(LieAlgebra.ad ℝ Limit (ι n u + ι n v) ^ 2)) (ι n x)) =
      (-(LieAlgebra.ad ℝ B (g n u + g n v) ^ 2)) (g n x) := by
  rw [← ofStage_neg_ad_sum_sq, liftStarAlgHom_of]
  exact map_neg_ad_sum_sq (g n).toAlgHom u v x

theorem lift_ad_sub_sq (n : ℕ) (u v x : Stage n) :
    liftStarAlgHom g hg
        ((LieAlgebra.ad ℝ Limit (ι n u - ι n v) ^ 2) (ι n x)) =
      (LieAlgebra.ad ℝ B (g n u - g n v) ^ 2) (g n x) := by
  rw [← ofStage_ad_sub_sq, liftStarAlgHom_of]
  exact map_ad_sub_sq (g n).toAlgHom u v x

end Universal

end InfoGeometry.Canonical.Cl11PeirceStarColimit
