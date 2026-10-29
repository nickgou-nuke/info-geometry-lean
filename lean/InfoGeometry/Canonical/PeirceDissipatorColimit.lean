/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDoubleCommutator
import InfoGeometry.Clifford.Cl11StarUniversal

/-!
# Exact Peirce actions in the real matrix tensor colimit

Native squared adjoint actions intertwine with algebra homomorphisms. For the
existing faithful real tensor inclusions, their weighted equations and zero
sets are reflected as well as preserved. The reflected Gram expression and
the two opposite-corner mode equations are evaluated in the actual quotient.
-/

namespace InfoGeometry.Canonical.PeirceDissipatorColimit

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners InfoGeometry.Core.PeirceSandwichDuality
open InfoGeometry.Core.PeirceDoubleCommutator
open InfoGeometry.Clifford.Cl11TensorTowerLimit InfoGeometry.Clifford.Cl11StarUniversal

attribute [local instance 100] LieRing.ofAssociativeRing

section Naturality

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- Naturality of the native squared inner action, with no commutativity assumptions. -/
theorem map_ad_sq (f : A →ₐ[R] B) (a x : A) :
    f ((LieAlgebra.ad R A a ^ 2) x) =
      (LieAlgebra.ad R B (f a) ^ 2) (f x) := by
  simp only [pow_two, Module.End.mul_apply, LieAlgebra.ad_apply, Ring.lie_def,
    map_sub, map_mul]

theorem map_neg_ad_sq (f : A →ₐ[R] B) (a x : A) :
    f ((-(LieAlgebra.ad R A a ^ 2)) x) =
      (-(LieAlgebra.ad R B (f a) ^ 2)) (f x) := by
  simp only [LinearMap.neg_apply, map_neg, map_ad_sq]

/-- A faithful algebra map reflects the entire operator-weighted action equation. -/
theorem ad_sq_weighted_eq_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    (a k x : A) (r : R) :
    (LieAlgebra.ad R B (f a) ^ 2) (f x) = r • (f k * f x) ↔
      (LieAlgebra.ad R A a ^ 2) x = r • (k * x) := by
  rw [← map_ad_sq, ← map_mul, ← map_smul]
  exact hf.eq_iff

end Naturality

/-- The native linear maps form a commuting square at each finite stage. -/
theorem ofStage_ad_sq_intertwines (n : ℕ) (a : Stage n) :
    (ofStageStarAlgHom n).toLinearMap.comp (LieAlgebra.ad ℝ (Stage n) a ^ 2) =
      (LieAlgebra.ad ℝ Limit (ofStage n a) ^ 2).comp
        (ofStageStarAlgHom n).toLinearMap := by
  ext x
  exact map_ad_sq (ofStageStarAlgHom n).toAlgHom a x

/-- The actual quotient loses no finite-stage zero of the squared action. -/
theorem ofStage_ad_sq_eq_zero_iff (n : ℕ) (a x : Stage n) :
    (LieAlgebra.ad ℝ Limit (ofStage n a) ^ 2) (ofStage n x) = 0 ↔
      (LieAlgebra.ad ℝ (Stage n) a ^ 2) x = 0 := by
  have hm := map_ad_sq (ofStageStarAlgHom n).toAlgHom a x
  change ofStage n ((LieAlgebra.ad ℝ (Stage n) a ^ 2) x) =
    (LieAlgebra.ad ℝ Limit (ofStage n a) ^ 2) (ofStage n x) at hm
  rw [← hm, ← map_zero (ofStage n)]
  exact (ofStageStarAlgHom_injective n).eq_iff

/-- Noncommutation is preserved and reflected by the faithful inclusions. -/
theorem ofStage_commute_iff (n : ℕ) (a b : Stage n) :
    Commute (ofStage n a) (ofStage n b) ↔ Commute a b := by
  change ofStage n a * ofStage n b = ofStage n b * ofStage n a ↔ a * b = b * a
  rw [← map_mul, ← map_mul]
  exact (ofStageStarAlgHom_injective n).eq_iff

theorem ofStage_reflection (n : ℕ) (p : Stage n) :
    ofStage n (reflection p) = reflection (ofStage n p) := by
  change ofStage n (2 * p - 1) = 2 * ofStage n p - 1
  simp only [two_mul, map_sub, map_add, map_one]

theorem ofStage_component10 (n : ℕ) (p a : Stage n) :
    ofStage n (component10 p a) = component10 (ofStage n p) (ofStage n a) := by
  simp [component10, complementIdempotent]

theorem ofStage_component01 (n : ℕ) (p a : Stage n) :
    ofStage n (component01 p a) = component01 (ofStage n p) (ofStage n a) := by
  simp [component01, complementIdempotent]

/-- Idempotent support is transported to the actual limit carrier. -/
theorem ofStage_mem_peirce10 (n : ℕ) {p u : Stage n} (hu : u ∈ peirce10 p) :
    ofStage n u ∈ peirce10 (ofStage n p) := by
  rcases hu with ⟨a, rfl⟩
  change ofStage n (component10 p a) ∈ peirce10 (ofStage n p)
  rw [ofStage_component10]
  exact component10_mem _ _

theorem ofStage_mem_peirce01 (n : ℕ) {p v : Stage n} (hv : v ∈ peirce01 p) :
    ofStage n v ∈ peirce01 (ofStage n p) := by
  rcases hv with ⟨a, rfl⟩
  change ofStage n (component01 p a) ∈ peirce01 (ofStage n p)
  rw [ofStage_component01]
  exact component01_mem _ _

/-- All finite opposite-corner hypotheses are realized inside the real limit. -/
theorem ofStage_opposite_corners (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    IsIdempotentElem (ofStage n p) ∧
      ofStage n u ∈ peirce10 (ofStage n p) ∧
      ofStage n v ∈ peirce01 (ofStage n p) := by
  exact ⟨limit_idempotent hp.eq, ofStage_mem_peirce10 n hu, ofStage_mem_peirce01 n hv⟩

/-- The complete nilpotent, parity and reflection-duality frame is realized
on the actual canonical images, with independent opposite corners. -/
theorem limit_peirce_frame (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    let s := reflection (ofStage n p)
    let a := ofStage n u
    let b := ofStage n v
    a ^ 2 = 0 ∧ b ^ 2 = 0 ∧
      s * (a + b) * s = -(a + b) ∧ s * (a - b) * s = -(a - b) ∧
      s * (a * b + b * a) * s = a * b + b * a ∧
      s * ⁅a, b⁆ * s = ⁅a, b⁆ ∧ ⁅a, b⁆ = s * (a * b + b * a) := by
  dsimp only
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  have hu2 : ofStage n u ^ 2 = 0 := by
    have h := (corners_sq_zero hp' (ofStage n u)).1
    change (component10 (ofStage n p) (ofStage n u)) ^ 2 = 0 at h
    simpa only [component10_fixed hp' hu'] using h
  have hv2 : ofStage n v ^ 2 = 0 := by
    have h := (corners_sq_zero hp' (ofStage n v)).2
    change (component01 (ofStage n p) (ofStage n v)) ^ 2 = 0 at h
    simpa only [component01_fixed hp' hv'] using h
  refine ⟨hu2, hv2, coupled_conjugation hp' hu' hv', ?_,
    jordan_conjugation hp' hu' hv', bracket_conjugation hp' hu' hv',
    (reflection_mul_jordan hp' hu' hv').symm⟩
  simp only [mul_sub, sub_mul, reflection_mul_corner10 hp' hu',
    reflection_mul_corner01 hp' hv', neg_mul, corner10_mul_reflection hp' hu',
    corner01_mul_reflection hp' hv']
  abel

/-- The four stationary modes from the frame remain stationary in the quotient. -/
theorem limit_stationary_modes (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    let a := ofStage n u
    let b := ofStage n v
    (-(LieAlgebra.ad ℝ Limit (a + b) ^ 2)) (a * b + b * a) = 0 ∧
      (-(LieAlgebra.ad ℝ Limit (a + b) ^ 2)) (a + b) = 0 ∧
      (LieAlgebra.ad ℝ Limit (a - b) ^ 2) (a * b + b * a) = 0 ∧
      (LieAlgebra.ad ℝ Limit (a - b) ^ 2) (a - b) = 0 := by
  dsimp only
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  exact ⟨neg_ad_sum_sq_quadratic hp' hu' hv', neg_ad_sum_sq_sum _ _,
    ad_difference_sq_quadratic hp' hu' hv', ad_difference_sq_difference _ _⟩

theorem limit_reflection_modes (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    let s := reflection (ofStage n p)
    let a := ofStage n u
    let b := ofStage n v
    (-(LieAlgebra.ad ℝ Limit (a + b) ^ 2)) s =
        -(4 • ((a * b + b * a) * s)) ∧
      (LieAlgebra.ad ℝ Limit (a - b) ^ 2) s =
        -(4 • ((a * b + b * a) * s)) := by
  dsimp only
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  exact ⟨neg_ad_sum_sq_reflection hp' hu' hv', ad_difference_sq_reflection hp' hu' hv'⟩

/-- The axial input to the negative sum-square has its exact operator factor in the limit. -/
theorem limit_neg_ad_sum_sq_difference (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad ℝ Limit (ofStage n u + ofStage n v) ^ 2))
        (ofStage n u - ofStage n v) =
      -(4 • ((ofStage n u * ofStage n v + ofStage n v * ofStage n u) *
        (ofStage n u - ofStage n v))) := by
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  exact neg_ad_sum_sq_difference hp' hu' hv'

theorem limit_neg_ad_sum_sq_bracket (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (-(LieAlgebra.ad ℝ Limit (ofStage n u + ofStage n v) ^ 2))
        ⁅ofStage n u, ofStage n v⁆ =
      -(4 • ((ofStage n u * ofStage n v + ofStage n v * ofStage n u) *
        ⁅ofStage n u, ofStage n v⁆)) := by
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  exact neg_ad_sum_sq_bracket hp' hu' hv'

theorem limit_ad_difference_sq_sum (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad ℝ Limit (ofStage n u - ofStage n v) ^ 2)
        (ofStage n u + ofStage n v) =
      -(4 • ((ofStage n u * ofStage n v + ofStage n v * ofStage n u) *
        (ofStage n u + ofStage n v))) := by
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  exact ad_difference_sq_sum hp' hu' hv'

theorem limit_ad_difference_sq_bracket (n : ℕ) {p u v : Stage n}
    (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad ℝ Limit (ofStage n u - ofStage n v) ^ 2)
        ⁅ofStage n u, ofStage n v⁆ =
      -(4 • ((ofStage n u * ofStage n v + ofStage n v * ofStage n u) *
        ⁅ofStage n u, ofStage n v⁆)) := by
  obtain ⟨hp', hu', hv'⟩ := ofStage_opposite_corners n hp hu hv
  exact ad_difference_sq_bracket hp' hu' hv'

/-- Reflection of a lifted forward corner is minus its actual star. -/
theorem limit_reflected_star_corner (n : ℕ) {p u : Stage n}
    (hp : IsIdempotentElem p) (hps : IsSelfAdjoint p) (hu : u ∈ peirce10 p) :
    reflection (ofStage n p) * star (ofStage n u) * reflection (ofStage n p) =
      -star (ofStage n u) := by
  have hv := star_mem_peirce01 hps hu
  have h : reflection p * star u * reflection p = -star u := by
    rw [reflection_mul_corner01 hp hv, neg_mul, corner01_mul_reflection hp hv]
  simpa only [map_mul, ofStage_reflection, ofStage_star, map_neg] using
    congrArg (ofStage n) h

/-- The negative reflected anticommutator is a Gram sum in the actual star ring. -/
theorem limit_reflected_gram (n : ℕ) {p u : Stage n}
    (hp : IsIdempotentElem p) (hps : IsSelfAdjoint p) (hu : u ∈ peirce10 p) :
    -((reflection (ofStage n p) * star (ofStage n u) * reflection (ofStage n p)) *
          ofStage n u + ofStage n u *
          (reflection (ofStage n p) * star (ofStage n u) * reflection (ofStage n p))) =
      ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u := by
  rw [limit_reflected_star_corner n hp hps hu]
  noncomm_ring

/-- The universal real star-algebra factorization also intertwines the actual
double action, and reads it back through the given finite-stage map. -/
theorem lift_ad_sq {B : Type} [Ring B] [StarRing B] [Algebra ℝ B]
    (f : ∀ n, Stage n →⋆ₐ[ℝ] B)
    (hf : ∀ n x, f (n + 1) (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n x) = f n x)
    (n : ℕ) (a x : Stage n) :
    InfoGeometry.Clifford.Cl11StarUniversal.lift f hf
        ((LieAlgebra.ad ℝ Limit (ofStageStarAlgHom n a) ^ 2) (ofStageStarAlgHom n x)) =
      (LieAlgebra.ad ℝ B (f n a) ^ 2) (f n x) := by
  have hm := map_ad_sq (ofStageStarAlgHom n).toAlgHom a x
  change ofStageStarAlgHom n ((LieAlgebra.ad ℝ (Stage n) a ^ 2) x) =
    (LieAlgebra.ad ℝ Limit (ofStageStarAlgHom n a) ^ 2) (ofStageStarAlgHom n x) at hm
  rw [← hm]
  rw [InfoGeometry.Clifford.Cl11StarUniversal.lift_of]
  exact map_ad_sq (f n).toAlgHom a x

end InfoGeometry.Canonical.PeirceDissipatorColimit
