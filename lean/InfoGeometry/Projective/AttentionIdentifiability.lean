/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.AttentionValueCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Identifiability of finite attention coordinates

The existing homogeneous decoder owns mass and fixed-value readout. This file
uses native affine independence and its actual linear kernel. No second
simplex, stochastic-matrix predicate, or value decoder is introduced.
-/

noncomputable section

namespace InfoGeometry.Projective.AttentionIdentifiability

open InfoGeometry.Projective.AttentionValueCoordinates
open scoped BigOperators

variable {J D : Type*} [Fintype J]

/-- Equal homogeneous outputs are exactly differences in the decoder kernel. -/
theorem decoder_eq_iff_sub_mem_ker (V : J → D → ℝ) (p q : J → ℝ) :
    homogeneousDecoder V p = homogeneousDecoder V q ↔
      p - q ∈ (homogeneousDecoder V).ker := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- Native affine independence is injectivity of the existing homogeneous map. -/
theorem affineIndependent_iff_decoder_injective (V : J → D → ℝ) :
    AffineIndependent ℝ V ↔ Function.Injective (homogeneousDecoder V) := by
  rw [affineIndependent_iff_linearIndependent_lift, Fintype.linearIndependent_iff]
  constructor
  · intro h p q hpq
    have hz : ∑ j, (p - q) j • affineLift (V j) = 0 := by
      change homogeneousDecoder V (p - q) = 0
      rw [map_sub, hpq, sub_self]
    exact sub_eq_zero.mp (funext (h (p - q) hz))
  · intro h c hc j
    have hz : homogeneousDecoder V c = homogeneousDecoder V 0 := by
      rw [map_zero]
      exact hc
    exact congrFun (h hz) j

/-- Dependence produces a genuine nonzero kernel direction, not a witness field. -/
theorem exists_nonzero_decoder_kernel (V : J → D → ℝ)
    (hV : ¬ AffineIndependent ℝ V) :
    ∃ δ : J → ℝ, δ ≠ 0 ∧ δ ∈ (homogeneousDecoder V).ker := by
  classical
  have hn : ¬ Function.Injective (homogeneousDecoder V) :=
    fun h => hV ((affineIndependent_iff_decoder_injective V).mpr h)
  simp only [Function.Injective, not_forall, not_imp] at hn
  obtain ⟨p, q, hpq, hne⟩ := hn
  exact ⟨p - q, sub_ne_zero.mpr hne, (decoder_eq_iff_sub_mem_ker V p q).mp hpq⟩

/-- Every real displacement along the kernel preserves the homogeneous output. -/
theorem decoder_add_smul_of_mem_ker (V : J → D → ℝ) (p δ : J → ℝ)
    (hδ : δ ∈ (homogeneousDecoder V).ker) (t : ℝ) :
    homogeneousDecoder V (p + t • δ) = homogeneousDecoder V p := by
  rw [map_add, map_smul, LinearMap.mem_ker.mp hδ, smul_zero, add_zero]

/-- A nonzero direction gives distinct coordinates for distinct parameters. -/
theorem kernel_line_injective (p δ : J → ℝ) (hδ : δ ≠ 0) :
    Function.Injective (fun t : ℝ => p + t • δ) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, δ j ≠ 0 := by
    by_contra! h
    exact hδ (funext h)
  intro s t h
  have he := congrFun h j
  change p j + s * δ j = p j + t * δ j at he
  exact mul_right_cancel₀ hj (add_left_cancel he)

/-- Exact injectivity criterion on the mass-one affine hyperplane. -/
theorem mass_one_readout_injective_iff (V : J → D → ℝ) (p₀ : J → ℝ)
    (hp₀ : ∑ j, p₀ j = 1) :
    Set.InjOn (fun p : J → ℝ => ∑ j, p j • V j) {p | ∑ j, p j = 1} ↔
      AffineIndependent ℝ V := by
  constructor
  · intro hinj
    by_contra hV
    obtain ⟨δ, hne, hker⟩ := exists_nonzero_decoder_kernel V hV
    have he := decoder_add_smul_of_mem_ker V p₀ δ hker 1
    rw [one_smul] at he
    obtain ⟨hm, hv⟩ := (homogeneousDecoder_eq_iff V (p₀ + δ) p₀).mp he
    have hsame := hinj (hm.trans hp₀) hp₀ hv
    apply hne
    have hz : p₀ + δ = p₀ + 0 := by simpa using hsame
    exact add_left_cancel hz
  · intro hV p hp q hq hpq
    exact coordinates_unique V hV p q (hp.trans hq.symm) hpq

/-- Matrix-level identifiability needs only row normalization, not positivity. -/
theorem matrix_readout_injective_of_affineIndependent {I : Type*}
    (V : Matrix J D ℝ) (hV : AffineIndependent ℝ V)
    (P Q : Matrix I J ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (hQ : ∀ i, ∑ j, Q i j = 1) :
    P * V = Q * V ↔ P = Q := by
  constructor
  · intro h
    ext i j
    have hv : (∑ k, P i k • V k) = ∑ k, Q i k • V k := by
      funext d
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply] using
        congrArg (fun M : Matrix I D ℝ => M i d) h
    exact congrFun (coordinates_unique V hV (P i) (Q i)
      ((hP i).trans (hQ i).symm) hv) j
  · rintro rfl
    rfl

section Dimension
variable [Fintype D]

/-- Too many indexed values force dependence even without any probability row. -/
theorem not_affineIndependent_of_card_gt (V : J → D → ℝ)
    (hcard : Fintype.card D + 1 < Fintype.card J) :
    ¬ AffineIndependent ℝ V := by
  intro hV
  exact (not_lt_of_ge (affineIndependent_card_le V hV)) hcard

/-- Rank-nullity for the actual mass-and-value decoder. -/
theorem decoder_rank_nullity (V : J → D → ℝ) :
    Module.finrank ℝ (homogeneousDecoder V).range +
      Module.finrank ℝ (homogeneousDecoder V).ker = Fintype.card J := by
  simpa [Module.finrank_pi] using (homogeneousDecoder V).finrank_range_add_finrank_ker

/-- The exact nullity uses the actual rank, not the ambient value dimension. -/
theorem decoder_nullity_eq (V : J → D → ℝ) :
    Module.finrank ℝ (homogeneousDecoder V).ker =
      Fintype.card J - Module.finrank ℝ (homogeneousDecoder V).range := by
  have h := decoder_rank_nullity V
  omega

theorem decoder_rank_le (V : J → D → ℝ) :
    Module.finrank ℝ (homogeneousDecoder V).range ≤ Fintype.card D + 1 := by
  simpa [Module.finrank_pi] using (homogeneousDecoder V).range.finrank_le

/-- The ambient dimension supplies only a lower bound without full rank. -/
theorem decoder_nullity_lower_bound (V : J → D → ℝ) :
    Fintype.card J - (Fintype.card D + 1) ≤
      Module.finrank ℝ (homogeneousDecoder V).ker := by
  have h := decoder_rank_nullity V
  have hr := decoder_rank_le V
  omega

/-- The commonly stated dimension is exact under the full homogeneous rank hypothesis. -/
theorem decoder_nullity_of_full_rank (V : J → D → ℝ)
    (hrank : Module.finrank ℝ (homogeneousDecoder V).range = Fintype.card D + 1) :
    Module.finrank ℝ (homogeneousDecoder V).ker =
      Fintype.card J - (Fintype.card D + 1) := by
  rw [decoder_nullity_eq, hrank]

end Dimension
end InfoGeometry.Projective.AttentionIdentifiability
