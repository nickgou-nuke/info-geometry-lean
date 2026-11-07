/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import InfoGeometry.LLM.LanguageSymmetryBinary
import InfoGeometry.LLM.LanguageSymmetryToeplitz
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic.Module

/-!
# Subgroup averaging and binary surprisal compression

The projector is Mathlib's finite-group average, not an assumed idempotent
called a quotient. Character functions act through multiplication operators.
The invariant space has a native quotient-group action for a normal subgroup.

The logarithmic scalar is the existing binary contrast. The operator below is
its affine lift along an involution; no arbitrary-ring logarithm or BKM metric
is asserted. A vanishing compressed involution need not have a vanishing
complementary diagonal block.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Compression of a scalar-affine operator preserves its two coefficients. -/
theorem compression_affine (p σ : A) (hp : p * p = p) (u δ : ℝ) :
    p * (u • (1 : A) + δ • σ) * p = u • p + δ • (p * σ * p) := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hp]

/-- The square of an affine involution, with central real coefficients. -/
theorem affine_involution_square (σ : A) (hσ : σ * σ = 1) (u δ : ℝ) :
    (u • (1 : A) + δ • σ) * (u • (1 : A) + δ • σ) =
      (u ^ 2 + δ ^ 2) • (1 : A) + (2 * u * δ) • σ := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, hσ]
  module

/-- A microscopic involution disappears to first order. -/
theorem compression_affine_micro (p σ : A) (hp : p * p = p)
    (hmicro : p * σ * p = 0) (u δ : ℝ) :
    p * (u • (1 : A) + δ • σ) * p = u • p := by
  rw [compression_affine p σ hp u δ, hmicro, smul_zero, add_zero]

/-- A commuting attribute retains its full affine operator on the compressed
carrier. -/
theorem compression_affine_macro (p σ : A) (hp : p * p = p)
    (hcomm : p * σ = σ * p) (u δ : ℝ) :
    p * (u • (1 : A) + δ • σ) * p = (u • (1 : A) + δ • σ) * p := by
  rw [compression_affine p σ hp u δ]
  simp only [add_mul, smul_mul_assoc, one_mul]
  rw [hcomm, mul_assoc, hp]

/-- Its exact second-order compression defect is the squared contrast. -/
theorem compression_affine_involution_defect (p σ : A) (hp : p * p = p)
    (hσ : σ * σ = 1) (hmicro : p * σ * p = 0) (u δ : ℝ) :
    p * ((u • (1 : A) + δ • σ) * (u • (1 : A) + δ • σ)) * p -
        (p * (u • (1 : A) + δ • σ) * p) *
          (p * (u • (1 : A) + δ • σ) * p) = δ ^ 2 • p := by
  rw [affine_involution_square σ hσ]
  simp only [compression_affine_micro p σ hp hmicro, smul_mul_assoc,
    mul_smul_comm, smul_smul, hp]
  module

/-- The same variance is the existing Peirce transfer product. -/
theorem affine_involution_helper_product (p σ : A) (hp : p * p = p)
    (hσ : σ * σ = 1) (hmicro : p * σ * p = 0) (u δ : ℝ) :
    (p * (u • (1 : A) + δ • σ) * (1 - p)) *
      ((1 - p) * (u • (1 : A) + δ • σ) * p) = δ ^ 2 • p := by
  rw [← Core.PeirceCompressionDefect.compression_square_defect p _ hp]
  exact compression_affine_involution_defect p σ hp hσ hmicro u δ

omit [Algebra ℝ A] in
/-- A nonzero compressed corner killed by an involution cannot commute with it. -/
theorem compressed_involution_not_commute (p σ : A) (hp : p * p = p)
    (hσ : σ * σ = 1) (hp0 : p ≠ 0) (hmicro : p * σ * p = 0) :
    p * σ ≠ σ * p := by
  intro hc
  have hz : p * σ = 0 := by
    have he : p * σ * p = p * σ := by
      rw [hc, mul_assoc, hp, ← hc]
    exact he.symm.trans hmicro
  have he := congrArg (fun a : A => a * σ) hz
  simp only [mul_assoc, hσ, mul_one, zero_mul] at he
  exact hp0 he

/-- The affine operator built from the actual two-point logarithmic values. -/
def binarySurprisalOperator (s : ℝ) (σ : A) : A :=
  binaryLogMean s • (1 : A) + binaryLogContrast s • σ

/-- On the positive probabilistic domain, the contrast is exactly `artanh`. -/
theorem binaryLogContrast_eq_artanh {s : ℝ} (hs : |s| < 1) :
    binaryLogContrast s = Real.artanh s := by
  rw [binaryLogContrast_eq_log_ratio hs,
    Real.artanh_eq_half_log ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩]
  ring

/-- Within `(-1,1)`, the contrast vanishes exactly at zero coupling. -/
theorem binaryLogContrast_ne_zero_iff {s : ℝ} (hs : |s| < 1) :
    binaryLogContrast s ≠ 0 ↔ s ≠ 0 := by
  rw [binaryLogContrast_eq_artanh hs, ne_eq, Real.artanh_eq_zero_iff]
  have hlo : ¬ s ≤ -1 := not_le.mpr (abs_lt.mp hs).1
  have hhi : ¬ 1 ≤ s := not_le.mpr (abs_lt.mp hs).2
  simp only [hlo, hhi, false_or, or_false]

/-- A genuine binary logarithmic contrast yields the stated variance. -/
theorem binary_surprisal_compression_defect (p σ : A) (hp : p * p = p)
    (hσ : σ * σ = 1) (hmicro : p * σ * p = 0) {s : ℝ} (hs : |s| < 1) :
    p * (binarySurprisalOperator s σ * binarySurprisalOperator s σ) * p -
        (p * binarySurprisalOperator s σ * p) *
          (p * binarySurprisalOperator s σ * p) = (Real.artanh s) ^ 2 • p := by
  unfold binarySurprisalOperator
  rw [compression_affine_involution_defect p σ hp hσ hmicro,
    binaryLogContrast_eq_artanh hs]

end Algebra

section Averaging

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℝ V] [Invertible (Fintype.card G : ℝ)]

/-- The native average is an idempotent endomorphism. -/
theorem subgroup_average_idempotent (ρ : Representation ℝ G V) :
    ρ.averageMap * ρ.averageMap = ρ.averageMap :=
  ρ.isProj_averageMap.isIdempotentElem

/-- Averaging absorbs a subgroup action on its left. -/
theorem action_mul_average (ρ : Representation ℝ G V) (g : G) :
    ρ g * ρ.averageMap = ρ.averageMap := by
  ext v
  exact ρ.averageMap_invariant v g

/-- Averaging also absorbs a subgroup action on its right. -/
theorem average_mul_action (ρ : Representation ℝ G V) (g : G) :
    ρ.averageMap * ρ g = ρ.averageMap := by
  rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
    ← map_mul, GroupAlgebra.mul_average_right]

/-- A nontrivial scalar covariance forces the compressed operator to vanish. -/
theorem average_weighted_compression_zero (ρ : Representation ℝ G V)
    (σ : Module.End ℝ V) (g : G) (c : ℝ) (hc : c ≠ 1)
    (hcov : ρ g * σ = c • (σ * ρ g)) :
    ρ.averageMap * σ * ρ.averageMap = 0 := by
  have heq : ρ.averageMap * σ * ρ.averageMap =
      c • (ρ.averageMap * σ * ρ.averageMap) := by
    calc
      _ = ρ.averageMap * (ρ g * σ) * ρ.averageMap := by
        rw [← mul_assoc, average_mul_action]
      _ = c • (ρ.averageMap * σ * ρ.averageMap) := by
        rw [hcov]
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc,
          action_mul_average]
  have hz : (c - 1) • (ρ.averageMap * σ * ρ.averageMap) = 0 := by
    rw [sub_smul, one_smul, ← heq, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

/-- Commutation with every subgroup action implies commutation with its average. -/
theorem average_commutes_of_commutes (ρ : Representation ℝ G V)
    (σ : Module.End ℝ V) (hcomm : ∀ g, ρ g * σ = σ * ρ g) :
    ρ.averageMap * σ = σ * ρ.averageMap := by
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul,
    map_sum, Representation.asAlgebraHom_of, smul_mul_assoc, mul_smul_comm,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact hcomm g

/-- An operator preserving subgroup invariants descends through compression. -/
theorem average_compression_of_commutes (ρ : Representation ℝ G V)
    (σ : Module.End ℝ V) (hcomm : ∀ g, ρ g * σ = σ * ρ g) :
    ρ.averageMap * σ * ρ.averageMap = σ * ρ.averageMap := by
  ext v
  apply ρ.averageMap_id
  intro g
  change (ρ g * σ) (ρ.averageMap v) = σ (ρ.averageMap v)
  rw [hcomm g]
  exact congrArg σ (ρ.averageMap_invariant v g)

end Averaging

section QuotientFunctions

open TannakaDuality

variable {G : Type} [Group G] (H : Subgroup G)

/-- Pullback from quotient functions identifies the quotient with subgroup
invariants of the native right regular representation. No normality is needed
for this equivalence of function spaces. -/
def quotientFunctionsEquivInvariants :
    (G ⧸ H → ℝ) ≃ₗ[ℝ]
      (Representation.invariants ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) where
  toFun f := ⟨fun x => f (QuotientGroup.mk x), by
    intro h
    funext x
    change f (QuotientGroup.mk (x * h.val)) = f (QuotientGroup.mk x)
    rw [QuotientGroup.mk_mul_of_mem x h.property]⟩
  invFun f := Quotient.lift f.val (by
    intro a b hab
    have hm : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hf := congrFun (f.property ⟨a⁻¹ * b, hm⟩) a
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply,
      FiniteGroup.rightRegular_apply, mul_inv_cancel_left] using hf.symm)
  left_inv f := by
    funext x
    induction x using Quotient.inductionOn with
    | h x => rfl
  right_inv f := by rfl
  map_add' f g := by rfl
  map_smul' r f := by rfl

/-- The native quotient-group representation acts compatibly on the invariant
carrier; normality is the precise extra requirement. -/
theorem quotient_action_on_invariants [H.Normal]
    (g x : G)
    (f : (Representation.invariants ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype))) :
    ((FiniteGroup.rightRegular (k := ℝ) (G := G)).quotientToInvariants H
      (QuotientGroup.mk' H g) f).val x = f.val (x * g) := rfl

/-- A character acts on functions by pointwise multiplication. -/
def characterMultiplier (χ : G →* ℝ) : Module.End ℝ (G → ℝ) :=
  LinearMap.mulLeft ℝ (χ : G → ℝ)

/-- Translation and character multiplication obey the exact covariance law. -/
theorem rightRegular_character_covariance (χ : G →* ℝ) (g : G) :
    FiniteGroup.rightRegular (k := ℝ) g * characterMultiplier χ =
      χ g • (characterMultiplier χ * FiniteGroup.rightRegular (k := ℝ) g) := by
  ext f x
  change χ (x * g) * f (x * g) = χ g * (χ x * f (x * g))
  rw [map_mul]
  ring

/-- A sign character gives an actual involution of the whole function space. -/
theorem characterMultiplier_involution (χ : G →* ℝ)
    (hχ : ∀ x, χ x ^ 2 = 1) :
    characterMultiplier χ * characterMultiplier χ = 1 := by
  ext f x
  change χ x * (χ x * f x) = f x
  rw [← mul_assoc, ← pow_two, hχ x, one_mul]

/-- For a sign character, the affine lift is exactly multiplication by the
actual pointwise logarithm. The positive probabilistic domain is supplied by
`binary_factor_pos` when `|s| < 1`. -/
theorem binary_surprisal_character_apply (χ : G →* ℝ)
    (hχ : ∀ x, χ x ^ 2 = 1) (s : ℝ) (f : G → ℝ) (x : G) :
    binarySurprisalOperator s (characterMultiplier χ) f x =
      Real.log (1 + s * χ x) * f x := by
  change binaryLogMean s * f x + binaryLogContrast s * (χ x * f x) = _
  rw [binary_log_affine s (χ x) (hχ x)]
  ring

/-- A character trivial on a normal subgroup gives the actual quotient
multiplier, and multiplication commutes with pullback along the quotient map. -/
theorem quotient_character_multiplier_compatible [H.Normal]
    (χ : G →* ℝ) (hχ : H ≤ χ.ker) (f : G ⧸ H → ℝ) :
    characterMultiplier χ (fun x => f (QuotientGroup.mk' H x)) =
      fun x => characterMultiplier (QuotientGroup.lift H χ hχ) f
        (QuotientGroup.mk' H x) := by
  rfl

variable [Fintype H] [Invertible (Fintype.card H : ℝ)]

/-- A character nontrivial on the averaging subgroup is killed in compression. -/
theorem micro_character_compression_zero (χ : G →* ℝ)
    (hmicro : ∃ h : H, χ h.val ≠ 1) :
    (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) *
        characterMultiplier χ *
        (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) = 0 := by
  obtain ⟨h, hh⟩ := hmicro
  exact average_weighted_compression_zero _ _ h (χ h.val) hh
    (rightRegular_character_covariance χ h.val)

/-- A character trivial on the averaging subgroup descends at first order. -/
theorem macro_character_compression (χ : G →* ℝ)
    (hmacro : ∀ h : H, χ h.val = 1) :
    (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) *
        characterMultiplier χ *
        (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) =
      characterMultiplier χ *
        (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) := by
  apply average_compression_of_commutes
  intro h
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hmacro h, one_smul] using
    rightRegular_character_covariance χ h.val

/-- Macro-character multiplication actually commutes with subgroup averaging. -/
theorem macro_character_commutes_average (χ : G →* ℝ)
    (hmacro : ∀ h : H, χ h.val = 1) :
    (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) *
        characterMultiplier χ =
      characterMultiplier χ *
        (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) := by
  apply average_commutes_of_commutes
  intro h
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hmacro h, one_smul] using
    rightRegular_character_covariance χ h.val

/-- A character trivial on the subgroup retains the full binary-surprisal
affine operator under compression, including the contrast term. -/
theorem quotient_macro_binary_surprisal_compression (χ : G →* ℝ)
    (hmacro : ∀ h : H, χ h.val = 1) (s : ℝ) :
    let P := (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype))
    let L := binarySurprisalOperator s (characterMultiplier χ)
    P * L * P = L * P := by
  exact compression_affine_macro _ _ (subgroup_average_idempotent _)
    (macro_character_commutes_average H χ hmacro) _ _

/-- The regular subgroup projector is nonzero because it fixes constants. -/
theorem regular_subgroup_average_ne_zero :
    (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype)) ≠ 0 := by
  intro hz
  have hc := (Representation.averageMap_id ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype))
    (fun _ => (1 : ℝ)) (by intro h; rfl)
  rw [hz] at hc
  have h := congrFun hc (1 : G)
  norm_num at h

/-- Binary microscopic attributes have exactly the claimed quotient variance,
now for a constructed projector and a constructed multiplication operator. -/
theorem quotient_binary_surprisal_defect (χ : G →* ℝ)
    (hχ : ∀ x, χ x ^ 2 = 1) (hmicro : ∃ h : H, χ h.val ≠ 1)
    {s : ℝ} (hs : |s| < 1) :
    let P := (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype))
    let L := binarySurprisalOperator s (characterMultiplier χ)
    P * (L * L) * P - (P * L * P) * (P * L * P) = (Real.artanh s) ^ 2 • P := by
  exact binary_surprisal_compression_defect _ _ (subgroup_average_idempotent _)
    (characterMultiplier_involution χ hχ) (micro_character_compression_zero H χ hmicro) hs

/-- On the regular carrier, nonzero coupling is precisely nonzero variance. -/
theorem quotient_binary_surprisal_defect_ne_zero_iff (χ : G →* ℝ)
    (hχ : ∀ x, χ x ^ 2 = 1) (hmicro : ∃ h : H, χ h.val ≠ 1)
    {s : ℝ} (hs : |s| < 1) :
    let P := (Representation.averageMap ((FiniteGroup.rightRegular (k := ℝ) (G := G)).comp H.subtype))
    let L := binarySurprisalOperator s (characterMultiplier χ)
    P * (L * L) * P - (P * L * P) * (P * L * P) ≠ 0 ↔ s ≠ 0 := by
  dsimp only
  rw [quotient_binary_surprisal_defect H χ hχ hmicro hs,
    smul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0)]
  rw [← binaryLogContrast_eq_artanh hs, binaryLogContrast_ne_zero_iff hs]
  exact and_iff_left (regular_subgroup_average_ne_zero H)

end QuotientFunctions

section Counterexample

open Matrix

/-- Exchange the first two coordinates and leave the third fixed. -/
def partialSwap3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

/-- Vanishing of one diagonal corner does not imply that an involution is
entirely off diagonal: the complementary corner can retain a fixed vector. -/
theorem partialSwap3_compression_counterexample :
    let P : Matrix (Fin 3) (Fin 3) ℝ := endpointProjection3
    P * P = P ∧ partialSwap3 * partialSwap3 = 1 ∧ P * partialSwap3 * P = 0 ∧
      (1 - P) * partialSwap3 * (1 - P) ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [endpointProjection3, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [partialSwap3, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [endpointProjection3, partialSwap3, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro h
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 2 2) h
    norm_num [endpointProjection3, partialSwap3, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] at he

end Counterexample

end InfoGeometry.LLM.LanguageSymmetry
