import Mathlib.Tactic
import InfoGeometry.Categorical.LogNilpotentHadjiivanovBraidedCategory
import InfoGeometry.Categorical.LogNilpotentCrossCheckedR
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

/-!
# Rank-two readback of the natural Hadjiivanov braiding

The all-object braiding is defined with Mathlib's finite nilpotent exponential.
On a square-zero Jordan cell the mixed cross term is square-zero, so that
exponential truncates exactly to `1 + p (N ⊗ N)`.  This file proves that the
new two-object construction recovers the checked-R owner from PR #120 exactly.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentHadjiivanovExponential
open InfoGeometry.Categorical.LogNilpotentHadjiivanovBraidedCategory
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Clifford.LogCftMonodromy

/-- The scaled mixed term remains square-zero when the underlying logarithmic
endomorphism is square-zero. -/
theorem scaledCrossEnd_sq_zero_of_sq_zero
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    (p • crossEnd X X) ^ 2 = 0 := by
  have hcross : crossEnd X X ^ 2 = 0 := by
    simpa [crossEnd] using
      (crossTensorEnd_sq_eq_zero_of_sq_zero
        X.toLogEndModule X.toLogEndModule hX hX)
  rw [smul_pow, hcross, smul_zero]

/-- On square-zero objects, the native nilpotent exponential is exactly the
rank-two affine Hadjiivanov readout. -/
theorem crossExpEnd_eq_affine_of_sq_zero
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    crossExpEnd p X X = LinearMap.id + p • crossEnd X X := by
  rw [crossExpEnd, IsNilpotent.exp_eq_sum
    (scaledCrossEnd_sq_zero_of_sq_zero X hX p)]
  norm_num [Finset.sum_range_succ]

/-- The all-object exponential coincides with the pre-existing square-zero
Hadjiivanov unipotent map. -/
theorem crossExpEnd_eq_crossUnipotentMap
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    crossExpEnd p X X = crossUnipotentMap X hX p := by
  rw [crossExpEnd_eq_affine_of_sq_zero X hX p]
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp [crossUnipotentMap]
  · intro x y
    simp [crossUnipotentMap_tmul, crossEnd,
      crossTensorEnd, TensorProduct.map_tmul]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Under square-zero hypotheses, the natural two-object linear braiding is
exactly the earlier checked-R linear equivalence. -/
theorem logarithmicBraidingLinearEquiv_eq_logCheckedR
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    (crossExpLinearEquiv p X X).trans (TensorProduct.comm ℂ X X) =
      logCheckedR X hX p := by
  apply LinearEquiv.ext
  intro t
  have hExp := crossExpEnd_eq_crossUnipotentMap X hX p
  have ht := LinearMap.congr_fun hExp t
  simp [logCheckedR, LinearEquiv.trans_apply, crossExpLinearEquiv,
    crossUnipotentEquiv, ht]

/-- The categorical natural braiding recovers the checked-R logarithmic
isomorphism whenever the supplied monodromy witness is used. -/
theorem logarithmicBraidingIso_eq_logCheckedRLogIso
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ)
    (hmonodromy :
      ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap ≠
        LinearMap.id) :
    logarithmicBraidingIso p X X =
      logCheckedRLogIso X hX p hmonodromy := by
  apply Iso.ext
  apply LogEndModule.Hom.ext
  change
    ((crossExpLinearEquiv p X X).trans (TensorProduct.comm ℂ X X)).toLinearMap =
      (logCheckedR X hX p).toLinearMap
  exact congrArg LinearEquiv.toLinearMap
    (logarithmicBraidingLinearEquiv_eq_logCheckedR X hX p)

/-- Physical specialization: the natural `p = -2πi` braiding on the standard
Jordan object is exactly the rank-two Hadjiivanov checked-R owner. -/
theorem standardHadjiivanovBraiding_eq_checkedR :
    hadjiivanovBraidingIso standardJordanObject standardJordanObject =
      standardHadjiivanovCheckedRLogIso := by
  exact logarithmicBraidingIso_eq_logCheckedRLogIso
    standardJordanObject standardJordanObject_sq_zero logShearBase
    (standard_logCheckedR_monodromy_nontrivial
      logShearBase logShearBase_ne_zero)

/-- Therefore the physical all-object braiding is genuinely non-symmetric on
its standard rank-two generator. -/
theorem standardHadjiivanovBraiding_double_ne_id :
    (hadjiivanovBraidingIso standardJordanObject standardJordanObject).hom ≫
        (hadjiivanovBraidingIso standardJordanObject standardJordanObject).hom ≠
      𝟙 (standardJordanObject ⊗ standardJordanObject) := by
  intro h
  have hh := congrArg
    (fun f : standardJordanObject ⊗ standardJordanObject ⟶
        standardJordanObject ⊗ standardJordanObject => f.hom) h
  rw [standardHadjiivanovBraiding_eq_checkedR] at hh
  exact standardHadjiivanov_monodromy_ne_id (by
    simpa [LogNilpotentModule.hom_comp] using hh)

end InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge
