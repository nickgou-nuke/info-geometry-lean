import Mathlib.Tactic
import InfoGeometry.Categorical.LogNilpotentPhysicalBraidedCategory
import InfoGeometry.Categorical.LogNilpotentCrossCheckedR
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

/-!
# Rank-two readback of the physical logarithmic braided category

The all-object physical braiding uses Mathlib's finite nilpotent exponential.
On the standard rank-two Jordan cell the mixed cross term is square-zero, so
that exponential truncates exactly to the affine Hadjiivanov readout already
owned by `LogNilpotentCrossCheckedR`.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonoidalCategory

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentPhysicalBraiding
open InfoGeometry.Categorical.LogNilpotentPhysicalBraidedCategory
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Clifford.LogCftMonodromy

/-- The scaled mixed generator is square-zero on a square-zero logarithmic
object. -/
theorem scaledCrossEnd_sq_zero_of_sq_zero
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    (scaledCrossEnd p X X) ^ 2 = 0 := by
  rw [scaledCrossEnd, smul_pow]
  have hcross :
      (crossTensorEnd X.toLogEndModule X.toLogEndModule) ^ 2 = 0 :=
    crossTensorEnd_sq_eq_zero_of_sq_zero
      X.toLogEndModule X.toLogEndModule hX hX
  rw [hcross, smul_zero]

/-- On square-zero objects Mathlib's nilpotent exponential is exactly
`id + p (N ⊗ N)`. -/
theorem crossExpEnd_eq_affine_of_sq_zero
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    crossExpEnd p X X =
      LinearMap.id + p • crossTensorEnd X.toLogEndModule X.toLogEndModule := by
  rw [crossExpEnd, IsNilpotent.exp_eq_sum
    (scaledCrossEnd_sq_zero_of_sq_zero X hX p)]
  simp [scaledCrossEnd, Finset.sum_range_succ]

/-- The all-object exponential readout agrees with the pre-existing
Hadjiivanov square-zero unipotent readout. -/
theorem crossExpEnd_eq_crossUnipotentMap
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    crossExpEnd p X X = crossUnipotentMap X hX p := by
  rw [crossExpEnd_eq_affine_of_sq_zero X hX p]
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp [crossUnipotentMap]
  · intro x y
    simp [crossUnipotentMap_tmul, crossTensorEnd,
      TensorProduct.map_tmul]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- For a square-zero object, the all-object physical braiding is exactly the
checked-R isomorphism from PR #120. -/
theorem physicalBraidingIso_eq_logCheckedRLogIso
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ)
    (hmonodromy :
      ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap ≠
        LinearMap.id) :
    physicalBraidingIso p X X =
      logCheckedRLogIso X hX p hmonodromy := by
  apply Iso.ext
  apply LogEndModule.Hom.ext
  apply LinearMap.ext
  intro t
  have hExp := LinearMap.congr_fun
    (crossExpEnd_eq_crossUnipotentMap X hX p) t
  simp [physicalBraidingIso, crossExpIso, crossExpHom,
    logCheckedRLogIso, InfoGeometry.Categorical.LogNilpotentCheckedRAdapter.checkedRIso,
    InfoGeometry.Categorical.LogNilpotentCheckedRAdapter.checkedRHom,
    LogNilpotentCrossCheckedR.logCheckedRDatum,
    LogNilpotentCrossCheckedR.logCheckedR,
    LinearEquiv.trans_apply, hExp]

/-- At `p = -2πi`, the all-object physical braiding on the standard Jordan
cell recovers the named Hadjiivanov checked-R owner exactly. -/
theorem standardHadjiivanovBraiding_eq_checkedR :
    physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject =
      standardHadjiivanovCheckedRLogIso := by
  exact physicalBraidingIso_eq_logCheckedRLogIso
    standardJordanObject standardJordanObject_sq_zero logShearBase
    (standard_logCheckedR_monodromy_nontrivial
      logShearBase logShearBase_ne_zero)

/-- Consequently the physical braided structure is non-symmetric on its
standard rank-two generator. -/
theorem standardHadjiivanovBraiding_double_ne_id :
    (physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject).hom ≫
      (physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject).hom ≠
      𝟙 (standardJordanObject ⊗ standardJordanObject) := by
  intro h
  have hh := congrArg
    (fun f : standardJordanObject ⊗ standardJordanObject ⟶
        standardJordanObject ⊗ standardJordanObject => f.hom) h
  rw [standardHadjiivanovBraiding_eq_checkedR] at hh
  exact standardHadjiivanov_monodromy_ne_id (by
    simpa [LogNilpotentModule.hom_comp] using hh)

end InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge
