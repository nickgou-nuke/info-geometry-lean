import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open MeasureTheory

theorem normalizedPrependBitLp_partition :
    (normalizedPrependBitLpContinuousLinearMap false).comp (normalizedPrependBitLpAdjoint false) +
    (normalizedPrependBitLpContinuousLinearMap true).comp (normalizedPrependBitLpAdjoint true) =
    ContinuousLinearMap.id ℂ L2Boundary := by
  apply ContinuousLinearMap.ext
  intro f
  let k : ℂ := prependBitLpNormFactor
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (ne_of_gt prependBitLpNormFactor_pos)
  let f₀ := k • prependBitLp false f
  let f₁ := k • prependBitLp true f
  have hf : normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁ = f := by
    rw [normalizedPrependBitLpContinuousLinearMap_apply,
      normalizedPrependBitLpContinuousLinearMap_apply,
      rawPrependBitLp_smul, rawPrependBitLp_smul,
      rawPrependBitLp_prependBitLp, rawPrependBitLp_prependBitLp]
    change (k⁻¹ : ℂ) • (k • branchIndicatorLp false f) +
        (k⁻¹ : ℂ) • (k • branchIndicatorLp true f) = f
    rw [inv_smul_smul₀ hk, inv_smul_smul₀ hk,
      branchIndicatorLp_partition]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [← hf]
  have hF : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₀ := by
    rw [map_add]
    have hself : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀) = f₀ := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self false) f₀
      exact hcomp
    have hcross : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap true f₁) = 0 := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : false ≠ true)) f₁
      exact hcomp
    rw [hself, hcross, add_zero]
  have hT : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
    rw [map_add]
    have hcross : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀) = 0 := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : true ≠ false)) f₀
      exact hcomp
    have hself : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
      have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self true) f₁
      exact hcomp
    rw [hcross, hself, zero_add]
  rw [hF, hT]
