import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.Canonical.CuntzCantorBoundaryShift
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge

/-!
# Cantor-Bernoulli Cylinder Multiplication Operator Bridge

This file establishes the fundamental isomorphism between:
1. Finite binary tree word cylinder projectors $P_w = S_w S_w^\dagger \in \mathcal{B}(L^2(\mathcal{C}, \mu_C))$,
2. Spatial multiplication operators $M_{\mathbf{1}_{[w]}}$ by characteristic functions of Cantor cylinders,
3. Bernoulli probability cylinder measures $\mu_C([w]) = 2^{-|w|}$,
4. Diagonal expectations in the canonical gauge state: $\varphi(P_w) = 2^{-|w|}$.

## Key Results:
- `normalizedPrependBitLpAdjoint_apply`: Evaluates the adjoint operator $V_b^\dagger(f) = \sqrt{2} (f \circ \operatorname{prependBit}_b)$.
- `branchProjection_apply_eq_branchIndicator`: Proves $P_b f = \mathbf{1}_{B_b} \cdot f$.
- `operatorCylinderProjection_single_coeFn`: $P_b f = \mathbf{1}_{B_b} f$ almost everywhere.
- `wordIndicatorFunction_memLp`: Proves $\mathbf{1}_{[w]} \cdot f \in L^2(\mathcal{C}, \mu_C)$ for arbitrary words.
- `operatorCylinderProjection_apply_eq_wordIndicator`: $P_w f = \mathbf{1}_{[w]} \cdot f$ for arbitrary words.
- `operatorCylinderProjection_coeFn`: $P_w f = \mathbf{1}_{[w]} f$ almost everywhere on the Cantor boundary.
- `operatorCylinderProjection_word_gaugeState`: $\varphi(P_w) = 2^{-|w|}$.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge

open Complex
open ContinuousLinearMap
open MeasureTheory
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge

/-- The single-bit operator cylinder projection on L^2(C, μ_C). -/
def branchProjection (b : Bool) : L2Boundary →L[ℂ] L2Boundary :=
  (normalizedPrependBitLpContinuousLinearMap b).comp (normalizedPrependBitLpAdjoint b)

@[simp] theorem operatorCylinderProjection_singleton_eq_branchProjection (b : Bool) :
    operatorCylinderProjection [b] = branchProjection b :=
  operatorCylinderProjection_singleton b

/-- Direct formula for the action of the adjoint isometry $V_b^\dagger$ on $L^2$. -/
theorem normalizedPrependBitLpAdjoint_apply (b : Bool) (f : L2Boundary) :
    normalizedPrependBitLpAdjoint b f = (prependBitLpNormFactor : ℂ) • prependBitLp b f := by
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
  cases b with
  | false =>
      have hF : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₀ := by
        rw [map_add]
        have hself : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀) = f₀ := by
          have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self false) f₀
          exact hcomp
        have hcross : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap true f₁) = 0 := by
          have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : false ≠ true)) f₁
          exact hcomp
        rw [hself, hcross, add_zero]
      have h_eq : normalizedPrependBitLpAdjoint false f = f₀ := by
        rw [← hf]
        exact hF
      exact h_eq
  | true =>
      have hT : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
        rw [map_add]
        have hcross : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀) = 0 := by
          have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : true ≠ false)) f₀
          exact hcomp
        have hself : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
          have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self true) f₁
          exact hcomp
        rw [hcross, hself, zero_add]
      have h_eq : normalizedPrependBitLpAdjoint true f = f₁ := by
        rw [← hf]
        exact hT
      exact h_eq

/-- The cylinder projector for length 1 acts as multiplication by the branch indicator on L^2. -/
theorem branchProjection_apply_eq_branchIndicator (b : Bool) (f : L2Boundary) :
    branchProjection b f = branchIndicatorLp b f := by
  let k : ℂ := prependBitLpNormFactor
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (ne_of_gt prependBitLpNormFactor_pos)
  dsimp [branchProjection]
  change (normalizedPrependBitLpContinuousLinearMap b) (normalizedPrependBitLpAdjoint b f) = branchIndicatorLp b f
  rw [normalizedPrependBitLpAdjoint_apply]
  rw [normalizedPrependBitLpContinuousLinearMap_apply,
    rawPrependBitLp_smul, rawPrependBitLp_prependBitLp]
  change (k⁻¹ : ℂ) • (k • branchIndicatorLp b f) = branchIndicatorLp b f
  rw [inv_smul_smul₀ hk]

theorem operatorCylinderProjection_single_apply_eq_branchIndicator (b : Bool) (f : L2Boundary) :
    (operatorCylinderProjection [b]) f = branchIndicatorLp b f := by
  rw [operatorCylinderProjection_singleton_eq_branchProjection]
  exact branchProjection_apply_eq_branchIndicator b f

/-- The cylinder projector P_b applied to f equals 1_{B_b} * f almost everywhere. -/
theorem operatorCylinderProjection_single_coeFn (b : Bool) (f : L2Boundary) :
    ((operatorCylinderProjection [b] f : L2Boundary) : Boundary → ℂ) =ᵐ[μC]
      (prependBitBranch b).indicator (fun x => f x) := by
  rw [operatorCylinderProjection_single_apply_eq_branchIndicator]
  exact (branchIndicatorFunction_memLp b f).coeFn_toLp

/-!
### General Word Cylinder Projector Multiplication
-/

/-- The indicator function of a general word cylinder set $[w]$ multiplied by $f$. -/
def wordIndicatorFunction (w : List Bool) (f : L2Boundary) : Boundary → ℂ :=
  (wordBranchSet w).indicator (fun x => f x)

/-- The function $\mathbf{1}_{[w]} f$ belongs to $L^2$. -/
theorem wordIndicatorFunction_memLp (w : List Bool) (f : L2Boundary) :
    MemLp (wordIndicatorFunction w f) 2 μC := by
  dsimp [wordIndicatorFunction]
  apply MemLp.indicator (measurableSet_wordBranchSet w)
  exact Lp.memLp f

/-- The element in `L2Boundary` corresponding to $\mathbf{1}_{[w]} f$. -/
def wordIndicatorLp (w : List Bool) (f : L2Boundary) : L2Boundary :=
  (wordIndicatorFunction_memLp w f).toLp (wordIndicatorFunction w f)

@[simp] theorem wordIndicatorLp_nil (f : L2Boundary) :
    wordIndicatorLp [] f = f := by
  apply Lp.ext
  have hto : (wordIndicatorLp [] f : Boundary → ℂ) =ᵐ[μC] wordIndicatorFunction [] f :=
    (wordIndicatorFunction_memLp [] f).coeFn_toLp
  filter_upwards [hto] with x hx
  rw [hx, wordIndicatorFunction, wordBranchSet_nil, Set.indicator_univ]

theorem wordIndicatorLp_smul (w : List Bool) (c : ℂ) (f : L2Boundary) :
    wordIndicatorLp w (c • f) = c • wordIndicatorLp w f := by
  classical
  apply Lp.ext
  have h1 : (wordIndicatorLp w (c • f) : Boundary → ℂ) =ᵐ[μC] wordIndicatorFunction w (c • f) :=
    (wordIndicatorFunction_memLp w (c • f)).coeFn_toLp
  have h2 : ((c • wordIndicatorLp w f : L2Boundary) : Boundary → ℂ) =ᵐ[μC] c • ((wordIndicatorLp w f : L2Boundary) : Boundary → ℂ) :=
    Lp.coeFn_smul c (wordIndicatorLp w f)
  have h3 : (wordIndicatorLp w f : Boundary → ℂ) =ᵐ[μC] wordIndicatorFunction w f :=
    (wordIndicatorFunction_memLp w f).coeFn_toLp
  have hsmul2 : ((c • f : L2Boundary) : Boundary → ℂ) =ᵐ[μC] c • (f : Boundary → ℂ) :=
    Lp.coeFn_smul c f
  filter_upwards [h1, h2, h3, hsmul2] with x h1x h2x h3x hs2x
  rw [h1x, h2x, Pi.smul_apply, h3x]
  dsimp [wordIndicatorFunction]
  by_cases hx : x ∈ wordBranchSet w
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hs2x]
    rfl
  · rw [Set.indicator_apply, if_neg hx, Set.indicator_apply, if_neg hx, mul_zero]

theorem rawPrependBitLp_wordIndicatorLp (b : Bool) (w : List Bool) (f : L2Boundary) :
    rawPrependBitLp b (wordIndicatorLp w (prependBitLp b f)) = wordIndicatorLp (b :: w) f := by
  classical
  apply Lp.ext
  have hraw : (rawPrependBitLp b (wordIndicatorLp w (prependBitLp b f)) : Boundary → ℂ) =ᵐ[μC]
      rawPrependBitFunction b (wordIndicatorLp w (prependBitLp b f)) :=
    (rawPrependBitFunction_memLp b (wordIndicatorLp w (prependBitLp b f))).coeFn_toLp
  have hword : (wordIndicatorLp w (prependBitLp b f) : Boundary → ℂ) =ᵐ[μC]
      wordIndicatorFunction w (prependBitLp b f) :=
    (wordIndicatorFunction_memLp w (prependBitLp b f)).coeFn_toLp
  have hword_tail := hword.comp_tendsto
    tail_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hpre : (prependBitLp b f : Boundary → ℂ) =ᵐ[μC] prependBitFunction b f :=
    (prependBitFunction_memLp b f).coeFn_toLp
  have hpre_tail := hpre.comp_tendsto
    tail_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hcons : (wordIndicatorLp (b :: w) f : Boundary → ℂ) =ᵐ[μC]
      wordIndicatorFunction (b :: w) f :=
    (wordIndicatorFunction_memLp (b :: w) f).coeFn_toLp
  filter_upwards [hraw, hword_tail, hpre_tail, hcons] with x hrawx hwordx hprex hconsx
  rw [hrawx, hconsx]
  dsimp [wordIndicatorFunction, rawPrependBitFunction]
  by_cases hxb : x ∈ prependBitBranch b
  · rw [Set.indicator_of_mem hxb]
    have h_tail_val : ((wordIndicatorLp w (prependBitLp b f) : Boundary → ℂ) ∘ tail) x =
        (wordIndicatorLp w (prependBitLp b f) : Boundary → ℂ) (tail x) := rfl
    rw [← h_tail_val, hwordx]
    dsimp [wordIndicatorFunction]
    have h_mem_iff : x ∈ wordBranchSet (b :: w) ↔ tail x ∈ wordBranchSet w := by
      rw [prependBitBranch_eq_range] at hxb
      rcases hxb with ⟨y, rfl⟩
      rw [tail_prependBit]
      dsimp [wordBranchSet]
      exact (prependBit_injective b).mem_set_image
    by_cases hxtail : tail x ∈ wordBranchSet w
    · have hxcons : x ∈ wordBranchSet (b :: w) := h_mem_iff.mpr hxtail
      have h_mem_image : x ∈ prependBit b '' wordBranchSet w := hxcons
      rw [Set.indicator_of_mem hxtail, Set.indicator_of_mem h_mem_image]
      have h_pre_tail_val : ((prependBitLp b f : Boundary → ℂ) ∘ tail) x =
          (prependBitLp b f : Boundary → ℂ) (tail x) := rfl
      rw [← h_pre_tail_val, hprex]
      dsimp [prependBitFunction]
      rw [prependBitBranch_eq_range] at hxb
      rcases hxb with ⟨y, rfl⟩
      rw [tail_prependBit]
    · have hxcons : x ∉ wordBranchSet (b :: w) := fun h => hxtail (h_mem_iff.mp h)
      rw [Set.indicator_apply, if_neg hxtail]
      rw [Set.indicator_apply, if_neg (show x ∉ prependBit b '' wordBranchSet w from hxcons)]
  · rw [Set.indicator_apply, if_neg hxb]
    have hxcons : x ∉ wordBranchSet (b :: w) := by
      intro hmem
      dsimp [wordBranchSet] at hmem
      rcases hmem with ⟨y, hy, rfl⟩
      apply hxb
      rw [prependBitBranch_eq_range]
      exact ⟨y, rfl⟩
    rw [Set.indicator_apply, if_neg (show x ∉ prependBit b '' wordBranchSet w from hxcons)]

/-- The general binary word cylinder projector acts on L² by multiplying by the indicator $\mathbf{1}_{[w]}$. -/
theorem operatorCylinderProjection_apply_eq_wordIndicator (w : List Bool) (f : L2Boundary) :
    operatorCylinderProjection w f = wordIndicatorLp w f := by
  revert f
  induction w with
  | nil =>
      intro f
      dsimp [operatorCylinderProjection, operatorWord, operatorWordDag]
      simp [wordIndicatorLp_nil]
  | cons b w ih =>
      intro f
      dsimp [operatorCylinderProjection, operatorWord, operatorWordDag]
      have h_star : star (branchOperator b) = normalizedPrependBitLpAdjoint b := by
        cases b <;> rfl
      have h_op : branchOperator b = normalizedPrependBitLpContinuousLinearMap b := by
        cases b <;> rfl
      have h_proj : (operatorWord w) ((operatorWordDag w) ((star (branchOperator b)) f)) =
          operatorCylinderProjection w ((star (branchOperator b)) f) := rfl
      rw [h_proj, h_star]
      let k : ℂ := prependBitLpNormFactor
      have hk : k ≠ 0 := by
        dsimp [k]
        exact_mod_cast (ne_of_gt prependBitLpNormFactor_pos)
      have hadj : normalizedPrependBitLpAdjoint b f = (k : ℂ) • prependBitLp b f :=
        normalizedPrependBitLpAdjoint_apply b f
      rw [hadj]
      rw [ih ((k : ℂ) • prependBitLp b f)]
      rw [wordIndicatorLp_smul]
      rw [h_op]
      rw [normalizedPrependBitLpContinuousLinearMap_apply]
      rw [rawPrependBitLp_smul]
      change (k⁻¹ : ℂ) • (k • rawPrependBitLp b (wordIndicatorLp w (prependBitLp b f))) =
        wordIndicatorLp (b :: w) f
      rw [inv_smul_smul₀ hk]
      exact rawPrependBitLp_wordIndicatorLp b w f

/-- The cylinder projector P_w applied to f equals 1_{[w]} * f almost everywhere. -/
theorem operatorCylinderProjection_coeFn (w : List Bool) (f : L2Boundary) :
    ((operatorCylinderProjection w f : L2Boundary) : Boundary → ℂ) =ᵐ[μC]
      (wordBranchSet w).indicator (fun x => f x) := by
  rw [operatorCylinderProjection_apply_eq_wordIndicator]
  exact (wordIndicatorFunction_memLp w f).coeFn_toLp

/-- The diagonal weight of the single-bit cylinder projection in the canonical gauge state is 1/2. -/
theorem operatorCylinderProjection_single_gaugeState (b : Bool) :
    canonicalGaugeState [b] [b] = 1 / 2 :=
  canonicalGaugeState_single_proj b

/-- The general word cylinder projector diagonal expectation is 2^{-|w|}. -/
theorem operatorCylinderProjection_word_gaugeState (w : List Bool) :
    canonicalGaugeState w w = (1 / 2 : ℂ) ^ w.length :=
  canonicalGaugeState_proj w

theorem canonicalGaugeState_word_eq_wordBranchSet_measure_toReal (w : List Bool) :
    canonicalGaugeState w w =
      ((μC (wordBranchSet w)).toReal : ℂ) := by
  rw [canonicalGaugeState_proj, μC_wordBranchSet]
  norm_num [ENNReal.toReal_ofNat]

end InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
