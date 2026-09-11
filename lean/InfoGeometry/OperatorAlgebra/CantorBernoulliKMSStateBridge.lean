import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Algebra.CuntzKMSState

/-!
# Cantor-Bernoulli Spatial Vector and Modular-Weight Bridge

This file formalizes the concrete spatial vector readout and finite
modular-weight compatibility at the numerical parameter $\beta = \ln 2$ on the spatial
$L^2(\mathcal{C}, \mu_C)$ representation of the binary Cuntz operators.
It does not by itself construct the canonical gauge-invariant C*-algebraic
KMS state, a faithful GNS representation, or a Tomita--Takesaki modular
group; those require the
conditional-expectation and GNS completion layer owned separately.

## Key Results:
- `vacuumL2`: The vacuum vector $\Omega = \mathbf{1} \in L^2(\mathcal{C}, \mu_C)$ with $\|\Omega\| = 1$.
- `cantorVacuumState`: The concrete spatial vector functional
  $\omega(A) = \langle \Omega, A \Omega \rangle$.
- `cantorVacuumState_proj`: Evaluates branch projectors $P_b = V_b V_b^\dagger$ to $\omega(P_b) = 1/2$.
- `beta_c_exp_neg`: Connects $\omega(P_b)$ numerically to $e^{-\beta_c}$ at the parameter $\beta_c = \ln 2$; this is not a KMS-state theorem.
- `cantorVacuumState_proj_eq_modularPhaseComplex`: Proves that the spatial
  functional $\omega$ evaluates
  branch projectors to the exact Wick-rotated complex modular phase of the Cuntz modular group
  `modularPhaseComplex 2 I`.
-/

noncomputable section

open MeasureTheory
open Complex
open scoped ENNReal
open scoped Classical

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
### 1. The Vacuum / Constant Section in L²
-/

/-- The constant function 1 on the Cantor boundary. -/
def vacuumFunction : Boundary → ℂ := fun _ => 1

theorem vacuumFunction_memLp : MemLp vacuumFunction 2 μC := by
  apply memLp_const

/-- The vacuum vector $\Omega = \mathbf{1} \in L^2(\mathcal{C}, \mu_C)$. -/
def vacuumL2 : L2Boundary := (vacuumFunction_memLp).toLp vacuumFunction

@[simp] theorem vacuumL2_coeFn :
    ((vacuumL2 : L2Boundary) : Boundary → ℂ) =ᵐ[μC] fun _ => (1 : ℂ) :=
  MemLp.coeFn_toLp vacuumFunction_memLp

theorem vacuumL2_inner_self : inner ℂ vacuumL2 vacuumL2 = 1 := by
  rw [L2.inner_def]
  have hvac := vacuumL2_coeFn
  have hint : (fun x => inner ℂ ((vacuumL2 : Boundary → ℂ) x) ((vacuumL2 : Boundary → ℂ) x)) =ᵐ[μC]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [hvac] with x hx
    simp only [hx]
    simp [inner]
  rw [integral_congr_ae hint]
  rw [integral_const]
  have hmeas : μC.real Set.univ = 1 := by
    dsimp [Measure.real]
    rw [measure_univ, ENNReal.toReal_one]
  rw [hmeas]
  simp

/-!
### 2. The Concrete Cantor C*-State
-/

/-- The concrete spatial state on $\mathcal{B}(L^2(\mathcal{C}, \mu_C))$:
$\omega(A) = \langle \Omega, A \Omega \rangle$. -/
def cantorVacuumState (A : BoundedL2Operator) : ℂ :=
  inner ℂ vacuumL2 (A vacuumL2)

theorem cantorVacuumState_id :
    cantorVacuumState (ContinuousLinearMap.id ℂ L2Boundary) = 1 := by
  dsimp [cantorVacuumState]
  exact vacuumL2_inner_self

/-- The cylinder branch projectors $P_b = V_b V_b^\dagger$. -/
def P (b : Bool) : BoundedL2Operator :=
  (normalizedPrependBitLpContinuousLinearMap b).comp (normalizedPrependBitLpAdjoint b)

theorem P_eq_operatorCylinderProjection (b : Bool) :
    P b =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection [b] := by
  symm
  exact InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection_singleton b

theorem normalizedPrependBitLp_comp_adjoint_apply (b : Bool) (f : L2Boundary) :
    (normalizedPrependBitLpContinuousLinearMap b) (normalizedPrependBitLpAdjoint b f) =
      branchIndicatorLp b f := by
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
  have hV0 : normalizedPrependBitLpContinuousLinearMap false f₀ = branchIndicatorLp false f := by
    dsimp [f₀]
    rw [normalizedPrependBitLpContinuousLinearMap_apply,
      rawPrependBitLp_smul, rawPrependBitLp_prependBitLp]
    change (k⁻¹ : ℂ) • (k • branchIndicatorLp false f) = _
    rw [inv_smul_smul₀ hk]
  have hV1 : normalizedPrependBitLpContinuousLinearMap true f₁ = branchIndicatorLp true f := by
    dsimp [f₁]
    rw [normalizedPrependBitLpContinuousLinearMap_apply,
      rawPrependBitLp_smul, rawPrependBitLp_prependBitLp]
    change (k⁻¹ : ℂ) • (k • branchIndicatorLp true f) = _
    rw [inv_smul_smul₀ hk]
  cases b
  · have hF : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₀ := by
      rw [map_add]
      have hself : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap false f₀) = f₀ := by
        have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self false) f₀
        exact hcomp
      have hcross : (normalizedPrependBitLpAdjoint false) (normalizedPrependBitLpContinuousLinearMap true f₁) = 0 := by
        have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : false ≠ true)) f₁
        exact hcomp
      rw [hself, hcross, add_zero]
    have h_adj : normalizedPrependBitLpAdjoint false f = f₀ := by
      rw [← hf, hF]
    rw [h_adj, hV0]
  · have hT : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀ + normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
      rw [map_add]
      have hcross : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap false f₀) = 0 := by
        have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (by decide : true ≠ false)) f₀
        exact hcomp
      have hself : (normalizedPrependBitLpAdjoint true) (normalizedPrependBitLpContinuousLinearMap true f₁) = f₁ := by
        have hcomp := ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_self true) f₁
        exact hcomp
      rw [hcross, hself, zero_add]
    have h_adj : normalizedPrependBitLpAdjoint true f = f₁ := by
      rw [← hf, hT]
    rw [h_adj, hV1]

theorem P_apply (b : Bool) (f : L2Boundary) :
    P b f = branchIndicatorLp b f :=
  normalizedPrependBitLp_comp_adjoint_apply b f

/-! The operator-tree singleton projection is the same multiplication-by-
branch-indicator operator as the spatial Bernoulli projection. -/
theorem operatorCylinderProjection_singleton_apply (b : Bool) (f : L2Boundary) :
    CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection [b] f =
      branchIndicatorLp b f := by
  rw [← P_eq_operatorCylinderProjection b]
  exact P_apply b f

theorem μC_prependBitBranch (b : Bool) : μC (prependBitBranch b) = 1 / 2 := by
  have huniv := prependBitBranchProductMeasure_univ b
  have hbranch : prependBitBranchProductMeasure b =
      (2 : ℝ≥0∞) • μC.restrict (prependBitBranch b) := by
    rw [prependBitBranch_eq_range,
      ← prependBit_measure_map_eq_branchProductMeasure b,
      prependBit_measure_map_eq_two_restrict_branch]
  rw [hbranch] at huniv
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ] at huniv
  have hhalf : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    simpa [one_div] using (ENNReal.inv_mul_cancel (by norm_num) (by norm_num))
  calc
    μC (prependBitBranch b) = (1 / 2 : ℝ≥0∞) * (2 * μC (prependBitBranch b)) := by
      rw [← mul_assoc, hhalf, one_mul]
    _ = 1 / 2 * 1 := by rw [huniv]
    _ = 1 / 2 := mul_one (1 / 2)

theorem cantorVacuumState_proj (b : Bool) :
    cantorVacuumState (P b) = (1 / 2 : ℂ) := by
  dsimp [cantorVacuumState]
  rw [P_apply, L2.inner_def]
  have hvac := vacuumL2_coeFn
  have hproj : ((branchIndicatorLp b vacuumL2 : L2Boundary) : Boundary → ℂ) =ᵐ[μC]
      branchIndicatorFunction b vacuumL2 :=
    MemLp.coeFn_toLp (branchIndicatorFunction_memLp b vacuumL2)
  have hint : (fun x => inner ℂ ((vacuumL2 : Boundary → ℂ) x)
      (((branchIndicatorLp b vacuumL2 : L2Boundary) : Boundary → ℂ) x)) =ᵐ[μC]
      (fun x => (prependBitBranch b).indicator (fun _ => (1 : ℂ)) x) := by
    filter_upwards [hvac, hproj] with x hx hpx
    rw [hx, hpx]
    dsimp [branchIndicatorFunction]
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hxb : x ∈ prependBitBranch b
    · rw [if_pos hxb, if_pos hxb]
      simp [hx]
    · rw [if_neg hxb, if_neg hxb]
      simp
  rw [integral_congr_ae hint]
  rw [integral_indicator (measurableSet_prependBitBranch b)]
  rw [integral_const]
  have hmeas : (μC.restrict (prependBitBranch b)).real Set.univ = 1 / 2 := by
    dsimp [Measure.real]
    rw [Measure.restrict_apply_univ, μC_prependBitBranch b]
    exact ENNReal.toReal_div (1 : ℝ≥0∞) (2 : ℝ≥0∞)
  rw [hmeas]
  simp

/-- The spatial Bernoulli vector and the finite gauge-word kernel agree on
    the length-one cylinder projections.  This is a generator-level bridge;
    it does not identify the two functionals on the completed C*-algebra. -/
theorem cantorVacuumState_proj_eq_gaugeWord (b : Bool) :
    cantorVacuumState (P b) =
      canonicalGaugeState [b] [b] := by
  rw [cantorVacuumState_proj, canonicalGaugeState_single_proj]

/-!
### 3. Thermal KMS Flow at Inverse Temperature $\beta = \ln 2$
-/

/-- The critical inverse Hawking/KMS temperature: $\beta_c = \ln 2$. -/
def beta_c : ℝ := Real.log 2

theorem beta_c_exp_neg :
    Complex.exp (- (beta_c : ℂ)) = 1 / 2 := by
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hlog : (beta_c : ℂ) = (Real.log 2 : ℂ) := rfl
  rw [hlog, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log hpos]
  push_cast
  ring

theorem cantorVacuumState_proj_eq_exp_weight (b : Bool) :
    cantorVacuumState (P b) = Complex.exp (- (beta_c : ℂ)) := by
  rw [cantorVacuumState_proj, beta_c_exp_neg]

/- This compatibility is only a numerical equality for the spatial vector
   functional.  It is not a KMS-state theorem; retain the old name only as a
   deprecated compatibility alias for downstream code. -/
@[deprecated cantorVacuumState_proj_eq_exp_weight (since := "2026-08-14")]
theorem cantorVacuumState_proj_eq_KMS_weight (b : Bool) :
    cantorVacuumState (P b) = Complex.exp (- (beta_c : ℂ)) :=
  cantorVacuumState_proj_eq_exp_weight b

/-- The spatial state $\omega$ evaluates the branch projectors to the exact
Wick-rotated complex modular phase for the binary generator at imaginary time $i$. -/
theorem cantorVacuumState_proj_eq_modularPhaseComplex (b : Bool) :
    cantorVacuumState (P b) =
      InfoGeometry.Algebra.CuntzKMSCondition.modularPhaseComplex 2 I := by
  dsimp [InfoGeometry.Algebra.CuntzKMSCondition.modularPhaseComplex]
  have h : I * I * (Real.log (2 : ℝ) : ℂ) = - (beta_c : ℂ) := by
    dsimp [beta_c]
    rw [Complex.I_mul_I]
    ring
  rw [h, beta_c_exp_neg, cantorVacuumState_proj]

end InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
