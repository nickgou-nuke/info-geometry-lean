import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Canonical.SouriauFisherCovariance
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A finite thermal sheet-exchange model

This file formalizes only a finite Gibbs model. Its two states have energies
`+β₀` and `-β₀`; exchanging the states while negating `β₀` preserves the
normalized Gibbs weights. This is a parameter/state covariance statement,
not an identification of temperature with spacetime, a thermofield-double
construction, or a claim of CPT symmetry.
-/

noncomputable section

open scoped BigOperators
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

namespace InfoGeometry.EmergentFisherMetric

/-- The two-state finite model with opposite values of its first observable. -/
def binarySheetDatum : CartanSouriauDatum (Fin 2) where
  momentMap x i := if i = 0 then if x = 0 then 1 else -1 else 0
  beta := fun _ => 0

/-- Exchange the two states and reverse the first inverse-temperature
coordinate. The second parameter is left fixed. -/
def exchangeParameter (beta : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -beta 0 else beta i

@[simp] theorem binarySheetDatum_moment_zero_zero :
    binarySheetDatum.momentMap 0 0 = 1 := by
  simp [binarySheetDatum]

@[simp] theorem binarySheetDatum_moment_one_zero :
    binarySheetDatum.momentMap 1 0 = -1 := by
  simp [binarySheetDatum]

@[simp] theorem binarySheetDatum_moment_second (x : Fin 2) :
    binarySheetDatum.momentMap x 1 = 0 := by
  simp [binarySheetDatum]

@[simp] theorem exchangeParameter_zero (beta : Fin 2 → ℝ) :
    exchangeParameter beta 0 = -beta 0 := by
  simp [exchangeParameter]

@[simp] theorem exchangeParameter_one (beta : Fin 2 → ℝ) :
    exchangeParameter beta 1 = beta 1 := by
  simp [exchangeParameter]

theorem exchangeParameter_involutive (beta : Fin 2 → ℝ) :
    exchangeParameter (exchangeParameter beta) = beta := by
  funext i
  fin_cases i <;> simp [exchangeParameter]

private def sheetParameterEquiv : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) where
  toFun := exchangeParameter
  invFun := exchangeParameter
  left_inv := exchangeParameter_involutive
  right_inv := exchangeParameter_involutive
  map_add' beta gamma := by
    funext i
    fin_cases i
    · simp [exchangeParameter]
      ring
    · simp [exchangeParameter]
  map_smul' c beta := by
    funext i
    fin_cases i <;> simp [exchangeParameter, smul_eq_mul]
  continuous_toFun := continuous_pi fun i => by
    fin_cases i
    · exact continuous_neg.comp (continuous_apply 0)
    · exact continuous_apply 1
  continuous_invFun := continuous_pi fun i => by
    fin_cases i
    · exact continuous_neg.comp (continuous_apply 0)
    · exact continuous_apply 1

/-- The state involution exchanging the two thermal sheets. -/
def sheetExchange : Equiv.Perm (Fin 2) := Equiv.swap 0 1

@[simp] theorem sheetExchange_zero : sheetExchange 0 = 1 := by
  simp [sheetExchange]

@[simp] theorem sheetExchange_one : sheetExchange 1 = 0 := by
  simp [sheetExchange]

/-- The pairing energy is invariant when both sheet and signed parameter are
exchanged. -/
theorem pairingEnergy_sheetExchange (beta : Fin 2 → ℝ) (x : Fin 2) :
    realPairingEnergy binarySheetDatum (exchangeParameter beta)
      (sheetExchange x) = realPairingEnergy binarySheetDatum beta x := by
  fin_cases x <;> simp [realPairingEnergy, binarySheetDatum, exchangeParameter,
    sheetExchange]

private def sheetFisherAction :
    InfoGeometry.Canonical.CartanStatePermutationAction
      (G := Unit) binarySheetDatum where
  Ad _ := sheetParameterEquiv
  stateEquiv _ := sheetExchange
  cocycle _ := 0
  pairing_cov _ beta x := by
    change realPairingEnergy binarySheetDatum (exchangeParameter beta)
        (sheetExchange x) = realPairingEnergy binarySheetDatum beta x - 0
    rw [pairingEnergy_sheetExchange]
    ring

theorem gibbsKernel_sheetExchange (beta : Fin 2 → ℝ) (x : Fin 2) :
    realGibbsKernel binarySheetDatum (exchangeParameter beta) (sheetExchange x) =
      realGibbsKernel binarySheetDatum beta x := by
  unfold realGibbsKernel
  rw [pairingEnergy_sheetExchange]

theorem gibbsPartition_sheetExchange (beta : Fin 2 → ℝ) :
    realGibbsPartition binarySheetDatum (exchangeParameter beta) =
      realGibbsPartition binarySheetDatum beta := by
  unfold realGibbsPartition
  rw [show (∑ x : Fin 2,
      realGibbsKernel binarySheetDatum (exchangeParameter beta) x) =
      ∑ x : Fin 2,
        realGibbsKernel binarySheetDatum (exchangeParameter beta) (sheetExchange x) by
          exact (Equiv.sum_comp sheetExchange _).symm]
  simp_rw [gibbsKernel_sheetExchange]

/-- The normalized Gibbs probability is covariant under the sheet exchange. -/
theorem gibbsWeight_sheetExchange (beta : Fin 2 → ℝ) (x : Fin 2) :
    realGibbsWeight binarySheetDatum (exchangeParameter beta) (sheetExchange x) =
      realGibbsWeight binarySheetDatum beta x := by
  unfold realGibbsWeight
  rw [gibbsKernel_sheetExchange, gibbsPartition_sheetExchange]

theorem gibbsWeight_sum_eq_one (beta : Fin 2 → ℝ) :
    (∑ x : Fin 2, realGibbsWeight binarySheetDatum beta x) = 1 :=
  realGibbsWeight_sum_eq_one binarySheetDatum beta

theorem gibbsPartition_pos (beta : Fin 2 → ℝ) :
    0 < realGibbsPartition binarySheetDatum beta :=
  realGibbsPartition_pos binarySheetDatum beta

@[simp] theorem mean_second_observable (beta : Fin 2 → ℝ) :
    InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta 1 = 0 := by
  simp [InfoGeometry.Lie.souriauChargeMean, binarySheetDatum]

/-- The mean of the signed two-state observable is the difference of the
normalized probabilities of the positive and negative states. -/
theorem mean_first_observable_eq_weight_difference (beta : Fin 2 → ℝ) :
    InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta 0 =
      realGibbsWeight binarySheetDatum beta 0 -
        realGibbsWeight binarySheetDatum beta 1 := by
  unfold InfoGeometry.Lie.souriauChargeMean
  rw [Fin.sum_univ_two]
  simp [binarySheetDatum]
  ring

/-- The Fisher form of this binary model has exactly one identifiable
parameter direction: it vanishes precisely on directions whose first
coordinate is zero. In particular, the unused second parameter is a genuine
null direction, so this model does not define a positive definite metric on
the full two-dimensional parameter space. -/
theorem fisherQuadratic_eq_zero_iff_first_eq_zero
    (beta v : Fin 2 → ℝ) :
    InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v = 0 ↔
      v 0 = 0 := by
  rw [InfoGeometry.Lie.fisherSouriauQuadratic_eq_zero_iff]
  constructor
  · intro h
    have hzero := h 0
    have hone := h 1
    have hdiff :
        (∑ i : Fin 2, v i *
          (binarySheetDatum.momentMap 0 i -
            InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta i)) -
        (∑ i : Fin 2, v i *
          (binarySheetDatum.momentMap 1 i -
            InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta i)) =
          2 * v 0 := by
      simp [binarySheetDatum]
      ring
    rw [hzero, hone] at hdiff
    nlinarith
  · intro hv x
    rw [Fin.sum_univ_two]
    rw [mean_second_observable]
    simp [binarySheetDatum, hv]

/-- In this two-sheet model the full Fisher quadratic form is the variance of
the single observable, hence its exact closed form is
`4 p₀ p₁ v₀²`.  The second coordinate is absent because its observable is
identically zero. -/
theorem fisherQuadratic_eq_sheet_weight_product
    (beta v : Fin 2 → ℝ) :
    InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v =
      4 * realGibbsWeight binarySheetDatum beta 0 *
        realGibbsWeight binarySheetDatum beta 1 * (v 0) ^ 2 := by
  rw [InfoGeometry.Lie.fisherSouriauQuadratic_eq_directionalVariance]
  let p₀ := realGibbsWeight binarySheetDatum beta 0
  let p₁ := realGibbsWeight binarySheetDatum beta 1
  have hp : p₀ + p₁ = 1 := by
    dsimp [p₀, p₁]
    simpa only [Fin.sum_univ_two] using gibbsWeight_sum_eq_one beta
  have hm₀ : InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta 0 = p₀ - p₁ := by
    rw [InfoGeometry.Lie.souriauChargeMean, Fin.sum_univ_two]
    simp [binarySheetDatum, p₀, p₁]
    ring
  have hm₁ : InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta 1 = 0 :=
    mean_second_observable beta
  rw [Fin.sum_univ_two]
  simp_rw [Fin.sum_univ_two, hm₀, hm₁]
  simp only [binarySheetDatum_moment_zero_zero,
    binarySheetDatum_moment_one_zero, binarySheetDatum_moment_second]
  have h₀ : 1 - (p₀ - p₁) = 2 * p₁ := by linarith [hp]
  have h₁ : -1 - (p₀ - p₁) = -2 * p₀ := by linarith [hp]
  rw [h₀, h₁]
  simp only [sub_zero, mul_zero, add_zero]
  rw [pow_two, pow_two]
  calc
    realGibbsWeight binarySheetDatum beta 0 *
        ((v 0 * (2 * p₁)) * (v 0 * (2 * p₁))) +
      realGibbsWeight binarySheetDatum beta 1 *
        ((v 0 * (-2 * p₀)) * (v 0 * (-2 * p₀))) =
      4 * realGibbsWeight binarySheetDatum beta 0 *
        realGibbsWeight binarySheetDatum beta 1 * (v 0) ^ 2 * (p₀ + p₁) := by
          dsimp [p₀, p₁]
          ring
    _ = 4 * realGibbsWeight binarySheetDatum beta 0 *
        realGibbsWeight binarySheetDatum beta 1 * (v 0) ^ 2 := by
          rw [hp, mul_one]

/-- The binary model's Fisher quadratic form is its Bernoulli variance times
the square of the identifiable parameter direction. This is the standard
one-dimensional Fisher geometry of a two-state exponential family. -/
theorem fisherQuadratic_eq_binary_variance
    (beta v : Fin 2 → ℝ) :
    InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v =
      (1 - (InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta 0) ^ 2) *
        (v 0) ^ 2 := by
  rw [fisherQuadratic_eq_sheet_weight_product,
    mean_first_observable_eq_weight_difference]
  have hp := gibbsWeight_sum_eq_one beta
  rw [Fin.sum_univ_two] at hp
  have hvariance :
      4 * realGibbsWeight binarySheetDatum beta 0 *
          realGibbsWeight binarySheetDatum beta 1 =
        1 - (realGibbsWeight binarySheetDatum beta 0 -
          realGibbsWeight binarySheetDatum beta 1) ^ 2 := by
    calc
      4 * realGibbsWeight binarySheetDatum beta 0 *
          realGibbsWeight binarySheetDatum beta 1 =
        (realGibbsWeight binarySheetDatum beta 0 +
          realGibbsWeight binarySheetDatum beta 1) ^ 2 -
          (realGibbsWeight binarySheetDatum beta 0 -
            realGibbsWeight binarySheetDatum beta 1) ^ 2 := by
              ring
      _ = 1 - (realGibbsWeight binarySheetDatum beta 0 -
          realGibbsWeight binarySheetDatum beta 1) ^ 2 := by
            rw [hp]
            norm_num
  rw [hvariance]

/-- Every state in the finite binary Gibbs model has strictly positive
probability, since its exponential kernel and partition function are positive. -/
theorem binarySheetWeight_pos (beta : Fin 2 → ℝ) (x : Fin 2) :
    0 < realGibbsWeight binarySheetDatum beta x := by
  unfold realGibbsWeight realGibbsKernel
  exact div_pos (Real.exp_pos _) (gibbsPartition_pos beta)

/-- The finite Fisher form is strictly positive exactly on the identifiable
first parameter direction. The second coordinate is a null direction, so the
model gives a positive semidefinite form rather than a Riemannian metric on
the full parameter plane. -/
theorem fisherQuadratic_pos_iff_first_ne_zero
    (beta v : Fin 2 → ℝ) :
    0 < InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v ↔
      v 0 ≠ 0 := by
  rw [fisherQuadratic_eq_sheet_weight_product]
  constructor
  · intro h hv
    simp [hv] at h
  · intro hv
    have h₀ := binarySheetWeight_pos beta 0
    have h₁ := binarySheetWeight_pos beta 1
    positivity

/-- The binary Fisher quadratic form is bounded above by the squared
identifiable direction, because the variance of a `{-1,1}`-valued observable
is at most one. -/
theorem fisherQuadratic_le_first_direction_sq
    (beta v : Fin 2 → ℝ) :
    InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v ≤
      (v 0) ^ 2 := by
  rw [fisherQuadratic_eq_binary_variance]
  have hmean : 0 ≤
      (InfoGeometry.Lie.souriauChargeMean binarySheetDatum beta 0) ^ 2 :=
    sq_nonneg _
  have hv : 0 ≤ (v 0) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hmean hv]

/-- The covariance Fisher quadratic form is invariant when both the state
labels and the signed parameter/direction coordinates are exchanged. -/
theorem fisherQuadratic_sheetExchange (beta v : Fin 2 → ℝ) :
    InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum (exchangeParameter beta)
      (exchangeParameter v) = InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v := by
  change InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum
      (sheetFisherAction.Ad () beta) (sheetFisherAction.Ad () v) =
    InfoGeometry.Lie.fisherSouriauQuadratic binarySheetDatum beta v
  exact InfoGeometry.Canonical.fisherSouriauQuadratic_covariance
    binarySheetDatum sheetFisherAction () beta v

end InfoGeometry.EmergentFisherMetric

end noncomputable section
