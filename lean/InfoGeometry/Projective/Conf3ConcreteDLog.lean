import InfoGeometry.Projective.TwistorConfigurationSpace
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Projective.ProjectiveLogarithmicBoundaryGeometry
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Concrete coefficient layer for the `d log Q` packet

This owner records the coefficient of the logarithmic form on the finite
non-isotropic configuration carrier.  It supplies:
1. The scalar coefficient `1 / Q(x_i - x_j)`.
2. The ordinary configuration-space logarithmic forms `ω_ij = (dz_i - dz_j) / (z_i - z_j)`.
3. The exact, unconditional proof that concrete differential forms on `Conf_3(K)`
   satisfy the 3-term Arnold-Cohen relation in any exterior algebra.
-/

namespace InfoGeometry.Projective.Conf3ConcreteDLog

open InfoGeometry.Projective.TwistorConfigurationSpace
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive
open InfoGeometry.Projective.ProjectiveLogarithmicBoundaryGeometry
open InfoGeometry.Canonical.ArnoldCohenBCFWBridge

noncomputable section

/-- The coefficient of the logarithmic form attached to an ordered pair. -/
def dlogCoefficient (X : FQ3) (i j : Fin 3) : ℂ :=
  1 / X.separation i j

/-- Three explicit points on an affine line in `ℂ⁴`. -/
def standardPoints : TripleC4 :=
  fun i k => if k = 0 then (i.1 : ℂ) else 0

theorem standardPoints_pairwise_non_isotropic :
    PairwiseNonIsotropic standardPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [standardPoints, quadSeparation, quadForm, Fin.sum_univ_succ] <;>
    norm_num

/-- A concrete non-isotropic configuration for chart-level tests. -/
def standardConfiguration : FQ3 :=
  ⟨standardPoints, standardPoints_pairwise_non_isotropic⟩

/-- The affine translation direction used for a concrete one-parameter chart. -/
def translationDirection : C4 :=
  fun k => if k = 0 then 1 else 0

/-- A nonconstant affine chart obtained by translating all three points. -/
def affineTranslationChart (t : ℝ) : FQ3 :=
  ⟨fun i => standardPoints i + (t : ℂ) • translationDirection,
    by
      intro i j hij
      rw [quadSeparation_translate]
      exact standardPoints_pairwise_non_isotropic i j hij⟩

theorem affineTranslationChart_separation
    (t : ℝ) (i j : Fin 3) :
    (affineTranslationChart t).separation i j = standardConfiguration.separation i j := by
  exact quadSeparation_translate (standardPoints i) (standardPoints j)
    ((t : ℂ) • translationDirection)

/- A nonconstant chart which rescales every separation by a nonzero factor. -/
def exponentialScalingChart (t : ℝ) : FQ3 :=
  ⟨fun i => Complex.exp (t : ℂ) • standardPoints i,
    by
      intro i j hij
      rw [quadSeparation_smul]
      apply mul_ne_zero
      · exact pow_ne_zero 2 (Complex.exp_ne_zero (t : ℂ))
      · exact standardPoints_pairwise_non_isotropic i j hij⟩

def scaleConfiguration (c : ℂ) (X : FQ3) (hc : c ≠ 0) : FQ3 :=
  ⟨fun i => c • X.points i,
    by
      intro i j hij
      rw [quadSeparation_smul]
      exact mul_ne_zero (pow_ne_zero 2 hc)
        (X.pairwise_non_isotropic i j hij)⟩

theorem scaleConfiguration_separation
    (c : ℂ) (X : FQ3) (hc : c ≠ 0) (i j : Fin 3) :
    (scaleConfiguration c X hc).separation i j =
      c ^ 2 * X.separation i j := by
  exact quadSeparation_smul c (X.points i) (X.points j)

theorem dlogCoefficient_scaleConfiguration
    (c : ℂ) (X : FQ3) (hc : c ≠ 0) (i j : Fin 3) :
    dlogCoefficient (scaleConfiguration c X hc) i j =
      c⁻¹ ^ 2 * dlogCoefficient X i j := by
  unfold dlogCoefficient
  rw [scaleConfiguration_separation]
  field_simp

theorem exponentialScalingChart_separation
    (t : ℝ) (i j : Fin 3) :
    (exponentialScalingChart t).separation i j =
      (Complex.exp (t : ℂ)) ^ 2 * standardConfiguration.separation i j := by
  exact quadSeparation_smul (Complex.exp (t : ℂ)) (standardPoints i)
    (standardPoints j)

theorem exponentialScalingChart_separation_norm
    (t : ℝ) (i j : Fin 3) :
    ‖(exponentialScalingChart t).separation i j‖ =
      Real.exp (2 * t) * ‖standardConfiguration.separation i j‖ := by
  rw [exponentialScalingChart_separation]
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.ofReal_re]
  rw [pow_two, ← Real.exp_add]
  have h2 : t + t = 2 * t := by ring
  rw [h2]

/-- The real-valued logarithmic potential on the non-isotropic complement. -/
noncomputable def logPotential (X : FQ3) (i j : Fin 3) : ℝ :=
  Real.log ‖X.separation i j‖

/-- Pullback of the projective logarithmic potential along a real chart. -/
def chartLogPotential (γ : ℝ → FQ3) (i j : Fin 3) : InfoGeometry.LogPotential ℝ :=
  fun t => logPotential (γ t) i j

theorem exponentialScalingChart_logPotential
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    logPotential (exponentialScalingChart t) i j =
      2 * t + logPotential standardConfiguration i j := by
  unfold logPotential
  rw [exponentialScalingChart_separation_norm]
  have hsep : ‖standardConfiguration.separation i j‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (standardConfiguration.pairwise_non_isotropic i j hij)
  rw [Real.log_mul (by positivity) hsep, Real.log_exp]

theorem exponentialScalingChart_chartLogPotential_eq_affine
    (i j : Fin 3) (hij : i ≠ j) :
    chartLogPotential exponentialScalingChart i j =
      fun t => 2 * t + logPotential standardConfiguration i j := by
  funext t
  exact exponentialScalingChart_logPotential t i j hij

theorem hasDerivAt_exponentialScalingChart_logPotential
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    HasDerivAt (fun s => logPotential (exponentialScalingChart s) i j) 2 t := by
  have h := (hasDerivAt_id t).const_mul 2 |>.add_const
    (logPotential standardConfiguration i j)
  convert h using 1 <;> norm_num
  funext s
  exact exponentialScalingChart_logPotential s i j hij

theorem hasDerivAt_exponentialScalingChart_chartLogPotential
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    HasDerivAt (chartLogPotential exponentialScalingChart i j) 2 t := by
  simpa [chartLogPotential] using
    hasDerivAt_exponentialScalingChart_logPotential t i j hij

theorem deriv_exponentialScalingChart_chartLogPotential
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    deriv (chartLogPotential exponentialScalingChart i j) t = 2 := by
  exact (hasDerivAt_exponentialScalingChart_chartLogPotential t i j hij).deriv

theorem secondDeriv_exponentialScalingChart_chartLogPotential
    (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    deriv (fun s => deriv (chartLogPotential exponentialScalingChart i j) s) t = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
  have heq : (fun s => deriv (chartLogPotential exponentialScalingChart i j) s) =
      (fun _ : ℝ => (2 : ℝ)) := by
    funext s
    exact deriv_exponentialScalingChart_chartLogPotential s i j hij
  rw [heq]
  exact hconst.deriv

theorem exp_logPotential (X : FQ3) (i j : Fin 3) (hij : i ≠ j) :
    Real.exp (logPotential X i j) = ‖X.separation i j‖ := by
  unfold logPotential
  rw [Real.exp_log]
  exact norm_pos_iff.mpr (X.pairwise_non_isotropic i j hij)

theorem exp_chartLogPotential
    (γ : ℝ → FQ3) (i j : Fin 3) (t : ℝ) (hij : i ≠ j) :
    Real.exp (chartLogPotential γ i j t) = ‖(γ t).separation i j‖ := by
  exact exp_logPotential (γ t) i j hij

/-- Chain rule for the real logarithmic potential along a regular positive
    chart. The projective chart supplies the hypotheses separately. -/
theorem hasDerivAt_log_of_hasDerivAt
    (q : ℝ → ℝ) (q' t : ℝ) (hq : 0 < q t)
    (hderiv : HasDerivAt q q' t) :
    HasDerivAt (fun s => Real.log (q s)) (q' / q t) t := by
  simpa using hderiv.log (ne_of_gt hq)

theorem logPotential_permute
    (σ : Equiv.Perm (Fin 3)) (X : FQ3) (i j : Fin 3) :
    logPotential (X.permute σ) i j = logPotential X (σ i) (σ j) := by
  unfold logPotential
  rw [FQ3.separation_permute]

/-- The scalar coefficient of the ordinary configuration-space form
    `d log (z_i - z_j)`. -/
def linearDLogCoefficient {K : Type*} [Field K] (z : Fin 3 → K) (i j : Fin 3) : K :=
  1 / (z i - z j)

/-- **Theorem**: The scalar coefficients of configuration forms satisfy the Arnold partial fraction sum. -/
theorem linearDLogCoefficient_arnold {K : Type*} [Field K]
    (z : Fin 3 → K)
    (h₁₂ : z 0 ≠ z 1) (h₂₃ : z 1 ≠ z 2) (h₃₁ : z 2 ≠ z 0) :
    linearDLogCoefficient z 0 1 * linearDLogCoefficient z 1 2 +
      linearDLogCoefficient z 1 2 * linearDLogCoefficient z 2 0 +
      linearDLogCoefficient z 2 0 * linearDLogCoefficient z 0 1 = 0 := by
  unfold linearDLogCoefficient
  have d12 : z 0 - z 1 ≠ 0 := sub_ne_zero.mpr h₁₂
  have d23 : z 1 - z 2 ≠ 0 := sub_ne_zero.mpr h₂₃
  have d31 : z 2 - z 0 ≠ 0 := sub_ne_zero.mpr h₃₁
  field_simp [d12, d23, d31]
  ring

/-- Concrete logarithmic form on `Conf_3(K)` constructed from 1-forms `dz`. -/
def conf3ConcreteForm
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (dz : Fin 3 → M) (z : Fin 3 → K) (i j : Fin 3) : M :=
  (linearDLogCoefficient z i j) • (dz i - dz j)

/-- 
🏆 **THEOREM: Exact Arnold-Cohen Relation for Concrete Differential Forms on Conf_3(K)**

Proves unconditionally (with no abstract certificate fields) that for any configuration
`z ∈ Conf_3(K)`, the concrete logarithmic 1-forms `ω_ij = (dz_i - dz_j)/(z_i - z_j)`
satisfy the 3-term Arnold relation in any exterior form algebra:
$$\omega_{01} \wedge \omega_{12} + \omega_{12} \wedge \omega_{20} + \omega_{20} \wedge \omega_{01} = 0.$$
-/
theorem conf3_concrete_arnold_relation
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (alg : ExteriorFormAlgebra (R := K) M)
    (dz : Fin 3 → M) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0) :
    alg.wedge (conf3ConcreteForm dz z 0 1) (conf3ConcreteForm dz z 1 2) +
    alg.wedge (conf3ConcreteForm dz z 1 2) (conf3ConcreteForm dz z 2 0) +
    alg.wedge (conf3ConcreteForm dz z 2 0) (conf3ConcreteForm dz z 0 1) = 0 := by
  dsimp [conf3ConcreteForm]
  rw [wedge_smul_left, wedge_smul_right, ← smul_assoc, smul_eq_mul]
  rw [wedge_smul_left, wedge_smul_right, ← smul_assoc, smul_eq_mul]
  rw [wedge_smul_left, wedge_smul_right, ← smul_assoc, smul_eq_mul]
  have h_sub_l := wedge_sub_left alg
  have h_sub_r := wedge_sub_right alg
  have h_alt := alg.wedge_alternating
  have h_anti := alg.wedge_anticomm
  have t : alg.wedge (dz 0 - dz 1) (dz 1 - dz 2) =
      alg.wedge (dz 0) (dz 1) - alg.wedge (dz 0) (dz 2) + alg.wedge (dz 1) (dz 2) := by
    rw [h_sub_l, h_sub_r, h_sub_r, h_alt (dz 1)]
    abel
  have u : alg.wedge (dz 1 - dz 2) (dz 2 - dz 0) =
      alg.wedge (dz 0) (dz 1) - alg.wedge (dz 0) (dz 2) + alg.wedge (dz 1) (dz 2) := by
    rw [h_sub_l, h_sub_r, h_sub_r, h_alt (dz 2), h_anti (dz 1) (dz 0), h_anti (dz 2) (dz 0)]
    abel
  have v : alg.wedge (dz 2 - dz 0) (dz 0 - dz 1) =
      alg.wedge (dz 0) (dz 1) - alg.wedge (dz 0) (dz 2) + alg.wedge (dz 1) (dz 2) := by
    rw [h_sub_l, h_sub_r, h_sub_r, h_alt (dz 0), h_anti (dz 2) (dz 0), h_anti (dz 2) (dz 1)]
    abel
  rw [t, u, v]
  let Δ := alg.wedge (dz 0) (dz 1) - alg.wedge (dz 0) (dz 2) + alg.wedge (dz 1) (dz 2)
  change (linearDLogCoefficient z 0 1 * linearDLogCoefficient z 1 2) • Δ +
         (linearDLogCoefficient z 1 2 * linearDLogCoefficient z 2 0) • Δ +
         (linearDLogCoefficient z 2 0 * linearDLogCoefficient z 0 1) • Δ = 0
  rw [← add_smul, ← add_smul, linearDLogCoefficient_arnold z h01 h12 h20, zero_smul]

/-- BCFW pole factorization on concrete configuration-space forms. -/
theorem conf3_concrete_bcfw_pole_factorization
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (alg : ExteriorFormAlgebra (R := K) M)
    (dz : Fin 3 → M) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0) :
    alg.wedge (conf3ConcreteForm dz z 0 1) (conf3ConcreteForm dz z 1 2) =
      - (alg.wedge (conf3ConcreteForm dz z 1 2) (conf3ConcreteForm dz z 2 0) +
         alg.wedge (conf3ConcreteForm dz z 2 0) (conf3ConcreteForm dz z 0 1)) := by
  have h := conf3_concrete_arnold_relation alg dz z h01 h12 h20
  rw [add_assoc] at h
  exact eq_neg_of_add_eq_zero_left h

/- The concrete configuration coefficient uses exactly the repository's
   canonical scalar `d log` kernel; no second logarithmic API is introduced. -/
theorem dlogCoefficient_eq_grothendieck_dlog
    (X : FQ3) (i j : Fin 3) :
    dlogCoefficient X i j = grothendieck_dlog (X.separation i j) := by
  rfl

/-- The concrete logarithmic coefficient is equivariant under relabelling. -/
theorem dlogCoefficient_permute
    (σ : Equiv.Perm (Fin 3)) (X : FQ3) (i j : Fin 3) :
    dlogCoefficient (X.permute σ) i j = dlogCoefficient X (σ i) (σ j) := by
  unfold dlogCoefficient
  rw [FQ3.separation_permute]

/-- Reversing an edge does not change its quadratic logarithmic coefficient. -/
theorem dlogCoefficient_symm (X : FQ3) (i j : Fin 3) :
    dlogCoefficient X i j = dlogCoefficient X j i := by
  unfold dlogCoefficient
  simpa [FQ3.separation] using congrArg (fun z : ℂ => 1 / z)
    (quadSeparation_comm (X.points i) (X.points j))

/-- Every coefficient attached to a genuine ordered edge is defined. -/
theorem dlogCoefficient_ne_zero (X : FQ3) (i j : Fin 3) (hij : i ≠ j) :
    dlogCoefficient X i j ≠ 0 := by
  unfold dlogCoefficient
  simp [one_div, X.pairwise_non_isotropic i j hij]

/-- The cyclic coefficient sum used by the linear Arnold identity. -/
def dlogCoefficientArnoldSum (X : FQ3) : ℂ :=
  dlogCoefficient X 0 1 * dlogCoefficient X 1 2 +
    dlogCoefficient X 1 2 * dlogCoefficient X 2 0 +
    dlogCoefficient X 2 0 * dlogCoefficient X 0 1

theorem dlogCoefficientArnoldSum_scaleConfiguration
    (c : ℂ) (X : FQ3) (hc : c ≠ 0) :
    dlogCoefficientArnoldSum (scaleConfiguration c X hc) =
      c⁻¹ ^ 4 * dlogCoefficientArnoldSum X := by
  unfold dlogCoefficientArnoldSum
  simp only [dlogCoefficient_scaleConfiguration]
  ring

/-- The present quadratic-separation scaffold does not satisfy the linear
    Arnold partial-fraction identity, even on the standard configuration. -/
theorem standardConfiguration_dlogCoefficient_arnold_sum :
    dlogCoefficient standardConfiguration 0 1 *
        dlogCoefficient standardConfiguration 1 2 +
      dlogCoefficient standardConfiguration 1 2 *
        dlogCoefficient standardConfiguration 2 0 +
      dlogCoefficient standardConfiguration 2 0 *
        dlogCoefficient standardConfiguration 0 1 = (3 / 2 : ℂ) := by
  unfold dlogCoefficient FQ3.separation standardConfiguration standardPoints
    quadSeparation quadForm
  norm_num [Fin.sum_univ_succ]

theorem standardConfiguration_dlogCoefficient_arnold_sum_ne_zero :
    dlogCoefficientArnoldSum standardConfiguration ≠ 0 := by
  unfold dlogCoefficientArnoldSum
  rw [standardConfiguration_dlogCoefficient_arnold_sum]
  norm_num

theorem standardConfiguration_not_arnold_coefficient_relation :
    ¬ dlogCoefficientArnoldSum standardConfiguration = 0 :=
  standardConfiguration_dlogCoefficient_arnold_sum_ne_zero

theorem dlogCoefficientArnoldSum_scale_standard_ne_zero
    (c : ℂ) (hc : c ≠ 0) :
    dlogCoefficientArnoldSum (scaleConfiguration c standardConfiguration hc) ≠ 0 := by
  rw [dlogCoefficientArnoldSum_scaleConfiguration]
  unfold dlogCoefficientArnoldSum
  rw [standardConfiguration_dlogCoefficient_arnold_sum]
  exact mul_ne_zero (pow_ne_zero 4 (inv_ne_zero hc)) (by norm_num)

end
end InfoGeometry.Projective.Conf3ConcreteDLog
