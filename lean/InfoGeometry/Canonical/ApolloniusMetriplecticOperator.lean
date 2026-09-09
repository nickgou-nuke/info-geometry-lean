import InfoGeometry.Quantum.ApolloniusFisherInformation
import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.Krein.Metric

/-!
# The Apollonius Fisher--Onsager operator

This is the native finite-dimensional non-equilibrium operator attached to the
existing Apollonius Fisher metric.  It is an Onsager operator on the tangent
carrier `Fin 2 → ℝ`; no analytic flow or spectral claim is made here.
-/

namespace InfoGeometry.Canonical.ApolloniusMetriplecticOperator

open InfoGeometry.Quantum.ApolloniusFisherInformation

noncomputable section

def apolloniusOnsagerOperator (st : ApolloniusState) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := fun v => fun i =>
    (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) * v i
  map_add' := by
    intro v w
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro a v
    funext i
    simp only [Pi.smul_apply]
    change _ * (a * v i) = a * (_ * v i)
    ring

theorem apolloniusOnsagerOperator_apply (st : ApolloniusState)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    apolloniusOnsagerOperator st v i =
      (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) * v i := rfl

/-- The Onsager map is the linear map represented by the existing Fisher
    matrix, with the repository's `Fin 2` coordinate order. -/
theorem apolloniusOnsagerOperator_eq_fisher_action
    (st : ApolloniusState) (v : Fin 2 → ℝ) :
    apolloniusOnsagerOperator st v =
      fun i => ∑ j, apolloniusFisherMatrix st i j * v j := by
  funext i
  fin_cases i <;>
    simp [apolloniusOnsagerOperator, apolloniusFisherMatrix]

/-- One explicit Euler dissipative step on the finite tangent carrier. -/
def apolloniusDissipativeStep (st : ApolloniusState) (τ : ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.id - τ • apolloniusOnsagerOperator st

theorem apolloniusDissipativeStep_apply
    (st : ApolloniusState) (τ : ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    apolloniusDissipativeStep st τ v i =
      (1 - τ / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) * v i := by
  change v i - τ * (apolloniusOnsagerOperator st v i) = _
  rw [apolloniusOnsagerOperator_apply]
  ring

theorem apolloniusDissipativeStep_zero_at_inverse_scale
    (st : ApolloniusState) (v : Fin 2 → ℝ) :
    apolloniusDissipativeStep st
      ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) v = 0 := by
  funext i
  rw [apolloniusDissipativeStep_apply]
  have hden : (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 ≠ 0 :=
    ne_of_gt st.h_non_sing
  change (1 - ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) /
      ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) * v i = 0
  have hratio :
      1 - ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) /
        ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) = 0 := by
    have hpos : 0 < (st.sigma * 2 - 1) ^ 2 + 2 ^ 2 * st.t ^ 2 := by
      nlinarith [st.h_non_sing]
    field_simp [ne_of_gt hpos]
    norm_num
  rw [hratio]
  simp

/-! ### Finite-dimensional Krein pairing consequences -/

open InfoGeometry.Krein

def apolloniusKreinPairing (v w : Fin 2 → ℝ) : ℝ :=
  hessian_indefinite_formCoord (v 0, v 1) (w 0, w 1)

theorem apolloniusKreinPairing_eq_coordinate_formula
    (v w : Fin 2 → ℝ) :
    apolloniusKreinPairing v w = v 0 * w 1 + w 0 * v 1 := by
  unfold apolloniusKreinPairing hessian_indefinite_formCoord
  simp
  ring

theorem apolloniusKreinPairing_left_nondegenerate
    (v : Fin 2 → ℝ) :
    (∀ w : Fin 2 → ℝ, apolloniusKreinPairing v w = 0) ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    fin_cases i
    · have h := hv ![0, 1]
      rw [apolloniusKreinPairing_eq_coordinate_formula] at h
      simpa using h
    · have h := hv ![1, 0]
      rw [apolloniusKreinPairing_eq_coordinate_formula] at h
      simpa using h
  · intro hv w
    subst v
    rw [apolloniusKreinPairing_eq_coordinate_formula]
    simp

theorem apolloniusKreinPairing_self_eq_two_mul
    (v : Fin 2 → ℝ) :
    apolloniusKreinPairing v v = 2 * (v 0 * v 1) := by
  rw [apolloniusKreinPairing_eq_coordinate_formula]
  ring

theorem apolloniusKreinPairing_null_iff
    (v : Fin 2 → ℝ) :
    apolloniusKreinPairing v v = 0 ↔ v 0 = 0 ∨ v 1 = 0 := by
  rw [apolloniusKreinPairing_self_eq_two_mul]
  constructor
  · intro h
    rcases mul_eq_zero.mp (by linarith : v 0 * v 1 = 0) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (h0 | h1)
    · simp [h0]
    · simp [h1]

theorem apolloniusOnsagerOperator_symmetric
    (st : ApolloniusState) (v w : Fin 2 → ℝ) :
    apolloniusKreinPairing v (apolloniusOnsagerOperator st w) =
      apolloniusKreinPairing (apolloniusOnsagerOperator st v) w := by
  unfold apolloniusKreinPairing
  rw [apolloniusOnsagerOperator_apply, apolloniusOnsagerOperator_apply,
    apolloniusOnsagerOperator_apply, apolloniusOnsagerOperator_apply]
  simp only [hessian_indefinite_formCoord]
  simp
  ring

theorem apolloniusDissipativeStep_kreinPairing
    (st : ApolloniusState) (τ : ℝ) (v : Fin 2 → ℝ) :
    apolloniusKreinPairing (apolloniusDissipativeStep st τ v)
      (apolloniusDissipativeStep st τ v) =
      (1 - τ / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) ^ 2 *
        apolloniusKreinPairing v v := by
  unfold apolloniusKreinPairing
  rw [apolloniusDissipativeStep_apply, apolloniusDissipativeStep_apply]
  simp only [hessian_indefinite_formCoord]
  simp
  ring

theorem apolloniusKreinPairing_symmetric
    (v w : Fin 2 → ℝ) :
    apolloniusKreinPairing v w = apolloniusKreinPairing w v := by
  unfold apolloniusKreinPairing hessian_indefinite_formCoord
  simp
  ring

theorem apolloniusDissipativeStep_kreinPairing_bilinear
    (st : ApolloniusState) (τ : ℝ) (v w : Fin 2 → ℝ) :
    apolloniusKreinPairing (apolloniusDissipativeStep st τ v)
      (apolloniusDissipativeStep st τ w) =
      (1 - τ / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) ^ 2 *
        apolloniusKreinPairing v w := by
  unfold apolloniusKreinPairing
  rw [apolloniusDissipativeStep_apply, apolloniusDissipativeStep_apply,
    apolloniusDissipativeStep_apply, apolloniusDissipativeStep_apply]
  simp only [hessian_indefinite_formCoord]
  simp
  ring

theorem apolloniusDissipativeStep_preserves_krein_null_iff
    (st : ApolloniusState) {τ : ℝ} (hτ :
      τ ≠ (st.sigma - 1 / 2) ^ 2 + st.t ^ 2) (v : Fin 2 → ℝ) :
    apolloniusKreinPairing (apolloniusDissipativeStep st τ v)
      (apolloniusDissipativeStep st τ v) = 0 ↔
      apolloniusKreinPairing v v = 0 := by
  rw [apolloniusDissipativeStep_kreinPairing]
  have hden : (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 ≠ 0 :=
    ne_of_gt st.h_non_sing
  have hscale :
      (1 - τ / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    intro hzero
    apply hτ
    have hzero' :
        1 - τ / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) = 0 := by
      convert hzero using 1 <;> field_simp [hden] <;> ring
    have hratio :
        τ / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) = 1 := by
      linarith [hzero']
    exact (div_eq_one_iff_eq hden).mp hratio
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hs | hv
    · exact False.elim (hscale hs)
    · exact hv
  · intro hv
    rw [hv]
    simp

theorem apolloniusOnsagerOperator_quadratic_nonnegative
    (st : ApolloniusState) (v : Fin 2 → ℝ) :
    0 ≤ ∑ i, v i * (apolloniusOnsagerOperator st v) i := by
  have hden : 0 < (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 := st.h_non_sing
  rw [Fin.sum_univ_two]
  simp only [apolloniusOnsagerOperator_apply]
  have hinv : 0 < 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) :=
    one_div_pos.mpr hden
  calc
    v 0 * (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) * v 0) +
        v 1 * (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) * v 1) =
      (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) *
        ((v 0) ^ 2 + (v 1) ^ 2) := by ring
    _ ≥ 0 := mul_nonneg (le_of_lt hinv) (by positivity)

theorem apolloniusOnsagerOperator_eq_zero_iff
    (st : ApolloniusState) (v : Fin 2 → ℝ) :
    apolloniusOnsagerOperator st v = 0 ↔ v = 0 := by
  have hden : (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 ≠ 0 :=
    ne_of_gt st.h_non_sing
  constructor
  · intro hv
    funext i
    have hi := congrFun hv i
    rw [apolloniusOnsagerOperator_apply] at hi
    exact (mul_eq_zero.mp (by simpa using hi)).resolve_left (one_div_ne_zero hden)
  · intro hv
    simp [hv]

/-- The Fisher operator as native Onsager metric data. -/
def apolloniusOnsagerMetricData (st : ApolloniusState) :
    InfoGeometry.SuperMetriplectic.OnsagerMetricData (Fin 2 → ℝ) where
  onsager := apolloniusOnsagerOperator st
  pairing := fun v w => ∑ i, v i * w i
  metric_symmetric := by
    intro v w
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [apolloniusOnsagerOperator_apply]
    ring
  metric_nonnegative := by
    intro v
    exact apolloniusOnsagerOperator_quadratic_nonnegative st v
  pairing_zero_right := by
    intro v
    simp

theorem apolloniusOnsagerMetricData_quadratic
    (st : ApolloniusState) (v : Fin 2 → ℝ) :
    (apolloniusOnsagerMetricData st).quadratic v =
      ∑ i, v i * (apolloniusOnsagerOperator st v) i := by
  rfl

theorem apolloniusOnsagerMetricData_quadratic_nonnegative
    (st : ApolloniusState) (v : Fin 2 → ℝ) :
    0 ≤ (apolloniusOnsagerMetricData st).quadratic v := by
  exact (apolloniusOnsagerMetricData st).metric_nonnegative v

theorem apolloniusOnsagerMetricData_quadratic_pos_of_ne_zero
    (st : ApolloniusState) {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    0 < (apolloniusOnsagerMetricData st).quadratic v := by
  rw [apolloniusOnsagerMetricData_quadratic]
  have hreadout :
      (∑ i, v i * (apolloniusOnsagerOperator st v) i) =
        apolloniusFisherQuadraticForm st v := by
    rw [Fin.sum_univ_two]
    simp only [apolloniusOnsagerOperator_apply,
      apolloniusFisherQuadraticForm, apolloniusFisherMatrix]
    change _ =
      v 0 * (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) * v 0) +
        v 1 * (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) * v 1)
    ring
  rw [hreadout]
  exact apollonius_fisher_pos_def st v hv

theorem apolloniusOnsager_reciprocity
    (st : ApolloniusState) (v w : Fin 2 → ℝ) :
    ∑ i, v i * (apolloniusOnsagerOperator st w) i =
      ∑ i, w i * (apolloniusOnsagerOperator st v) i := by
  exact (apolloniusOnsagerMetricData st).metric_symmetric v w

/-- The canonical purely dissipative Apollonius flow.  The energy force is
zero because the Fisher operator is strictly positive on this nonsingular
two-dimensional tangent space, so energy degeneracy is not silently assumed. -/
def apolloniusMetriplecticFlow (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    InfoGeometry.SuperMetriplectic.MetriplecticFlow (Fin 2 → ℝ) where
  metric := apolloniusOnsagerMetricData st
  entropyForce := entropyForce
  energyForce := 0
  reversibleFlow := 0
  dissipativeFlow := apolloniusOnsagerOperator st entropyForce
  totalFlow := apolloniusOnsagerOperator st entropyForce
  entropyProduction := (apolloniusOnsagerMetricData st).quadratic entropyForce
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := by simp
  energy_degeneracy := by simp
  entropyProduction_eq_quadratic := by rfl

theorem apolloniusMetriplecticFlow_entropyProduction_nonnegative
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    0 ≤ (apolloniusMetriplecticFlow st entropyForce).entropyProduction := by
  exact (apolloniusMetriplecticFlow st entropyForce).entropyProduction_nonnegative

theorem apolloniusMetriplecticFlow_dissipativeFlow
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    (apolloniusMetriplecticFlow st entropyForce).dissipativeFlow =
      apolloniusOnsagerOperator st entropyForce := rfl

theorem apolloniusMetriplecticFlow_totalFlow_eq_dissipative
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    (apolloniusMetriplecticFlow st entropyForce).totalFlow =
  (apolloniusMetriplecticFlow st entropyForce).dissipativeFlow := by
  rfl

theorem apolloniusMetriplecticFlow_equilibrium_iff
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    (apolloniusMetriplecticFlow st entropyForce).dissipativeFlow = 0 ↔
      entropyForce = 0 := by
  change apolloniusOnsagerOperator st entropyForce = 0 ↔ entropyForce = 0
  exact apolloniusOnsagerOperator_eq_zero_iff st entropyForce

theorem apolloniusMetriplecticFlow_entropyProduction_eq_fisher
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    (apolloniusMetriplecticFlow st entropyForce).entropyProduction =
      apolloniusFisherQuadraticForm st entropyForce := by
  change (apolloniusOnsagerMetricData st).quadratic entropyForce = _
  rw [apolloniusOnsagerMetricData_quadratic]
  have hreadout :
      (∑ i, entropyForce i *
          (apolloniusOnsagerOperator st entropyForce) i) =
        apolloniusFisherQuadraticForm st entropyForce := by
    rw [Fin.sum_univ_two]
    simp only [apolloniusOnsagerOperator_apply,
      apolloniusFisherQuadraticForm, apolloniusFisherMatrix]
    change _ =
      entropyForce 0 *
          (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) * entropyForce 0) +
        entropyForce 1 *
          (1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) * entropyForce 1)
    ring
  exact hreadout

theorem apolloniusMetriplecticFlow_entropyProduction_eq_zero_iff
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    (apolloniusMetriplecticFlow st entropyForce).entropyProduction = 0 ↔
      entropyForce = 0 := by
  constructor
  · intro hzero
    by_contra hforce
    have hpos' :
        0 < (apolloniusMetriplecticFlow st entropyForce).entropyProduction := by
      rw [apolloniusMetriplecticFlow_entropyProduction_eq_fisher]
      exact apollonius_fisher_pos_def st entropyForce hforce
    linarith
  · intro hforce
    subst entropyForce
    rw [apolloniusMetriplecticFlow_entropyProduction_eq_fisher]
    simp [apolloniusFisherQuadraticForm]

theorem apolloniusMetriplecticFlow_entropyProduction_pos_iff
    (st : ApolloniusState) (entropyForce : Fin 2 → ℝ) :
    0 < (apolloniusMetriplecticFlow st entropyForce).entropyProduction ↔
      entropyForce ≠ 0 := by
  constructor
  · intro hpos hzero
    subst entropyForce
    have hzero' :
        (apolloniusMetriplecticFlow st 0).entropyProduction = 0 :=
      (apolloniusMetriplecticFlow_entropyProduction_eq_zero_iff st 0).mpr rfl
    rw [hzero'] at hpos
    linarith
  · intro hforce
    rw [apolloniusMetriplecticFlow_entropyProduction_eq_fisher]
    exact apollonius_fisher_pos_def st entropyForce hforce

end
end InfoGeometry.Canonical.ApolloniusMetriplecticOperator
