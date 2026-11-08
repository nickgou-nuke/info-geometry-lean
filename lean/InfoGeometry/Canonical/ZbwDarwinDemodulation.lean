import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZitterbewegungMassEmergenceBridge
import InfoGeometry.Lie.SplitOctonionCrossTensor

/-!
# Exact Zitterbewegung kinematics and low-energy coefficient audits

The Dirac rest-energy gap determines an angular frequency and a period. A
second-order Taylor average with isotropic covariance contracts the Hessian to
its trace. This file proves that finite algebraic contraction and checks which
variance is needed to match the Foldy–Wouthuysen Darwin coefficient.

The coefficient computation is not a derivation of the Darwin term from a
physical Zitterbewegung trajectory, nor a derivation of a Lamb shift. Likewise,
the scalar triple product below is audited under conventional vector and
time-reversal transformations; it is not a Clover-detector prediction.
-/

namespace ZbwDemodulation

open InfoGeometry.Canonical.ZitterbewegungMassEmergence

noncomputable section

/-! ## Isotropic covariance contracts a Hessian to its trace -/

/-- The isotropic covariance tensor in three dimensions with total variance
`variance`. -/
def isotropicCovariance3 (variance : ℝ) (i j : Fin 3) : ℝ :=
  if i = j then variance / 3 else 0

/-- The isotropic covariance is symmetric in its coordinate indices. -/
theorem isotropicCovariance3_comm (variance : ℝ) (i j : Fin 3) :
    isotropicCovariance3 variance i j = isotropicCovariance3 variance j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp [isotropicCovariance3, h, h']

/-- Summing the three diagonal entries recovers the total variance parameter.
This fixes the convention used by `isotropicCovariance3`: each coordinate has
variance `variance / 3`, while `variance` is the trace of the covariance. -/
theorem isotropicCovariance3_trace (variance : ℝ) :
    (∑ i : Fin 3, isotropicCovariance3 variance i i) = variance := by
  simp [isotropicCovariance3]
  ring

/-- The isotropic covariance tensor is positive semidefinite whenever its
total variance is nonnegative. The quadratic form is the sum of the three
coordinate squares, each weighted by `variance / 3`. -/
theorem isotropicCovariance3_quadratic_nonneg (variance : ℝ)
    (u : Fin 3 → ℝ) (hvariance : 0 ≤ variance) :
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      u i * isotropicCovariance3 variance i j * u j := by
  have hform :
      (∑ i : Fin 3, ∑ j : Fin 3,
        u i * isotropicCovariance3 variance i j * u j) =
        variance / 3 * ((u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2) := by
    simp [isotropicCovariance3, Fin.sum_univ_three]
    ring
  rw [hform]
  positivity

/-! ## A finite isotropic displacement ensemble -/

/-- The six signed coordinate-axis displacements of radius `radius`. This is
the uniform octahedral ensemble in three dimensions; it is a finite moment
model and does not assert a Dirac trajectory. -/
def sixAxisDisplacement3 (radius : ℝ) : Fin 6 → Fin 3 → ℝ :=
  ![![radius, 0, 0], ![-radius, 0, 0],
    ![0, radius, 0], ![0, -radius, 0],
    ![0, 0, radius], ![0, 0, -radius]]

/-- The involution pairing each signed-axis displacement with its opposite. -/
def sixAxisOpposite : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

/-- The state involution negates the associated displacement vector. -/
theorem sixAxisDisplacement3_opposite (radius : ℝ) (s : Fin 6) :
    sixAxisDisplacement3 radius (sixAxisOpposite s) =
      -sixAxisDisplacement3 radius s := by
  fin_cases s <;> funext i <;> fin_cases i <;>
    simp [sixAxisOpposite, sixAxisDisplacement3]

/-- Uniform average of an observable evaluated on the signed-axis states. -/
def sixAxisObservableAverage3 (radius : ℝ)
    (observable : (Fin 3 → ℝ) → ℝ) : ℝ :=
  (1 / 6 : ℝ) * ∑ s : Fin 6,
    observable (sixAxisDisplacement3 radius s)

/-- Every odd observable has zero average on the centrally symmetric
six-state ensemble. The result follows by reindexing with the exact
antipodal involution. -/
theorem sixAxisObservableAverage3_eq_zero_of_odd (radius : ℝ)
    (observable : (Fin 3 → ℝ) → ℝ)
    (hodd : ∀ x, observable (-x) = -observable x) :
    sixAxisObservableAverage3 radius observable = 0 := by
  have hsum :
      (∑ s : Fin 6, observable (sixAxisDisplacement3 radius s)) =
        -(∑ s : Fin 6, observable (sixAxisDisplacement3 radius s)) := by
    calc
      (∑ s : Fin 6, observable (sixAxisDisplacement3 radius s)) =
          ∑ s : Fin 6,
            observable (sixAxisDisplacement3 radius (sixAxisOpposite s)) :=
        (Equiv.sum_comp sixAxisOpposite _).symm
      _ = ∑ s : Fin 6,
            -observable (sixAxisDisplacement3 radius s) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [sixAxisDisplacement3_opposite, hodd]
      _ = -(∑ s : Fin 6, observable (sixAxisDisplacement3 radius s)) :=
        by rw [Finset.sum_neg_distrib]
  have hzero :
      (∑ s : Fin 6, observable (sixAxisDisplacement3 radius s)) = 0 := by
    linarith
  unfold sixAxisObservableAverage3
  rw [hzero]
  ring

/-- Mean displacement under the uniform distribution on the six axis states. -/
def sixAxisMean3 (radius : ℝ) (i : Fin 3) : ℝ :=
  (1 / 6 : ℝ) * ∑ s : Fin 6, sixAxisDisplacement3 radius s i

/-- Second-moment tensor of the uniform signed-axis distribution. Its mean is
zero, so this second moment is also its covariance. -/
def sixAxisCovariance3 (radius : ℝ) (i j : Fin 3) : ℝ :=
  (1 / 6 : ℝ) * ∑ s : Fin 6,
    sixAxisDisplacement3 radius s i * sixAxisDisplacement3 radius s j

/-- Opposite points in the signed-axis ensemble cancel, giving zero mean. -/
theorem sixAxisMean3_eq_zero (radius : ℝ) (i : Fin 3) :
    sixAxisMean3 radius i = 0 := by
  change sixAxisObservableAverage3 radius (fun x => x i) = 0
  exact sixAxisObservableAverage3_eq_zero_of_odd radius (fun x => x i)
    (by intro x; simp)

/-- Each point in the signed-axis ensemble lies on the sphere of the declared
radius, expressed as an exact sum of coordinate squares. -/
theorem sixAxisDisplacement3_norm_sq (radius : ℝ) (s : Fin 6) :
  (∑ i : Fin 3, (sixAxisDisplacement3 radius s i) ^ 2) = radius ^ 2 := by
  fin_cases s <;>
    simp [sixAxisDisplacement3, Fin.sum_univ_three]

/-- The uniform signed-axis ensemble has covariance `(radius² / 3) δᵢⱼ`,
so its total variance is `radius²`. -/
theorem sixAxisCovariance3_eq_isotropic (radius : ℝ) (i j : Fin 3) :
    sixAxisCovariance3 radius i j =
      isotropicCovariance3 (radius ^ 2) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [sixAxisCovariance3, sixAxisDisplacement3,
      isotropicCovariance3, Fin.sum_univ_six] <;> ring

/-- The trace of the finite ensemble covariance is its total variance. -/
theorem sixAxisCovariance3_trace (radius : ℝ) :
    (∑ i : Fin 3, sixAxisCovariance3 radius i i) = radius ^ 2 := by
  simp_rw [sixAxisCovariance3_eq_isotropic]
  exact isotropicCovariance3_trace (radius ^ 2)

/-- The covariance realized by the six signed-axis states is positive
semidefinite: every linear observable has nonnegative second moment. -/
theorem sixAxisCovariance3_quadratic_nonneg (radius : ℝ) (u : Fin 3 → ℝ) :
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      u i * sixAxisCovariance3 radius i j * u j := by
  have h := isotropicCovariance3_quadratic_nonneg (radius ^ 2) u (sq_nonneg radius)
  simpa only [sixAxisCovariance3_eq_isotropic] using h

/-- The Hessian contraction in the second-order Taylor term, including its
factor `1/2`. -/
def isotropicHessianCorrection (variance : ℝ) (hessian : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
    isotropicCovariance3 variance i j * hessian i j

/-- The trace of a three-dimensional Hessian, i.e. the coordinate Laplacian. -/
def hessianTrace3 (hessian : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, hessian i i

/-- Contracting an isotropic covariance `(variance/3) δᵢⱼ` with a Hessian
produces `(variance/6) tr(H)`, the exact quadratic Taylor correction. -/
theorem isotropicHessianCorrection_eq (variance : ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) :
    isotropicHessianCorrection variance hessian =
      variance / 6 * hessianTrace3 hessian := by
  have h_inner (i : Fin 3) :
      (∑ j : Fin 3, isotropicCovariance3 variance i j * hessian i j) =
        variance / 3 * hessian i i := by
    calc
      (∑ j : Fin 3, isotropicCovariance3 variance i j * hessian i j) =
          isotropicCovariance3 variance i i * hessian i i := by
            apply Finset.sum_eq_single i
            · intro j _ hji
              have hne : i ≠ j := Ne.symm hji
              simp [isotropicCovariance3, hne]
            · intro hi
              exact (hi (Finset.mem_univ i)).elim
      _ = variance / 3 * hessian i i := by simp [isotropicCovariance3]
  unfold isotropicHessianCorrection hessianTrace3
  simp_rw [h_inner]
  rw [← Finset.mul_sum]
  ring

/-- Finite second-order Taylor average, expressed directly from the first
moment and covariance of the displacement. -/
def taylorAverage3 (base : ℝ) (gradient firstMoment : Fin 3 → ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) (covariance : Fin 3 → Fin 3 → ℝ) : ℝ :=
  base + (∑ i : Fin 3, gradient i * firstMoment i) +
    (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
      covariance i j * hessian i j

/-- If the displacement has zero first moment and isotropic covariance
`(variance / 3) δᵢⱼ`, the finite second-order Taylor average is the base value
plus `(variance / 6)` times the Hessian trace. This is the exact algebraic
moment calculation underlying the smearing heuristic; it assumes those
moments and does not derive them from a Dirac trajectory. -/
theorem taylorAverage3_eq_isotropic (base : ℝ) (gradient firstMoment : Fin 3 → ℝ)
    (hessian covariance : Fin 3 → Fin 3 → ℝ) (variance : ℝ)
    (hfirst : ∀ i, firstMoment i = 0)
    (hcov : ∀ i j, covariance i j = isotropicCovariance3 variance i j) :
    taylorAverage3 base gradient firstMoment hessian covariance =
      base + variance / 6 * hessianTrace3 hessian := by
  have hlinear : ∑ i : Fin 3, gradient i * firstMoment i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hfirst i]
    simp
  have hquadratic :
      (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
        covariance i j * hessian i j =
      isotropicHessianCorrection variance hessian := by
    unfold isotropicHessianCorrection
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcov]
  rw [taylorAverage3, hlinear, hquadratic, isotropicHessianCorrection_eq]
  ring

/-- The finite signed-axis moment model gives the same second-order Taylor
correction as the isotropic contraction theorem, with total variance `radius²`.
This establishes realizability of the assumed moments, not their physical
origin in Zitterbewegung dynamics. -/
theorem taylorAverage3_sixAxis (base : ℝ) (gradient : Fin 3 → ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) (radius : ℝ) :
    taylorAverage3 base gradient (sixAxisMean3 radius) hessian
      (sixAxisCovariance3 radius) =
        base + radius ^ 2 / 6 * hessianTrace3 hessian := by
  apply taylorAverage3_eq_isotropic
  · exact sixAxisMean3_eq_zero radius
  · exact sixAxisCovariance3_eq_isotropic radius

/-- The second-order Taylor polynomial at a displacement from the base point.
The Hessian term is written with the ordered coordinate sum and factor `1/2`. -/
def taylorPolynomial3 (base : ℝ) (gradient : Fin 3 → ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) (displacement : Fin 3 → ℝ) : ℝ :=
  base + (∑ i : Fin 3, gradient i * displacement i) +
    (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
      displacement i * displacement j * hessian i j

/-- Uniform finite average of the Taylor polynomial over the six signed-axis
displacements. -/
def sixAxisTaylorAverage3 (base : ℝ) (gradient : Fin 3 → ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) (radius : ℝ) : ℝ :=
  (1 / 6 : ℝ) * ∑ s : Fin 6,
    taylorPolynomial3 base gradient hessian (sixAxisDisplacement3 radius s)

/-- Direct finite-sum evaluation: the six Taylor samples average to the base
value plus `radius² / 6` times the Hessian trace. This derives the correction
from the six explicit sample points rather than assuming moment identities. -/
theorem sixAxisTaylorAverage3_eq_laplacian
    (base : ℝ) (gradient : Fin 3 → ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) (radius : ℝ) :
    sixAxisTaylorAverage3 base gradient hessian radius =
      base + radius ^ 2 / 6 * hessianTrace3 hessian := by
  simp [sixAxisTaylorAverage3, taylorPolynomial3, sixAxisDisplacement3,
    hessianTrace3, Fin.sum_univ_six, Fin.sum_univ_three]
  ring

/-- The isotropic Hessian correction is linear in the total covariance
variance. This separates the kinematic covariance input from the Hessian. -/
theorem isotropicHessianCorrection_smul_variance (variance scale : ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) :
    isotropicHessianCorrection (scale * variance) hessian =
      scale * isotropicHessianCorrection variance hessian := by
  rw [isotropicHessianCorrection_eq, isotropicHessianCorrection_eq]
  ring

/-- Changing a Hessian without changing its trace does not change its
isotropic second-order correction. The contraction depends only on the
Laplacian, not on off-diagonal entries or the trace-free part. -/
theorem isotropicHessianCorrection_eq_of_trace_eq (variance : ℝ)
    (h₁ h₂ : Fin 3 → Fin 3 → ℝ)
    (htrace : hessianTrace3 h₁ = hessianTrace3 h₂) :
    isotropicHessianCorrection variance h₁ =
      isotropicHessianCorrection variance h₂ := by
  rw [isotropicHessianCorrection_eq, isotropicHessianCorrection_eq, htrace]

/-- A nonnegative total variance and nonnegative Hessian trace give a
nonnegative isotropic quadratic correction. -/
theorem isotropicHessianCorrection_nonneg (variance : ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ)
    (hvariance : 0 ≤ variance) (htrace : 0 ≤ hessianTrace3 hessian) :
    0 ≤ isotropicHessianCorrection variance hessian := by
  rw [isotropicHessianCorrection_eq]
  positivity

/-- A zero Hessian has zero isotropic second-order correction, for every
variance. -/
theorem isotropicHessianCorrection_zero_hessian (variance : ℝ) :
    isotropicHessianCorrection variance (fun _ _ => 0) = 0 := by
  rw [isotropicHessianCorrection_eq]
  simp [hessianTrace3]

/-! ## Darwin coefficient comparison -/

/-- The Compton-radius scale `a = ℏ/(2mc)` used in the narrative. -/
def diracZitterRadius (m c hbar : ℝ) : ℝ :=
  hbar / (2 * m * c)

/-- Foldy–Wouthuysen Darwin coefficient multiplying the Laplacian of the
potential energy. -/
def darwinLaplacianCoefficient (m c hbar : ℝ) : ℝ :=
  hbar ^ 2 / (8 * m ^ 2 * c ^ 2)

/-- The Foldy–Wouthuysen Darwin coefficient is one half of the squared
Dirac Zitterbewegung radius. This identity isolates the numerical scale
comparison independently of any averaging model. -/
theorem darwinLaplacianCoefficient_eq_half_radius_sq
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    darwinLaplacianCoefficient m c hbar =
      diracZitterRadius m c hbar ^ 2 / 2 := by
  unfold darwinLaplacianCoefficient diracZitterRadius
  field_simp [hm, hc]
  ring

/-- For positive mass, light speed, and reduced Planck constant, the squared
radius and Darwin coefficient are strictly positive. -/
theorem diracZitterRadius_sq_pos (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    0 < diracZitterRadius m c hbar ^ 2 := by
  unfold diracZitterRadius
  positivity

theorem darwinLaplacianCoefficient_pos (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    0 < darwinLaplacianCoefficient m c hbar := by
  unfold darwinLaplacianCoefficient
  positivity

/-- Coefficient from the isotropic Taylor average when the variance is `a²`. -/
def radiusTaylorCoefficient (m c hbar : ℝ) : ℝ :=
  diracZitterRadius m c hbar ^ 2 / 6

/-- The quoted radius variance `a²` yields one third of the Darwin coefficient.
This records the factor mismatch in that version of the heuristic. -/
theorem radiusTaylorCoefficient_eq_third_darwin
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    radiusTaylorCoefficient m c hbar = darwinLaplacianCoefficient m c hbar / 3 := by
  unfold radiusTaylorCoefficient diracZitterRadius darwinLaplacianCoefficient
  field_simp [hm, hc]
  ring

/-- Matching the Darwin coefficient in a `variance/6` Taylor term requires
variance `3a²`. -/
theorem variance_required_for_darwin_eq_three_radius_sq
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    6 * darwinLaplacianCoefficient m c hbar =
      3 * diracZitterRadius m c hbar ^ 2 := by
  unfold darwinLaplacianCoefficient diracZitterRadius
  field_simp [hm, hc]
  ring

/-- In particular, the variance `3a²` gives exactly the Darwin coefficient
under the isotropic second-order Taylor formula. -/
theorem three_radius_variance_gives_darwin
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    (3 * diracZitterRadius m c hbar ^ 2) / 6 =
      darwinLaplacianCoefficient m c hbar := by
  have h := variance_required_for_darwin_eq_three_radius_sq m c hbar hm hc
  linarith

/-- With the variance explicitly set to three times the squared radius, the
isotropic Taylor correction is the Foldy–Wouthuysen Darwin coefficient times
the Hessian trace. This is a conditional algebraic coefficient identity; it
does not assert that a physical trajectory has this covariance. -/
theorem isotropic_radius_variance_gives_darwin_correction
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (hessian : Fin 3 → Fin 3 → ℝ) :
    isotropicHessianCorrection (3 * diracZitterRadius m c hbar ^ 2) hessian =
      darwinLaplacianCoefficient m c hbar * hessianTrace3 hessian := by
  rw [isotropicHessianCorrection_eq]
  rw [three_radius_variance_gives_darwin m c hbar hm hc]

/-- If the coordinatewise variance is instead chosen as the squared radius,
the isotropic Taylor correction is one third of the Darwin correction. This
records the coefficient mismatch without assigning either variance to a
physical trajectory. -/
theorem isotropic_radius_sq_variance_gives_third_darwin_correction
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (hessian : Fin 3 → Fin 3 → ℝ) :
    isotropicHessianCorrection (diracZitterRadius m c hbar ^ 2) hessian =
      (darwinLaplacianCoefficient m c hbar / 3) * hessianTrace3 hessian := by
  rw [isotropicHessianCorrection_eq]
  have hcoef : diracZitterRadius m c hbar ^ 2 / 6 =
      darwinLaplacianCoefficient m c hbar / 3 := by
    simpa [radiusTaylorCoefficient] using
      radiusTaylorCoefficient_eq_third_darwin m c hbar hm hc
  exact congrArg (fun t : ℝ => t * hessianTrace3 hessian) hcoef

/-- The explicit six-point ensemble at radius `a` gives one third of the
Foldy–Wouthuysen Darwin correction. This ties the coefficient audit to a
concrete finite distribution with exactly the stated total variance. -/
theorem sixAxis_radius_variance_gives_third_darwin
    (base : ℝ) (gradient : Fin 3 → ℝ) (hessian : Fin 3 → Fin 3 → ℝ)
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    taylorAverage3 base gradient
        (sixAxisMean3 (diracZitterRadius m c hbar)) hessian
        (sixAxisCovariance3 (diracZitterRadius m c hbar)) =
      base + (darwinLaplacianCoefficient m c hbar / 3) *
        hessianTrace3 hessian := by
  rw [taylorAverage3_sixAxis]
  have hcoef : diracZitterRadius m c hbar ^ 2 / 6 =
      darwinLaplacianCoefficient m c hbar / 3 := by
    simpa [radiusTaylorCoefficient] using
      radiusTaylorCoefficient_eq_third_darwin m c hbar hm hc
  rw [hcoef]

/-- Scaling the six-point radius by `sqrt 3` gives total variance `3a²` and
therefore matches the Foldy–Wouthuysen coefficient in the second-order Taylor
average. This is an exact finite-moment realization of the required variance,
not a derivation of that variance from electron dynamics. -/
theorem sixAxis_sqrtThree_radius_gives_darwin
    (base : ℝ) (gradient : Fin 3 → ℝ) (hessian : Fin 3 → Fin 3 → ℝ)
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    taylorAverage3 base gradient
        (sixAxisMean3 (Real.sqrt 3 * diracZitterRadius m c hbar)) hessian
        (sixAxisCovariance3 (Real.sqrt 3 * diracZitterRadius m c hbar)) =
      base + darwinLaplacianCoefficient m c hbar * hessianTrace3 hessian := by
  rw [taylorAverage3_sixAxis]
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hcoef :
      (Real.sqrt 3 * diracZitterRadius m c hbar) ^ 2 / 6 =
        darwinLaplacianCoefficient m c hbar := by
    rw [mul_pow, hsqrt]
    calc
      3 * diracZitterRadius m c hbar ^ 2 / 6 =
          diracZitterRadius m c hbar ^ 2 / 2 := by ring
      _ = darwinLaplacianCoefficient m c hbar :=
        (darwinLaplacianCoefficient_eq_half_radius_sq m c hbar hm hc).symm
  rw [hcoef]

/-- A trace-free Hessian contributes no second-order correction under any
isotropic variance. This separates the vanishing caused by the potential from
the choice of trembling scale. -/
theorem isotropicHessianCorrection_zero_of_trace (variance : ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ) (htrace : hessianTrace3 hessian = 0) :
    isotropicHessianCorrection variance hessian = 0 := by
  rw [isotropicHessianCorrection_eq, htrace]
  ring

/-- When the Hessian trace is nonzero, the isotropic quadratic correction
vanishes exactly when the total variance is zero. This makes explicit that
the contraction cannot hide a nonzero variance behind a nonzero Laplacian. -/
theorem isotropicHessianCorrection_eq_zero_iff (variance : ℝ)
    (hessian : Fin 3 → Fin 3 → ℝ)
    (htrace : hessianTrace3 hessian ≠ 0) :
    isotropicHessianCorrection variance hessian = 0 ↔ variance = 0 := by
  rw [isotropicHessianCorrection_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hvariance | htraceZero
    · linarith
    · exact (htrace htraceZero).elim
  · intro hvariance
    simp [hvariance]

/-- For a Hessian with nonzero trace, matching the isotropic Taylor correction
to the Foldy–Wouthuysen Darwin coefficient is equivalent to choosing total
variance `3a²`. This is an algebraic coefficient criterion; it makes no claim
that a physical trajectory has that variance. -/
theorem isotropic_correction_eq_darwin_iff_variance
    (m c hbar variance : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (hessian : Fin 3 → Fin 3 → ℝ)
    (htrace : hessianTrace3 hessian ≠ 0) :
    isotropicHessianCorrection variance hessian =
        darwinLaplacianCoefficient m c hbar * hessianTrace3 hessian ↔
      variance = 3 * diracZitterRadius m c hbar ^ 2 := by
  rw [isotropicHessianCorrection_eq,
    darwinLaplacianCoefficient_eq_half_radius_sq m c hbar hm hc]
  constructor
  · intro h
    have hcoeff : variance / 6 =
        diracZitterRadius m c hbar ^ 2 / 2 :=
      mul_right_cancel₀ htrace h
    nlinarith
  · intro hvariance
    rw [hvariance]
    ring

/-! ## Frequency, period, and accumulated cycle count -/

/-- Period corresponding to the Dirac gap angular frequency. -/
def comptonZitterPeriod (m c hbar : ℝ) : ℝ :=
  2 * Real.pi / comptonFrequency m c hbar

/-- Angular frequency times its associated period is one full turn, whenever
the frequency is nonzero. -/
theorem comptonFrequency_mul_period (m c hbar : ℝ)
    (hfreq : comptonFrequency m c hbar ≠ 0) :
    comptonFrequency m c hbar * comptonZitterPeriod m c hbar = 2 * Real.pi := by
  unfold comptonZitterPeriod
  field_simp [hfreq]

/-- For positive physical parameters, the gap frequency period is
`π ℏ/(m c²)`. -/
theorem comptonZitterPeriod_eq (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    comptonZitterPeriod m c hbar = Real.pi * hbar / (m * c ^ 2) := by
  rw [comptonZitterPeriod, comptonFrequency_eq]
  have hmc : m * c ^ 2 ≠ 0 := mul_ne_zero hm.ne' (pow_ne_zero 2 hc.ne')
  field_simp

/-- For positive mass, light speed, and reduced Planck scale, the rest-gap
angular frequency is positive. -/
theorem comptonFrequency_pos (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    0 < comptonFrequency m c hbar := by
  rw [comptonFrequency_eq]
  positivity

/-- The period associated with the positive rest-gap frequency is positive. -/
theorem comptonZitterPeriod_pos (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    0 < comptonZitterPeriod m c hbar := by
  rw [comptonZitterPeriod_eq m c hbar hm hc hhbar]
  positivity

/-- In terms of the radius `a = ℏ/(2mc)`, the period associated to the
rest-energy gap is `2πa/c`. This is an algebraic relation among the defined
scales, not a claim about a measured trajectory. -/
theorem comptonZitterPeriod_eq_radius (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    comptonZitterPeriod m c hbar =
      2 * Real.pi * diracZitterRadius m c hbar / c := by
  rw [comptonZitterPeriod_eq m c hbar hm hc hhbar]
  unfold diracZitterRadius
  have hm0 : m ≠ 0 := hm.ne'
  have hc0 : c ≠ 0 := hc.ne'
  field_simp [hm0, hc0]

/-- The rest-gap angular frequency times the Dirac radius equals the speed
parameter `c`. This is the exact scale relation behind `period = 2πa/c`. -/
theorem comptonFrequency_mul_radius (m c hbar : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hhbar : hbar ≠ 0) :
    comptonFrequency m c hbar * diracZitterRadius m c hbar = c := by
  rw [comptonFrequency_eq]
  unfold diracZitterRadius
  field_simp [hm, hc, hhbar]

/-- Number of angular cycles accumulated during a duration. -/
def zitterCyclesDuring (duration m c hbar : ℝ) : ℝ :=
  duration / comptonZitterPeriod m c hbar

/-- Rational encodings of the lifetime and period quoted in the brainstorm.
They are kept separate from the Dirac-gap period defined above: this theorem
checks only the arithmetic of those two reported decimal values. -/
def quotedIntermediateLifetime : ℚ := (363 : ℚ) / 100 * (1 / (10 : ℚ) ^ 12)

def quotedZitterPeriod : ℚ := (64 : ℚ) / 100 * (1 / (10 : ℚ) ^ 21)

/-- The two quoted decimal values divide to exactly 5,671,875,000 cycles.
This arithmetic check does not identify the quoted period with the rest-gap
period `comptonZitterPeriod`. -/
theorem quotedCycleCount_exact :
    quotedIntermediateLifetime / quotedZitterPeriod = 5671875000 := by
  norm_num [quotedIntermediateLifetime, quotedZitterPeriod]

/-- The cycle count is `duration * angularFrequency / (2π)`. -/
theorem zitterCyclesDuring_eq (duration m c hbar : ℝ)
    (hfreq : comptonFrequency m c hbar ≠ 0) :
    zitterCyclesDuring duration m c hbar =
      duration * comptonFrequency m c hbar / (2 * Real.pi) := by
  rw [zitterCyclesDuring, comptonZitterPeriod]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp [hfreq, hpi]

/-- Rewriting the gap frequency using `ω_Z a = c` expresses the angular cycle
count directly in terms of the radius scale. This is a consequence of the
defined scales, not a statement that a particle follows a circular orbit. -/
theorem zitterCyclesDuring_eq_speed_radius (duration m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    zitterCyclesDuring duration m c hbar =
      duration * c /
        (2 * Real.pi * diracZitterRadius m c hbar) := by
  have hfreq : comptonFrequency m c hbar ≠ 0 :=
    (ne_of_gt (comptonFrequency_pos m c hbar hm hc hhbar))
  rw [zitterCyclesDuring_eq duration m c hbar hfreq]
  have hradius : diracZitterRadius m c hbar ≠ 0 := by
    unfold diracZitterRadius
    exact div_ne_zero hhbar.ne'
      (mul_ne_zero (mul_ne_zero (by norm_num) hm.ne') hc.ne')
  have hperiodDenom : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  calc
    duration * comptonFrequency m c hbar / (2 * Real.pi) =
        duration * (comptonFrequency m c hbar * diracZitterRadius m c hbar) /
          ((2 * Real.pi) * diracZitterRadius m c hbar) := by
            field_simp [hfreq, hperiodDenom, hradius]
    _ = duration * c / (2 * Real.pi * diracZitterRadius m c hbar) := by
      rw [comptonFrequency_mul_radius m c hbar hm.ne' hc.ne' hhbar.ne']

/-- A nonnegative duration accumulates a nonnegative number of cycles when
the physical parameters make the gap period positive. -/
theorem zitterCyclesDuring_nonneg (duration m c hbar : ℝ)
    (hduration : 0 ≤ duration) (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    0 ≤ zitterCyclesDuring duration m c hbar := by
  unfold zitterCyclesDuring
  exact div_nonneg hduration (le_of_lt (comptonZitterPeriod_pos m c hbar hm hc hhbar))

/-- Multiplying the cycle count by the positive period recovers the elapsed
duration exactly. This is the precise relation between the two defined
kinematic quantities. -/
theorem zitterCyclesDuring_mul_period (duration m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    zitterCyclesDuring duration m c hbar * comptonZitterPeriod m c hbar = duration := by
  unfold zitterCyclesDuring
  have hperiod : comptonZitterPeriod m c hbar ≠ 0 :=
    (comptonZitterPeriod_pos m c hbar hm hc hhbar).ne'
  field_simp

/-! ## Native scalar triple product and discrete symmetry audit

The orientation observable uses the repository's owner for the Zorn cross
product and its exterior-power realization.  This file proves only the
transformation statements needed for the ZBW audit; it defines no competing
cross product or scalar triple product.
-/

open InfoGeometry.Lie.SplitOctonionCrossTensor

/-- Simultaneously reversing two polar entries preserves the native scalar
triple product. With the first entry axial and the other two polar, this
oriented scalar is parity even. -/
theorem nativeScalarTriple_parity_even
    (S p eps : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple S (-p) (-eps) = nativeScalarTriple S p eps := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]

/-- Under time reversal, spin and momentum reverse while electric
polarization is even; this scalar triple product is T-even. -/
theorem nativeScalarTriple_timeReversal_even
    (S p eps : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple (-S) (-p) eps = nativeScalarTriple S p eps := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]

/-- Reversing exactly one polar entry changes the sign of the oriented
triple product. -/
theorem nativeScalarTriple_odd_in_momentum
    (S p eps : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple S (-p) eps = -nativeScalarTriple S p eps := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]
  ring

/-- An orientation-preserving linear change of frame leaves the native
scalar triple observable unchanged. This is the exact algebraic statement
available independently of a detector model. -/
theorem nativeScalarTriple_map_of_det_one
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det = 1)
    (S p eps : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple (A.mulVec S) (A.mulVec p) (A.mulVec eps) =
      nativeScalarTriple S p eps := by
  rw [nativeScalarTriple_map, hA, one_mul]

/-- An orientation-reversing linear change of frame reverses the sign of
the native scalar triple observable. The determinant, rather than an
unverified physical interpretation of a detector asymmetry, controls this
sign. -/
theorem nativeScalarTriple_map_of_det_neg_one
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det = -1)
    (S p eps : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple (A.mulVec S) (A.mulVec p) (A.mulVec eps) =
      -nativeScalarTriple S p eps := by
  rw [nativeScalarTriple_map, hA]
  simp

/-- Collinear momentum and polarization make the oriented volume vanish. -/
theorem nativeScalarTriple_zero_of_polarization_collinear
    (S p : InfoGeometry.Algebra.FiniteSpin.Vec3R) (scale : ℝ) :
    nativeScalarTriple S p (scale • p) = 0 := by
  rw [nativeScalarTriple_eq_det3]
  simp [det3]
  ring

/-- The chiral scalar triple product also vanishes when spin is parallel to
momentum, independently of the polarization vector. -/
theorem nativeScalarTriple_zero_of_spin_collinear
    (p eps : InfoGeometry.Algebra.FiniteSpin.Vec3R) (scale : ℝ) :
    nativeScalarTriple (scale • p) p eps = 0 := by
  rw [nativeScalarTriple_eq_det3]
  simp [InfoGeometry.Lie.SplitOctonionCrossTensor.det3]
  ring

end

/-! ## Exact arithmetic audit of the conflicting displayed decimal values -/

namespace DecimalAudit

/-- Exact rational encoding of the displayed `6.4 × 10⁻²² s` period. -/
def shortPeriodClaim : ℚ := 64 / 10 ^ 23

/-- Exact rational encoding of the other displayed `4.05 × 10⁻²¹ s` period. -/
def gapPeriodClaim : ℚ := 405 / 10 ^ 23

/-- Exact rational encoding of the central `3.63 × 10⁻¹² s` lifetime. -/
def sodiumLevelLifetime : ℚ := 363 / 10 ^ 14

/-- Lower and upper endpoints of the displayed `3.63 ± 0.09 ps` lifetime,
encoded exactly in seconds. -/
def sodiumLevelLifetimeLower : ℚ := 354 / 10 ^ 14
def sodiumLevelLifetimeUpper : ℚ := 372 / 10 ^ 14

/-- The two displayed period figures are unequal. -/
theorem displayed_period_claims_conflict : shortPeriodClaim ≠ gapPeriodClaim := by
  norm_num [shortPeriodClaim, gapPeriodClaim]

/-- The lifetime divided by the short displayed period is 5,671,875,000 cycles. -/
theorem cycle_count_using_short_period_claim :
    sodiumLevelLifetime / shortPeriodClaim = 5671875000 := by
  norm_num [sodiumLevelLifetime, shortPeriodClaim]

/-- Using the `4.05 × 10⁻²¹ s` period instead gives a central estimate between
896,296,296 and 896,296,297 cycles, before accounting for measurement error. -/
theorem cycle_count_using_gap_period_claim_bounds :
    (896296296 : ℚ) ≤ sodiumLevelLifetime / gapPeriodClaim ∧
      sodiumLevelLifetime / gapPeriodClaim < 896296297 := by
  norm_num [sodiumLevelLifetime, gapPeriodClaim]

/-- The stated lifetime uncertainty, divided by the internally consistent
`4.05 × 10⁻²¹ s` period claim, bounds the central cycle count between about
`8.74 × 10⁸` and `9.19 × 10⁸`. -/
theorem uncertain_cycle_count_using_gap_period_claim_bounds :
    (874074074 : ℚ) ≤ sodiumLevelLifetimeLower / gapPeriodClaim ∧
      sodiumLevelLifetimeUpper / gapPeriodClaim < 918518519 := by
  norm_num [sodiumLevelLifetimeLower, sodiumLevelLifetimeUpper, gapPeriodClaim]

end DecimalAudit

end ZbwDemodulation
