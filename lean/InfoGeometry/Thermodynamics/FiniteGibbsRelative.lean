import InfoGeometry.Algebraic.CartanExponentialFamily
import InfoGeometry.Probability.FiniteGibbsVariational
import InfoGeometry.Analytic.LogSumExp

/-!
# Finite Gibbs relative thermodynamics

This file is the Lean-safe finite shadow of the Souriau/Tomita/non-equilibrium
dictionary.  It uses only the finite diagonal Cartan exponential family:

* `massieuPotential θ = log (∑ᵢ exp θᵢ)`;
* `relativeEntropy θ η = KL(p_θ || p_η)`;
* `relativeEntropy θ η = bregmanPhi θ η`;
* `fisherMetric θ X Y = Cov_θ(X,Y)`.

The determinant-volume cocycle is not used as a partition function here.  Its
finite Cartan logarithm is the affine readout `weylLogVolume`, whose mixed
second finite difference is already proved to vanish in
`CartanExponentialFamily`.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.FiniteGibbsRelative

open scoped BigOperators
open InfoGeometry.Algebraic.CartanExponentialFamily

variable {ι : Type*} [Fintype ι]

/-- Finite Cartan geometric temperature/modular generator coordinates. -/
abbrev FiniteTemperature (ι : Type*) := ι → ℝ

/-- Finite Massieu potential: the statistical log-partition `log ∑ᵢ exp θᵢ`. -/
noncomputable def massieuPotential (θ : FiniteTemperature ι) : ℝ :=
  massieu θ

/-- Finite Weyl/log-volume readout: the determinant-cocycle logarithm. -/
noncomputable def volumeCocycleLog (θ : FiniteTemperature ι) : ℝ :=
  weylLogVolume θ

/-- Relative modular/geometric driving vector in the finite Cartan chart. -/
def relativeHamiltonian (φ ψ : FiniteTemperature ι) : FiniteTemperature ι :=
  fun i => ψ i - φ i

/-- Finite relative entropy between two Gibbs states in the Cartan chart. -/
noncomputable def relativeEntropy (θ η : FiniteTemperature ι) : ℝ :=
  kl θ η

/-- Massieu-Bregman divergence with orientation `KL(p_θ || p_η)`. -/
noncomputable def massieuBregman (θ η : FiniteTemperature ι) : ℝ :=
  bregmanPhi θ η

/-- Finite Fisher/Souriau metric: the Cartan covariance form. -/
noncomputable def fisherMetric
    (θ : FiniteTemperature ι) (X Y : ι → ℝ) : ℝ :=
  fisherCov θ X Y

/-- Pointwise log-density difference for two finite Cartan Gibbs states. -/
theorem logDensity_sub_logDensity
    (θ η : FiniteTemperature ι) (i : ι) :
    InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i -
        InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i =
      (θ i - η i) + (massieuPotential η - massieuPotential θ) := by
  unfold InfoGeometry.Algebraic.CartanExponentialFamily.logDensity massieuPotential
  ring

/-!
The pointwise relative surprisal is the log-density difference with the
orientation used by `kl θ η`.  This is an algebraic identity in the finite
Cartan model; no measure-theoretic Radon--Nikodym construction is needed.
-/
theorem surprisal_difference_eq_logDensity_sub_logDensity
    (θ η : FiniteTemperature ι) (i : ι) :
    InfoGeometry.Algebraic.CartanExponentialFamily.surprisal η i -
        InfoGeometry.Algebraic.CartanExponentialFamily.surprisal θ i =
      InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i -
        InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i := by
  rw [InfoGeometry.Algebraic.CartanExponentialFamily.surprisal_eq_neg_logDensity,
    InfoGeometry.Algebraic.CartanExponentialFamily.surprisal_eq_neg_logDensity]
  ring

/-!
Expectation-level deviance readout: finite relative entropy is the expected
difference of surprisals under the first Cartan state.
-/
theorem relativeEntropy_eq_expect_surprisal_difference
    (θ η : FiniteTemperature ι) :
    relativeEntropy θ η =
      InfoGeometry.Algebraic.CartanExponentialFamily.expect θ (fun i =>
        InfoGeometry.Algebraic.CartanExponentialFamily.surprisal η i -
          InfoGeometry.Algebraic.CartanExponentialFamily.surprisal θ i) := by
  unfold relativeEntropy InfoGeometry.Algebraic.CartanExponentialFamily.kl
    InfoGeometry.Algebraic.CartanExponentialFamily.expect
  apply Finset.sum_congr rfl
  intro i hi
  change InfoGeometry.Algebraic.CartanExponentialFamily.prob θ i *
      (InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i -
        InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i) =
    InfoGeometry.Algebraic.CartanExponentialFamily.prob θ i *
      (InfoGeometry.Algebraic.CartanExponentialFamily.surprisal η i -
        InfoGeometry.Algebraic.CartanExponentialFamily.surprisal θ i)
  rw [surprisal_difference_eq_logDensity_sub_logDensity θ η i]

/-!
The Cartan `kl` owner and the normalized finite-KL owner use the same
probability law, but expose it through different coordinates.  This bridge
allows the existing Gibbs inequality and equality-case theorems to be reused
without duplicating their proofs here.
-/
theorem relativeEntropy_eq_normalizedFiniteRelativeEntropy
    [Nonempty ι] (θ η : FiniteTemperature ι)
    (hθ : 0 < Z θ) (hη : 0 < Z η) :
    relativeEntropy θ η =
      InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy
        (InfoGeometry.Algebraic.CartanExponentialFamily.prob θ)
        (InfoGeometry.Algebraic.CartanExponentialFamily.prob η) := by
  unfold relativeEntropy InfoGeometry.Algebraic.CartanExponentialFamily.kl
    InfoGeometry.Algebraic.CartanExponentialFamily.expect
  apply Finset.sum_congr rfl
  intro i hi
  have hθi : 0 < InfoGeometry.Algebraic.CartanExponentialFamily.prob θ i :=
    InfoGeometry.Algebraic.CartanExponentialFamily.prob_pos θ hθ i
  have hηi : 0 < InfoGeometry.Algebraic.CartanExponentialFamily.prob η i :=
    InfoGeometry.Algebraic.CartanExponentialFamily.prob_pos η hη i
  have hlogθ :
      Real.log (InfoGeometry.Algebraic.CartanExponentialFamily.prob θ i) =
      InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i := by
    unfold InfoGeometry.Algebraic.CartanExponentialFamily.prob
      InfoGeometry.Algebraic.CartanExponentialFamily.logDensity
    rw [Real.log_div (Real.exp_ne_zero _) hθ.ne', Real.log_exp]
    rfl
  have hlogη :
      Real.log (InfoGeometry.Algebraic.CartanExponentialFamily.prob η i) =
      InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i := by
    unfold InfoGeometry.Algebraic.CartanExponentialFamily.prob
      InfoGeometry.Algebraic.CartanExponentialFamily.logDensity
    rw [Real.log_div (Real.exp_ne_zero _) hη.ne', Real.log_exp]
    rfl
  rw [Real.log_div hθi.ne' hηi.ne', hlogθ, hlogη]

/-- Nonnegativity transported from the normalized finite-KL owner. -/
theorem relativeEntropy_nonneg
    [Nonempty ι] (θ η : FiniteTemperature ι)
    (hθ : 0 < Z θ) (hη : 0 < Z η) :
    0 ≤ relativeEntropy θ η := by
  rw [relativeEntropy_eq_normalizedFiniteRelativeEntropy θ η hθ hη]
  exact InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy_nonneg
    (prob θ) (prob η)
    (fun i => prob_pos θ hθ i)
    (fun i => prob_pos η hη i)
    (prob_sum_one θ hθ)
    (prob_sum_one η hη)

/-- Equality in Cartan relative entropy is equality of normalized Gibbs laws.
The common additive Cartan shift is intentionally not quotiented here. -/
theorem relativeEntropy_eq_zero_iff_prob_eq
    [Nonempty ι] (θ η : FiniteTemperature ι)
    (hθ : 0 < Z θ) (hη : 0 < Z η) :
    relativeEntropy θ η = 0 ↔ prob θ = prob η := by
  rw [relativeEntropy_eq_normalizedFiniteRelativeEntropy θ η hθ hη]
  exact InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy_eq_zero_iff
    (prob θ) (prob η)
    (fun i => prob_pos θ hθ i)
    (fun i => prob_pos η hη i)
    (prob_sum_one θ hθ)
    (prob_sum_one η hη)

/-!
The additive Cartan gauge is invisible to the normalized Gibbs law.  This is
the concrete finite consequence of the preceding equality characterization;
it does not quotient the parameter space or identify it with the determinant
readout.
-/
theorem relativeEntropy_zero_of_common_shift
    [Nonempty ι] (θ : FiniteTemperature ι) (c : ℝ) (hθ : 0 < Z θ) :
    relativeEntropy θ (fun i => θ i + c) = 0 := by
  apply (relativeEntropy_eq_zero_iff_prob_eq θ (fun i => θ i + c) hθ
    (Z_pos (fun i => θ i + c))).2
  funext i
  exact (prob_add_const θ c i).symm

/--
Zero finite relative entropy characterizes precisely the additive Cartan
gauge orbit.  This is the finite identifiability statement for the
normalized Gibbs chart: equal probabilities determine the natural parameters
up to one common scalar shift.
-/
theorem relativeEntropy_eq_zero_iff_common_shift
    [Nonempty ι] (θ η : FiniteTemperature ι)
    (hθ : 0 < Z θ) (hη : 0 < Z η) :
    relativeEntropy θ η = 0 ↔
      ∃ c : ℝ, ∀ i, η i = θ i + c := by
  constructor
  · intro hzero
    have hprob : prob θ = prob η :=
      (relativeEntropy_eq_zero_iff_prob_eq θ η hθ hη).1 hzero
    let c : ℝ := Phi η - Phi θ
    refine ⟨c, ?_⟩
    intro i
    have hlogθ :
        Real.log (prob θ i) =
          InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i := by
      unfold prob InfoGeometry.Algebraic.CartanExponentialFamily.logDensity
      rw [Real.log_div (Real.exp_ne_zero _) hθ.ne', Real.log_exp]
      rfl
    have hlogη :
        Real.log (prob η i) =
          InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i := by
      unfold prob InfoGeometry.Algebraic.CartanExponentialFamily.logDensity
      rw [Real.log_div (Real.exp_ne_zero _) hη.ne', Real.log_exp]
      rfl
    have hlogDensity :
        InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i =
          InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i := by
      calc
        InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i =
            Real.log (prob θ i) := hlogθ.symm
        _ = Real.log (prob η i) := by rw [congrFun hprob i]
        _ = InfoGeometry.Algebraic.CartanExponentialFamily.logDensity η i := hlogη
    unfold InfoGeometry.Algebraic.CartanExponentialFamily.logDensity at hlogDensity
    dsimp [c]
    linarith
  · rintro ⟨c, hc⟩
    have hηeq : η = (fun i => θ i + c) := by
      funext i
      exact hc i
    rw [hηeq]
    exact relativeEntropy_zero_of_common_shift θ c hθ

/--
Strict finite Gibbs dissipation away from the additive Cartan gauge orbit.
This is the exact finite Lyapunov criterion; no global convexity or analytic
continuation is involved.
-/
theorem relativeEntropy_pos_of_not_common_shift
    [Nonempty ι] (θ η : FiniteTemperature ι)
    (hθ : 0 < Z θ) (hη : 0 < Z η)
    (hnot : ¬ ∃ c : ℝ, ∀ i, η i = θ i + c) :
    0 < relativeEntropy θ η := by
  have hnonneg : 0 ≤ relativeEntropy θ η :=
    relativeEntropy_nonneg θ η hθ hη
  have hne : relativeEntropy θ η ≠ 0 := by
    intro hzero
    exact hnot ((relativeEntropy_eq_zero_iff_common_shift θ η hθ hη).1 hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/--
The finite relative modular readout is exactly the Massieu-Bregman divergence.

This is the finite, statistical statement.  It does not use
`det(exp A) = exp(trace A)`.
-/
theorem relativeEntropy_eq_massieuBregman
    [Nonempty ι] (θ η : FiniteTemperature ι) (hZ : 0 < Z θ) :
    relativeEntropy θ η = massieuBregman θ η := by
  exact kl_eq_bregmanPhi θ η hZ

/-- The finite Massieu-Bregman divergence vanishes on the diagonal. -/
theorem massieuBregman_self (θ : FiniteTemperature ι) :
    massieuBregman θ θ = 0 := by
  unfold massieuBregman bregmanPhi
  simp [Phi, expect]

/-- The finite relative entropy vanishes on the diagonal. -/
theorem relativeEntropy_self
    [Nonempty ι] (θ : FiniteTemperature ι) (hZ : 0 < Z θ) :
    relativeEntropy θ θ = 0 := by
  rw [relativeEntropy_eq_massieuBregman θ θ hZ, massieuBregman_self]

/-- The Fisher metric is the usual covariance formula. -/
theorem fisherMetric_eq_covariance
    [Nonempty ι] (θ : FiniteTemperature ι) (X Y : ι → ℝ) (hZ : 0 < Z θ) :
    fisherMetric θ X Y =
      expect θ (fun i => X i * Y i) - expect θ X * expect θ Y := by
  exact fisherCov_eq_expect_mul_sub_expect_mul θ X Y hZ

/-- Finite Fisher self-covariance is nonnegative. -/
theorem fisherMetric_self_nonneg
    [Nonempty ι] (θ : FiniteTemperature ι) (X : ι → ℝ) (hZ : 0 < Z θ) :
    0 ≤ fisherMetric θ X X := by
  exact fisherCov_self_nonneg θ X hZ

/-- The finite Fisher self-covariance is strictly positive for every
nonconstant observable.  This is the finite strictness criterion behind the
Souriau/Fisher metric; no infinite or analytic identification is used. -/
theorem fisherMetric_self_pos_of_nonconstant
    [Nonempty ι] (θ : FiniteTemperature ι) (X : ι → ℝ) (hZ : 0 < Z θ)
    (hX : ∃ i j : ι, X i ≠ X j) :
    0 < fisherMetric θ X X := by
  obtain ⟨i, j, hij⟩ := hX
  have hcenter : ∃ k : ι, X k - expect θ X ≠ 0 := by
    by_contra h
    push_neg at h
    apply hij
    linarith [h i, h j]
  obtain ⟨k, hk⟩ := hcenter
  change 0 < fisherCov θ X X
  unfold fisherCov
  apply Finset.sum_pos' (s := Finset.univ)
  · intro l hl
    have hprob : 0 ≤ prob θ l := prob_nonneg (θ := θ) hZ l
    simpa [pow_two, mul_assoc] using
      mul_nonneg hprob (sq_nonneg (X l - expect θ X))
  · refine ⟨k, Finset.mem_univ k, ?_⟩
    have hprob : 0 < prob θ k := prob_pos θ hZ k
    simpa [pow_two, mul_assoc] using
      mul_pos hprob (sq_pos_of_ne_zero hk)

/--
At the symmetric Cartan point, centered directions reduce the Fisher metric to
the averaged trace form.
-/
theorem fisherMetric_zero_eq_average_trace_form_of_centered
    [Nonempty ι] (X Y : ι → ℝ) (hX : centered X) (hY : centered Y) :
    fisherMetric (fun _ : ι => (0 : ℝ)) X Y =
      (1 / Fintype.card ι : ℝ) * ∑ i, X i * Y i := by
  exact fisherCov_zero_eq_average_trace_form_of_centered X Y hX hY

/--
The determinant/Weyl log-volume readout is affine; its mixed second finite
difference vanishes.  This is the formal firewall separating H¹ volume scaling
from Fisher geometry.
-/
theorem volumeCocycleLog_mixedSecondDifference_zero
    (θ X Y : FiniteTemperature ι) (s t : ℝ) :
    volumeCocycleLog (fun i => θ i + s * X i + t * Y i)
      - volumeCocycleLog (fun i => θ i + s * X i)
      - volumeCocycleLog (fun i => θ i + t * Y i)
      + volumeCocycleLog θ = 0 := by
  exact weylLogVolume_mixedSecondDifference_zero θ X Y s t

/--
Concrete two-point guardrail: at the symmetric Cartan point, the statistical
Massieu potential is `log 2`.
-/
theorem massieuPotential_zero_fin_two_eq_log_two :
    massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) = Real.log 2 := by
  unfold massieuPotential massieu Phi Z
  simp

/--
Concrete two-point guardrail: at the symmetric Cartan point, the determinant
log-volume readout is zero.
-/
theorem volumeCocycleLog_zero_fin_two_eq_zero :
    volumeCocycleLog (ι := Fin 2) (fun _ => (0 : ℝ)) = 0 := by
  unfold volumeCocycleLog weylLogVolume
  simp

/--
Concrete counterexample to identifying the Massieu partition potential with the
determinant/Weyl log-volume readout.

Even in the smallest nontrivial finite Cartan chart,
`log Tr(exp θ)` and `log det(exp θ)` disagree at `θ = 0`.
-/
theorem massieuPotential_zero_fin_two_ne_volumeCocycleLog_zero :
    massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) ≠
      volumeCocycleLog (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  rw [massieuPotential_zero_fin_two_eq_log_two]
  rw [volumeCocycleLog_zero_fin_two_eq_zero]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- The finite relative Hamiltonian is additive along state chains. -/
theorem relativeHamiltonian_chain
    {κ : Type*} (φ ψ χ : FiniteTemperature κ) :
    (fun i => relativeHamiltonian φ χ i) =
      fun i => relativeHamiltonian φ ψ i + relativeHamiltonian ψ χ i := by
  funext i
  unfold relativeHamiltonian
  ring

/--
Finite scalar relative cocycle shadow over commuting Cartan coordinates.

This is only the pointwise finite/abelian model of relative modular transport:
it is not the full Tomita-Takesaki/Connes cocycle for von Neumann algebras.
-/
noncomputable def finiteScalarRelativeCocycle
    {κ : Type*} (φ ψ : FiniteTemperature κ) (t : ℝ) (i : κ) : ℝ :=
  Real.exp (t * relativeHamiltonian φ ψ i)

/-- The finite scalar relative cocycle is normalized at time zero. -/
theorem finiteScalarRelativeCocycle_zero
    {κ : Type*} (φ ψ : FiniteTemperature κ) (i : κ) :
    finiteScalarRelativeCocycle φ ψ 0 i = 1 := by
  simp [finiteScalarRelativeCocycle]

/-- The finite scalar relative cocycle has the additive one-parameter law. -/
theorem finiteScalarRelativeCocycle_add
    {κ : Type*} (φ ψ : FiniteTemperature κ) (s t : ℝ) (i : κ) :
    finiteScalarRelativeCocycle φ ψ (s + t) i =
      finiteScalarRelativeCocycle φ ψ s i * finiteScalarRelativeCocycle φ ψ t i := by
  unfold finiteScalarRelativeCocycle
  have h :
      (s + t) * relativeHamiltonian φ ψ i =
        s * relativeHamiltonian φ ψ i + t * relativeHamiltonian φ ψ i := by
    ring
  rw [h, Real.exp_add]

/--
Finite scalar state-chain factorization.  In the finite Cartan lane the
relative generators commute pointwise, so the transition from `φ` to `χ`
factors through `ψ`.
-/
theorem finiteScalarRelativeCocycle_stateChain
    {κ : Type*} (φ ψ χ : FiniteTemperature κ) (t : ℝ) (i : κ) :
    finiteScalarRelativeCocycle φ χ t i =
      finiteScalarRelativeCocycle φ ψ t i * finiteScalarRelativeCocycle ψ χ t i := by
  unfold finiteScalarRelativeCocycle relativeHamiltonian
  have h :
      t * (χ i - φ i) = t * (ψ i - φ i) + t * (χ i - ψ i) := by
    ring
  rw [h, Real.exp_add]

/-!
The next theorem is the finite, fully analytic part of the convex-duality
dictionary: the directional derivative of the Massieu potential is the Gibbs
expectation.  The proof is reduced to the native finite log-sum-exp derivative
and therefore makes no measure-theoretic or infinite-dimensional claim.
-/

theorem hasDerivAt_massieu_direction
    [Nonempty ι] (θ X : FiniteTemperature ι) :
    HasDerivAt
      (fun t : ℝ => massieuPotential (fun i => θ i + t * X i))
      (expect θ X) 0 := by
  let w : ι → ℝ := fun i => Real.exp (θ i)
  have hcurve :
      (fun t : ℝ => massieuPotential (fun i => θ i + t * X i)) =
        (fun t : ℝ => InfoGeometry.Analytic.logSumExp w X t) := by
    funext t
    unfold massieuPotential massieu Phi Z
    unfold InfoGeometry.Analytic.logSumExp
      InfoGeometry.Analytic.logSumExpPartition
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.exp_add]
  rw [hcurve]
  have hpart := InfoGeometry.Analytic.hasDerivAt_logSumExpPartition w X 0
  have hpos : 0 < InfoGeometry.Analytic.logSumExpPartition w X 0 := by
    unfold InfoGeometry.Analytic.logSumExpPartition w
    apply Finset.sum_pos
    · intro i hi
      positivity
    · exact Finset.univ_nonempty
  have hlog := hpart.log hpos.ne'
  have htarget :
      InfoGeometry.Analytic.logSumExpMoment1 w X 0 /
          InfoGeometry.Analytic.logSumExpPartition w X 0 = expect θ X := by
    unfold InfoGeometry.Analytic.logSumExpMoment1
      InfoGeometry.Analytic.logSumExpPartition expect w
    simp only [zero_mul, Real.exp_zero, mul_one]
    unfold prob Z
    have hZ : Z θ ≠ 0 := (Z_pos θ).ne'
    have hsum_pos : 0 < ∑ x, Real.exp (θ x) := by
      exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
    apply (div_eq_iff (ne_of_gt hsum_pos)).2
    have hterm :
        (∑ i, (Real.exp (θ i) / ∑ j, Real.exp (θ j)) * X i) =
          (∑ i, Real.exp (θ i) * X i) / ∑ j, Real.exp (θ j) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hterm]
    field_simp [ne_of_gt hsum_pos]
  rw [htarget] at hlog
  exact hlog

/--
The second directional derivative is the Fisher covariance.  This is the
finite Hessian statement corresponding to the preceding mean-value theorem.
-/
theorem deriv2_massieu_direction
    [Nonempty ι] (θ X : FiniteTemperature ι) :
    deriv (fun t : ℝ =>
      deriv (fun s : ℝ => massieuPotential (fun i => θ i + s * X i)) t) 0 =
      fisherMetric θ X X := by
  let w : ι → ℝ := fun i => Real.exp (θ i)
  have hcurve :
      (fun t : ℝ => massieuPotential (fun i => θ i + t * X i)) =
        (fun t : ℝ => InfoGeometry.Analytic.logSumExp w X t) := by
    funext t
    unfold massieuPotential massieu Phi Z
    unfold InfoGeometry.Analytic.logSumExp
      InfoGeometry.Analytic.logSumExpPartition
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.exp_add]
  rw [hcurve]
  have hw : ∀ i, 0 < w i := fun i => Real.exp_pos _
  rw [InfoGeometry.Analytic.logSumExp_secondDeriv_eq_variance w X hw 0]
  rw [InfoGeometry.Analytic.logSumExpVariance_eq_centered w X hw 0]
  have hweight (i : ι) :
      InfoGeometry.Analytic.logSumExpWeight w X 0 i = prob θ i := by
    unfold InfoGeometry.Analytic.logSumExpWeight w
      InfoGeometry.Analytic.logSumExpPartition prob Z
    simp
  simp_rw [hweight]
  simp [fisherMetric, fisherCov, expect, pow_two]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end InfoGeometry.Thermodynamics.FiniteGibbsRelative
