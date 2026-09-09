import InfoGeometry.Algebraic.CartanExponentialFamily
import InfoGeometry.Probability.FiniteGibbsVariational

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

lemma log_prob_eq_logDensity [Nonempty ι] (θ : FiniteTemperature ι) (hZ : 0 < Z θ) (i : ι) :
    Real.log (prob θ i) = InfoGeometry.Algebraic.CartanExponentialFamily.logDensity θ i := by
  unfold prob InfoGeometry.Algebraic.CartanExponentialFamily.logDensity Phi
  rw [Real.log_div (ne_of_gt (Real.exp_pos (θ i))) (ne_of_gt hZ)]
  rw [Real.log_exp]

/-- The Cartan relative entropy matches the native finite Gibbs relative entropy of the normalized state. -/
theorem relativeEntropy_eq_normalizedFiniteRelativeEntropy
    [Nonempty ι] (θ η : FiniteTemperature ι) (hZθ : 0 < Z θ) (hZη : 0 < Z η) :
    relativeEntropy θ η =
      InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy (prob θ) (prob η) := by
  unfold relativeEntropy kl expect InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy
  apply Finset.sum_congr rfl
  intro i _hi
  have hpθ : 0 < prob θ i := prob_pos θ hZθ i
  have hpη : 0 < prob η i := prob_pos η hZη i
  rw [Real.log_div (ne_of_gt hpθ) (ne_of_gt hpη)]
  rw [log_prob_eq_logDensity θ hZθ i]
  rw [log_prob_eq_logDensity η hZη i]

/-- Nonnegativity of the finite Cartan relative entropy. -/
theorem relativeEntropy_nonneg
    [Nonempty ι] (θ η : FiniteTemperature ι) (hZθ : 0 < Z θ) (hZη : 0 < Z η) :
    0 ≤ relativeEntropy θ η := by
  rw [relativeEntropy_eq_normalizedFiniteRelativeEntropy θ η hZθ hZη]
  exact InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy_nonneg (prob θ) (prob η)
    (fun i => prob_pos θ hZθ i)
    (fun i => prob_pos η hZη i)
    (prob_sum_one θ hZθ)
    (prob_sum_one η hZη)

/-- Equality of finite Gibbs states is precisely a common shift along the central Cartan gauge direction. -/
theorem relativeEntropy_eq_zero_iff_common_shift
    [Nonempty ι] (θ η : FiniteTemperature ι) (hZθ : 0 < Z θ) (hZη : 0 < Z η) :
    relativeEntropy θ η = 0 ↔ ∃ c : ℝ, ∀ i : ι, η i = θ i + c := by
  rw [relativeEntropy_eq_normalizedFiniteRelativeEntropy θ η hZθ hZη]
  have hpos_θ : ∀ i, 0 < prob θ i := fun i => prob_pos θ hZθ i
  have hpos_η : ∀ i, 0 < prob η i := fun i => prob_pos η hZη i
  have hsum_θ : ∑ i, prob θ i = 1 := prob_sum_one θ hZθ
  have hsum_η : ∑ i, prob η i = 1 := prob_sum_one η hZη
  rw [InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy_eq_zero_iff
    (prob θ) (prob η) hpos_θ hpos_η hsum_θ hsum_η]
  constructor
  · intro hprob
    use Phi η - Phi θ
    intro i
    have hpi : prob θ i = prob η i := congrFun hprob i
    have hlog := congrArg Real.log hpi
    rw [log_prob_eq_logDensity θ hZθ i, log_prob_eq_logDensity η hZη i] at hlog
    unfold InfoGeometry.Algebraic.CartanExponentialFamily.logDensity at hlog
    linarith
  · rintro ⟨c, hc⟩
    ext i
    unfold prob Z
    have h_exp : ∀ j : ι, Real.exp (η j) = Real.exp (θ j) * Real.exp c := by
      intro j
      rw [hc j, Real.exp_add]
    have h_sum : (∑ j, Real.exp (η j)) = (∑ j, Real.exp (θ j)) * Real.exp c := by
      simp_rw [h_exp]
      rw [← Finset.sum_mul]
    rw [h_exp i, h_sum]
    have hec : Real.exp c ≠ 0 := ne_of_gt (Real.exp_pos c)
    rw [mul_div_mul_right _ _ hec]

/-- Strict positivity of the finite Cartan relative entropy away from the central gauge shift. -/
theorem relativeEntropy_pos_of_not_common_shift
    [Nonempty ι] (θ η : FiniteTemperature ι) (hZθ : 0 < Z θ) (hZη : 0 < Z η)
    (hnot : ¬ ∃ c : ℝ, ∀ i : ι, η i = θ i + c) :
    0 < relativeEntropy θ η := by
  have hnonneg := relativeEntropy_nonneg θ η hZθ hZη
  have hne : relativeEntropy θ η ≠ 0 := by
    intro hz
    exact hnot ((relativeEntropy_eq_zero_iff_common_shift θ η hZθ hZη).mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

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

end InfoGeometry.Thermodynamics.FiniteGibbsRelative
