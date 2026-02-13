import InfoGeometry.Basic
import Mathlib

open scoped BigOperators

abbrev EmpiricalCounts (α : Type*) := α → ℕ

def totalMass {α : Type*} [Fintype α] (N_func : EmpiricalCounts α) : ℕ :=
  ∑ x, N_func x

noncomputable def empiricalDistribution
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α) (x : α) : ℝ :=
  (N_func x : ℝ) / (totalMass N_func : ℝ)

/-- Empirical data is nontrivial when total mass is nonzero. -/
def EmpiricalNontrivial {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α) : Prop :=
  totalMass N_func ≠ 0

lemma empirical_sum_one
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (h : EmpiricalNontrivial N_func) :
    ∑ x, empiricalDistribution N_func x = 1 := by
  classical
  unfold empiricalDistribution
  have hmass : (totalMass N_func : ℝ) ≠ 0 := by
    exact_mod_cast h
  calc
    ∑ x, (N_func x : ℝ) / (totalMass N_func : ℝ)
        = (∑ x, (N_func x : ℝ)) / (totalMass N_func : ℝ) := by
          rw [Finset.sum_div]
    _ = (totalMass N_func : ℝ) / (totalMass N_func : ℝ) := by
          simp [totalMass]
    _ = 1 := by
          exact div_self hmass

structure ProbabilityDist (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_one : ∑ x, prob x = 1

noncomputable def densityRatio
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (x : α) : ℝ :=
  empiricalDistribution N_func x / Q.prob x

noncomputable def surprisal
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (x : α) : ℝ :=
  -Real.log (densityRatio N_func Q x)

noncomputable def entropyExpectation
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α) : ℝ :=
  ∑ x, empiricalDistribution N_func x * surprisal N_func Q x

noncomputable def KLdivergence
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α) : ℝ :=
  -entropyExpectation N_func Q

/-- Definition: P̂ is absolutely continuous with respect to Q if P̂(x) ≠ 0 implies Q(x) ≠ 0. -/
def AbsolutelyContinuous
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α) : Prop :=
  ∀ x, empiricalDistribution N_func x ≠ 0 → Q.prob x ≠ 0

/-- Q has full support if all point masses are strictly positive. -/
def FullSupport
    {α : Type*} [Fintype α]
    (Q : ProbabilityDist α) : Prop :=
  ∀ x, 0 < Q.prob x

lemma absolutelyContinuous_of_fullSupport
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_support : FullSupport Q) :
    AbsolutelyContinuous N_func Q := by
  intro x hx
  exact ne_of_gt (h_support x)

lemma kl_pointwise_ge_sub
    {p q : ℝ}
    (hp_nonneg : 0 ≤ p)
    (hq_pos : 0 < q) :
    p * Real.log (p / q) ≥ p - q := by
  by_cases hp0 : p = 0
  · subst hp0
    nlinarith
  · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp0)
    have hlog : Real.log (q / p) ≤ q / p - 1 := by
      exact Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)
    have hmul : (-p) * (q / p - 1) ≤ (-p) * Real.log (q / p) := by
      exact mul_le_mul_of_nonpos_left hlog (by linarith [hp_nonneg])

    have hratio : p / q = (q / p)⁻¹ := by
      field_simp [hp0, (ne_of_gt hq_pos)]

    have hlog_inv : Real.log (p / q) = -Real.log (q / p) := by
      have hqp_ne : q / p ≠ 0 := div_ne_zero (ne_of_gt hq_pos) hp0
      calc
        Real.log (p / q) = Real.log ((q / p)⁻¹) := by rw [hratio]
        _ = -Real.log (q / p) := by simpa [hqp_ne] using Real.log_inv (q / p)

    have hleft : p * Real.log (p / q) = (-p) * Real.log (q / p) := by
      rw [hlog_inv]
      ring

    have hright : (-p) * (q / p - 1) = p - q := by
      field_simp [hp0, (ne_of_gt hq_pos)]
      ring

    have hfinal : p - q ≤ p * Real.log (p / q) := by
      calc
        p - q = (-p) * (q / p - 1) := by simp [hright]
        _ ≤ (-p) * Real.log (q / p) := hmul
        _ = p * Real.log (p / q) := by simp [hleft]

    exact hfinal

lemma kl_pointwise_gt_sub_of_ne
    {p q : ℝ}
    (hp_nonneg : 0 ≤ p)
    (hq_pos : 0 < q)
    (hpq : p ≠ q) :
    p - q < p * Real.log (p / q) := by
  by_cases hp0 : p = 0
  · subst hp0
    nlinarith
  · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp0)
    have hqp_ne_one : q / p ≠ 1 := by
      intro hqp_eq_one
      have hq_eq_p : q = p := by
        have : q = 1 * p := (div_eq_iff hp0).1 hqp_eq_one
        simpa using this
      exact hpq (by simpa [eq_comm] using hq_eq_p)
    have hlog : Real.log (q / p) < q / p - 1 := by
      exact Real.log_lt_sub_one_of_pos (div_pos hq_pos hp_pos) hqp_ne_one
    have hmul : (-p) * (q / p - 1) < (-p) * Real.log (q / p) := by
      exact mul_lt_mul_of_neg_left hlog (by linarith [hp_pos])

    have hratio : p / q = (q / p)⁻¹ := by
      field_simp [hp0, (ne_of_gt hq_pos)]

    have hlog_inv : Real.log (p / q) = -Real.log (q / p) := by
      have hqp_ne : q / p ≠ 0 := div_ne_zero (ne_of_gt hq_pos) hp0
      calc
        Real.log (p / q) = Real.log ((q / p)⁻¹) := by rw [hratio]
        _ = -Real.log (q / p) := by simpa [hqp_ne] using Real.log_inv (q / p)

    have hleft : p * Real.log (p / q) = (-p) * Real.log (q / p) := by
      rw [hlog_inv]
      ring

    have hright : (-p) * (q / p - 1) = p - q := by
      field_simp [hp0, (ne_of_gt hq_pos)]
      ring

    calc
      p - q = (-p) * (q / p - 1) := by simp [hright]
      _ < (-p) * Real.log (q / p) := hmul
      _ = p * Real.log (p / q) := by simp [hleft]

lemma kl_pointwise_eq_iff
    {p q : ℝ}
    (hp_nonneg : 0 ≤ p)
    (hq_pos : 0 < q) :
    p * Real.log (p / q) = p - q ↔ p = q := by
  constructor
  · intro hEq
    by_contra hpq
    have hstrict : p - q < p * Real.log (p / q) :=
      kl_pointwise_gt_sub_of_ne hp_nonneg hq_pos hpq
    have : p - q < p - q := by
      calc
        p - q < p * Real.log (p / q) := hstrict
        _ = p - q := hEq
    exact (lt_irrefl (p - q)) this
  · intro hpq
    subst hpq
    have hp_ne : p ≠ 0 := ne_of_gt hq_pos
    simp [hp_ne]

theorem KL_nonneg
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : FullSupport Q) :
    0 ≤ KLdivergence N_func Q := by
  let P : α → ℝ := empiricalDistribution N_func

  have hPnonneg : ∀ x, 0 ≤ P x := by
    intro x
    unfold P empiricalDistribution
    exact div_nonneg (by positivity) (by positivity)

  have hterm :
      ∀ x, P x - Q.prob x ≤ P x * Real.log (P x / Q.prob x) := by
    intro x
    exact kl_pointwise_ge_sub (hPnonneg x) (h_support x)

  have hsum :
      (∑ x, (P x - Q.prob x)) ≤ ∑ x, (P x * Real.log (P x / Q.prob x)) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact hterm x

  have hsumP : ∑ x, P x = 1 := by
    simpa [P] using empirical_sum_one N_func h_nontrivial

  have hsumQ : ∑ x, Q.prob x = 1 := Q.sum_one

  have hsum_diff_zero : ∑ x, (P x - Q.prob x) = 0 := by
    calc
      ∑ x, (P x - Q.prob x) = (∑ x, P x) - (∑ x, Q.prob x) := by
        rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by simp [hsumP, hsumQ]
      _ = 0 := by ring

  have hKL :
      KLdivergence N_func Q = ∑ x, (P x * Real.log (P x / Q.prob x)) := by
    unfold KLdivergence entropyExpectation surprisal densityRatio P
    simp

  rw [hKL]
  have hnonneg_sum : 0 ≤ ∑ x, (P x * Real.log (P x / Q.prob x)) := by
    have htmp : (∑ x, (P x - Q.prob x)) ≤ ∑ x, (P x * Real.log (P x / Q.prob x)) := hsum
    simpa [hsum_diff_zero] using htmp
  exact hnonneg_sum

theorem KL_eq_zero_iff
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (h_nontrivial : EmpiricalNontrivial N_func)
    (h_support : FullSupport Q) :
    KLdivergence N_func Q = 0 ↔
      ∀ x, empiricalDistribution N_func x = Q.prob x := by
  let P : α → ℝ := empiricalDistribution N_func

  have hPnonneg : ∀ x, 0 ≤ P x := by
    intro x
    unfold P empiricalDistribution
    exact div_nonneg (by positivity) (by positivity)

  have hterm :
      ∀ x, P x - Q.prob x ≤ P x * Real.log (P x / Q.prob x) := by
    intro x
    exact kl_pointwise_ge_sub (hPnonneg x) (h_support x)

  have hgap_nonneg :
      ∀ x, 0 ≤ P x * Real.log (P x / Q.prob x) - (P x - Q.prob x) := by
    intro x
    exact sub_nonneg.mpr (hterm x)

  have hsumP : ∑ x, P x = 1 := by
    simpa [P] using empirical_sum_one N_func h_nontrivial

  have hsumQ : ∑ x, Q.prob x = 1 := Q.sum_one

  have hsum_diff_zero : ∑ x, (P x - Q.prob x) = 0 := by
    calc
      ∑ x, (P x - Q.prob x) = (∑ x, P x) - (∑ x, Q.prob x) := by
        rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by simp [hsumP, hsumQ]
      _ = 0 := by ring

  have hKL :
      KLdivergence N_func Q = ∑ x, (P x * Real.log (P x / Q.prob x)) := by
    unfold KLdivergence entropyExpectation surprisal densityRatio P
    simp

  constructor
  · intro hKL_zero
    have hsum_term_zero : ∑ x, (P x * Real.log (P x / Q.prob x)) = 0 := by
      simpa [hKL] using hKL_zero
    have hsum_gap_zero :
        ∑ x, (P x * Real.log (P x / Q.prob x) - (P x - Q.prob x)) = 0 := by
      calc
        ∑ x, (P x * Real.log (P x / Q.prob x) - (P x - Q.prob x))
            = (∑ x, (P x * Real.log (P x / Q.prob x))) - (∑ x, (P x - Q.prob x)) := by
              rw [Finset.sum_sub_distrib]
        _ = 0 - 0 := by simp [hsum_term_zero, hsum_diff_zero]
        _ = 0 := by ring
    have hgap_eq_zero :
        ∀ x, P x * Real.log (P x / Q.prob x) - (P x - Q.prob x) = 0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun y hy => hgap_nonneg y)).1 hsum_gap_zero x (Finset.mem_univ x)
    intro x
    have h_eq :
        P x * Real.log (P x / Q.prob x) = P x - Q.prob x := by
      linarith [hgap_eq_zero x]
    have hPx : P x = Q.prob x := (kl_pointwise_eq_iff (hPnonneg x) (h_support x)).1 h_eq
    simpa [P] using hPx
  · intro hPQ
    rw [hKL]
    refine (Finset.sum_eq_zero_iff_of_nonneg ?h_nonneg).2 ?h_zero
    · intro x hx
      have hPx : P x = Q.prob x := by simpa [P] using hPQ x
      rw [hPx]
      have hQne : Q.prob x ≠ 0 := ne_of_gt (h_support x)
      simp [hQne]
    · intro x hx
      have hPx : P x = Q.prob x := by simpa [P] using hPQ x
      rw [hPx]
      have hQne : Q.prob x ≠ 0 := ne_of_gt (h_support x)
      simp [hQne]

noncomputable def logRNDensity
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (x : α) : ℝ :=
  Real.log (densityRatio N_func Q x)

noncomputable def relativeSurprisal
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (x : α) : ℝ :=
  -logRNDensity N_func Q x

/-- Z(τ) = ∑ Q(x) * exp(-τ * ℓ(x)). -/
noncomputable def partitionFunction
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  ∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)

/-- Φ(τ) = log Z(τ). -/
noncomputable def Phi
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  Real.log (partitionFunction N_func Q τ)

/-- Rényi section: D_τ = Φ(τ)/(τ-1). -/
noncomputable def RenyiD
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  Phi N_func Q τ / (τ - 1)

/-- Tilted probability kernel (requires Z(τ) ≠ 0). -/
noncomputable def tiltedProb
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (_hZ : partitionFunction N_func Q τ ≠ 0)
    (x : α) : ℝ :=
  (Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)) /
    (partitionFunction N_func Q τ)

/-- U(τ) = E_{μ_τ}[log r]. -/
noncomputable def internalEnergy
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  ∑ x, tiltedProb N_func Q τ hZ x * logRNDensity N_func Q x

/-- F(τ) = Φ(τ)/τ. -/
noncomputable def freeEnergy
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  Phi N_func Q τ / τ

/-- S(τ) = τ U(τ) - Φ(τ). -/
noncomputable def entropyAtTau
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (_hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  τ * internalEnergy N_func Q τ _hZ - Phi N_func Q τ

lemma hasDerivAt_partitionFunction
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    HasDerivAt (partitionFunction N_func Q)
      (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x) τ := by
  classical
  unfold partitionFunction
  change HasDerivAt
    (fun t : ℝ => ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x))
    (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
      logRNDensity N_func Q x) τ
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
        (logRNDensity N_func Q x) τ := by
    have hlin0 :
        HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
          (-relativeSurprisal N_func Q x) τ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id τ).neg.mul_const (relativeSurprisal N_func Q x))
    simpa [relativeSurprisal] using hlin0
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t * relativeSurprisal N_func Q x))
        (Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) τ := by
    exact (Real.hasDerivAt_exp (-τ * relativeSurprisal N_func Q x)).comp τ hlin
  simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (Q.prob x)

theorem deriv_partitionFunction
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    deriv (partitionFunction N_func Q) τ =
      ∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x := by
  exact (hasDerivAt_partitionFunction N_func Q τ).deriv

theorem dPhi_eq_internalEnergy
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) :
    deriv (Phi N_func Q) τ = internalEnergy N_func Q τ hZ := by
  have hlog :
      HasDerivAt (Phi N_func Q)
        ((∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q τ) τ := by
    simpa [Phi] using (hasDerivAt_partitionFunction N_func Q τ).log hZ
  calc
    deriv (Phi N_func Q) τ
        = ((∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q τ) := hlog.deriv
    _ = ∑ x,
          ((Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)) /
            partitionFunction N_func Q τ) *
            logRNDensity N_func Q x := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = internalEnergy N_func Q τ hZ := by
          simp [internalEnergy, tiltedProb, mul_comm]

lemma hasDerivAt_partitionFunctionLogMoment
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    HasDerivAt
      (fun t => ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x)
      (∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
        (logRNDensity N_func Q x) ^ 2) τ := by
  classical
  refine HasDerivAt.fun_sum ?_
  intro x hx
  have hlin :
      HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
        (logRNDensity N_func Q x) τ := by
    have hlin0 :
        HasDerivAt (fun t : ℝ => -t * relativeSurprisal N_func Q x)
          (-relativeSurprisal N_func Q x) τ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id τ).neg.mul_const (relativeSurprisal N_func Q x))
    simpa [relativeSurprisal] using hlin0
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t * relativeSurprisal N_func Q x))
        (Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) τ := by
    exact (Real.hasDerivAt_exp (-τ * relativeSurprisal N_func Q x)).comp τ hlin
  have hfactor :
      HasDerivAt
        (fun t : ℝ => Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x))
        (Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) τ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (Q.prob x)
  have hterm :
      HasDerivAt
        (fun t : ℝ => Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x)
        ((Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) * logRNDensity N_func Q x) τ := by
    simpa [mul_assoc] using hfactor.mul_const (logRNDensity N_func Q x)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hterm

theorem deriv_partitionFunctionLogMoment
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ) :
    deriv
      (fun t => ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
        logRNDensity N_func Q x) τ
      = ∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x) *
          (logRNDensity N_func Q x) ^ 2 := by
  exact (hasDerivAt_partitionFunctionLogMoment N_func Q τ).deriv

theorem deriv_Phi_eq_partition_ratio
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0) :
    deriv (Phi N_func Q) =
      fun t =>
        (∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
          logRNDensity N_func Q x) / partitionFunction N_func Q t := by
  funext t
  have hlog :
      HasDerivAt (Phi N_func Q)
        ((∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
            logRNDensity N_func Q x) /
          partitionFunction N_func Q t) t := by
    simpa [Phi] using (hasDerivAt_partitionFunction N_func Q t).log (hZ t)
  exact hlog.deriv

noncomputable def varianceLogRNDensity
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hZ : partitionFunction N_func Q τ ≠ 0) : ℝ :=
  (∑ x, tiltedProb N_func Q τ hZ x * (logRNDensity N_func Q x) ^ 2) -
    (internalEnergy N_func Q τ hZ) ^ 2

theorem d2Phi_eq_varianceLogRNDensity
    {α : Type*} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (hZ : ∀ t, partitionFunction N_func Q t ≠ 0)
    (τ : ℝ) :
    deriv (fun t => deriv (Phi N_func Q) t) τ =
      varianceLogRNDensity N_func Q τ (hZ τ) := by
  let Z : ℝ → ℝ := partitionFunction N_func Q
  let M1 : ℝ → ℝ := fun t =>
    ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
      logRNDensity N_func Q x
  let M2 : ℝ → ℝ := fun t =>
    ∑ x, Q.prob x * Real.exp (-t * relativeSurprisal N_func Q x) *
      (logRNDensity N_func Q x) ^ 2
  have hderivPhi : deriv (Phi N_func Q) = fun t => M1 t / Z t := by
    simpa [M1, Z] using deriv_Phi_eq_partition_ratio N_func Q hZ
  calc
    deriv (fun t => deriv (Phi N_func Q) t) τ
        = deriv (fun t => M1 t / Z t) τ := by
            simp [hderivPhi]
    _ = (deriv M1 τ * Z τ - M1 τ * deriv Z τ) / (Z τ) ^ 2 := by
          refine deriv_fun_div ?_ ?_ ?_
          · exact (hasDerivAt_partitionFunctionLogMoment N_func Q τ).differentiableAt
          · exact (hasDerivAt_partitionFunction N_func Q τ).differentiableAt
          · simpa [Z] using hZ τ
    _ = ((M2 τ) * Z τ - M1 τ * M1 τ) / (Z τ) ^ 2 := by
          rw [(hasDerivAt_partitionFunctionLogMoment N_func Q τ).deriv]
          rw [(hasDerivAt_partitionFunction N_func Q τ).deriv]
    _ = M2 τ / Z τ - (M1 τ / Z τ) ^ 2 := by
          have hZτ : Z τ ≠ 0 := by simpa [Z] using hZ τ
          field_simp [hZτ]
    _ = varianceLogRNDensity N_func Q τ (hZ τ) := by
          have hM2 :
              M2 τ / Z τ =
                ∑ x, tiltedProb N_func Q τ (hZ τ) x * (logRNDensity N_func Q x) ^ 2 := by
            unfold M2 Z partitionFunction
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [tiltedProb, partitionFunction]
            ring
          have hM1 : M1 τ / Z τ = internalEnergy N_func Q τ (hZ τ) := by
            unfold M1 Z partitionFunction internalEnergy
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [tiltedProb, partitionFunction]
            ring
          simp [varianceLogRNDensity, hM2, hM1]
