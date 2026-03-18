import Architect
import InfoGeometry.Basic
import InfoGeometry.KL.Finite
import InfoGeometry.MaxEnt.IProjection

open scoped BigOperators ENNReal NNReal

namespace InfoGeometry.EntropicInference

/-!
# Entropic Inference (Canonical implementation)

This module implements the core identities of entropic inference using the
canonical `FinProb` (alias for `PMF`) structure from `InfoGeometry.Basic`.
-/

/-- Joint distributions on `X × Θ`. -/
abbrev Joint (X Θ : Type*) [Fintype X] [Fintype Θ] := FinProb (X × Θ)

section BayesJeffreyFinite

variable {X Θ : Type*} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]

/-- Marginal on `X`. -/
noncomputable def marginal_x (p : Joint X Θ) : FinProb X :=
  p.map Prod.fst

/-- Marginal on `Θ`. -/
noncomputable def marginal_theta (p : Joint X Θ) : FinProb Θ :=
  p.map Prod.snd

omit [MeasurableSpace X] [MeasurableSpace Θ] in
/-- Pointwise formula for the `X`-marginal as a finite fiber sum. -/
lemma marginal_x_apply_sum (p : Joint X Θ) (x : X) :
    (marginal_x p) x = ∑ θ : Θ, p (x, θ) := by
  classical
  rw [marginal_x, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simpa using
    (Finset.sum_eq_single (s := (Finset.univ : Finset X)) (a := x)
      (f := fun x1 : X => ∑ y : Θ, if x = (x1, y).1 then p (x1, y) else 0)
      (by
        intro x1 _hx1 hx1ne
        apply Finset.sum_eq_zero
        intro y _hy
        by_cases hxy : x = x1
        · exact (hx1ne hxy.symm).elim
        · simp [hxy])
      (by
        intro hxnot
        simp at hxnot))

/-- Conditional `p(θ | x)`. -/
noncomputable def cond_theta_given_x
    (p : Joint X Θ) (x : X)
    (hx : x ∈ (marginal_x p).support) : FinProb Θ := by
  classical
  refine PMF.ofFintype (fun θ => p (x, θ) * ((marginal_x p x)⁻¹)) ?_
  have hmx : marginal_x p x = ∑ θ : Θ, p (x, θ) := marginal_x_apply_sum p x
  have hne : marginal_x p x ≠ 0 := (PMF.mem_support_iff (marginal_x p) x).1 hx
  have htop : marginal_x p x ≠ ⊤ := (marginal_x p).apply_ne_top x
  calc
    ∑ θ : Θ, p (x, θ) * ((marginal_x p x)⁻¹)
        = (∑ θ : Θ, p (x, θ)) * ((marginal_x p x)⁻¹) := by
          rw [Finset.sum_mul]
    _ = (marginal_x p x) * ((marginal_x p x)⁻¹) := by simp [hmx]
    _ = 1 := by simpa [hne, htop] using ENNReal.mul_inv_cancel hne htop

omit [MeasurableSpace X] [MeasurableSpace Θ] in
/-- Pointwise ratio formula for the finite conditional `p(θ | x)`. -/
lemma cond_theta_given_x_apply
    (p : Joint X Θ) (x : X)
    (hx : x ∈ (marginal_x p).support) (θ : Θ) :
    cond_theta_given_x p x hx θ = p (x, θ) * ((marginal_x p x)⁻¹) := by
  simp [cond_theta_given_x]

/-- Assemble a joint distribution from a marginal on `X` and conditionals on `Θ | X`. -/
noncomputable def assemble (p_x : FinProb X) (p_theta_given_x : X → FinProb Θ) :
    Joint X Θ :=
  p_x.bind (fun x => (p_theta_given_x x).map (fun θ => (x, θ)))

omit [MeasurableSpace X] [MeasurableSpace Θ] in
/-- Pointwise formula for an assembled joint law. -/
lemma assemble_apply (p_x : FinProb X) (p_theta_given_x : X → FinProb Θ) (x : X) (θ : Θ) :
    assemble p_x p_theta_given_x (x, θ) = p_x x * p_theta_given_x x θ := by
  classical
  rw [assemble, PMF.bind_apply, tsum_fintype]
  have hmap :
      ∀ a : X,
        ((p_theta_given_x a).map (fun θ => (a, θ)) (x, θ))
          = if x = a then p_theta_given_x a θ else 0 := by
    intro a
    rw [PMF.map_apply, tsum_fintype]
    by_cases hxa : x = a
    · subst hxa
      simp
    · simp [hxa]
  simp [hmap]

omit [MeasurableSpace X] [MeasurableSpace Θ] in
/-- Marginalizing an assembled joint recovers the original marginal `p_x`. -/
theorem marginal_x_assemble (p_x : FinProb X) (p_theta_given_x : X → FinProb Θ) :
    marginal_x (assemble p_x p_theta_given_x) = p_x := by
  rw [marginal_x, assemble, PMF.map_bind]
  simp [PMF.map_comp]



/-- Bayes posterior after observing `x₀`. -/
noncomputable def bayes_posterior
    (q_theta : FinProb Θ) (q_x_given_theta : Θ → FinProb X) (x0 : X)
    (hZ : x0 ∈
      (marginal_x
        (q_theta.bind (fun θ => (q_x_given_theta θ).map (fun x => (x, θ))))).support) :
    FinProb Θ := by
  let joint : Joint X Θ :=
    q_theta.bind (fun θ => (q_x_given_theta θ).map (fun x => (x, θ)))
  exact cond_theta_given_x joint x0 hZ

/-- Jeffrey joint update: replace `x`-marginal by `p_x`, preserve `q(θ | x)`. -/
noncomputable def jeffrey_joint
    (q : Joint X Θ) (p_x : FinProb X)
    (hq : ∀ x, x ∈ (marginal_x q).support) :
    Joint X Θ :=
  assemble p_x (fun x => cond_theta_given_x q x (hq x))

omit [MeasurableSpace X] [MeasurableSpace Θ] in
lemma marginal_x_jeffrey_joint
    (q : Joint X Θ) (p_x : FinProb X)
    (hq : ∀ x, x ∈ (marginal_x q).support) :
    marginal_x (jeffrey_joint q p_x hq) = p_x := by
  simpa [jeffrey_joint] using marginal_x_assemble p_x (fun x => cond_theta_given_x q x (hq x))

end BayesJeffreyFinite

section Decompositions

variable {X Θ : Type*} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]

/-- Kullback–Leibler divergence on joints. -/
noncomputable def kl (p q : Joint X Θ) : ℝ≥0∞ :=
  InfoGeometry.kl_div (α := X × Θ)
    (p.toMeasure : MeasureTheory.Measure (X × Θ))
    (q.toMeasure : MeasureTheory.Measure (X × Θ))

noncomputable abbrev KL {X Θ : Type*} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]
    (p q : Joint X Θ) : ℝ≥0∞ := kl p q

omit [MeasurableSpace X] [MeasurableSpace Θ] in
/--
Full-support transport along a marginal identity.
This is only a convenience lemma for the finite/full-support formulation.
-/
lemma full_support_of_marginal_eq
    {p : Joint X Θ} {p_x : FinProb X}
    (hmarg : marginal_x p = p_x)
    (hp : ∀ x : X, x ∈ (marginal_x p).support) :
    ∀ x : X, x ∈ p_x.support := by
  intro x
  simpa [← hmarg] using hp x

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  Strict positivity of all joint atoms implies strict positivity of each `X`-marginal atom.
  -/
lemma marginal_x_toReal_pos_of_joint_toReal_pos
    [Nonempty Θ]
    (p : Joint X Θ)
    (hpos : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal) :
    ∀ x : X, 0 < (marginal_x p x).toReal := by
  intro x
  let θ0 : Θ := Classical.choice inferInstance
  have hterm_pos : 0 < (p (x, θ0)).toReal := hpos x θ0
  have hterm_le : p (x, θ0) ≤ marginal_x p x := by
    rw [marginal_x_apply_sum]
    have hle' : p (x, θ0) ≤ (∑ θ : Θ, p (x, θ)) := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset Θ))
          (a := θ0)
          (f := fun θ : Θ => p (x, θ))
          (by
            intro θ _hθ
            exact zero_le _)
          (by simp))
    simpa using hle'
  have hle_real : (p (x, θ0)).toReal ≤ (marginal_x p x).toReal := by
    exact ENNReal.toReal_mono ((marginal_x p).apply_ne_top x) hterm_le
  exact lt_of_lt_of_le hterm_pos hle_real

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  Strict positivity of all joint atoms implies full support of the `X`-marginal.
  -/
lemma marginal_x_full_support_of_joint_toReal_pos
    [Nonempty Θ]
    (p : Joint X Θ)
    (hpos : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal) :
    ∀ x : X, x ∈ (marginal_x p).support := by
  intro x
  have hmx_pos : 0 < (marginal_x p x).toReal :=
    marginal_x_toReal_pos_of_joint_toReal_pos p hpos x
  have hmx_ne_zero_real : (marginal_x p x).toReal ≠ 0 := ne_of_gt hmx_pos
  have hmx_ne_zero : marginal_x p x ≠ 0 := by
    intro hzero
    exact hmx_ne_zero_real (by simp [hzero])
  exact (PMF.mem_support_iff (marginal_x p) x).2 hmx_ne_zero

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  `toReal` ratio formula for finite conditionals under strict positivity.
  -/
lemma cond_theta_given_x_toReal_ratio
    [Nonempty Θ]
    (p : Joint X Θ)
    (hpos : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (x : X) (θ : Θ) :
    (cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hpos x) θ).toReal
      = (p (x, θ)).toReal / (marginal_x p x).toReal := by
  have hcond :=
    cond_theta_given_x_apply p x (marginal_x_full_support_of_joint_toReal_pos p hpos x) θ
  rw [hcond, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  Factorization of a strictly positive joint into marginal times conditional, in `toReal` form.
  -/
lemma joint_toReal_factor_marginal_conditional
    [Nonempty Θ]
    (p : Joint X Θ)
    (hpos : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (x : X) (θ : Θ) :
    (p (x, θ)).toReal
      = (marginal_x p x).toReal *
        (cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hpos x) θ).toReal := by
  have hpx_pos : 0 < (marginal_x p x).toReal :=
    marginal_x_toReal_pos_of_joint_toReal_pos p hpos x
  have hpx_ne : (marginal_x p x).toReal ≠ 0 := ne_of_gt hpx_pos
  have hratio := cond_theta_given_x_toReal_ratio p hpos x θ
  rw [hratio]
  field_simp [hpx_ne]

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  Pointwise logarithmic split:
  `log (p(x,θ)/q(x,θ)) = log (p(x)/q(x)) + log (p(θ|x)/q(θ|x))`,
  for strictly positive finite joints.
  -/
lemma pointwise_log_split
    [Nonempty Θ]
    (p q : Joint X Θ)
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal)
    (x : X) (θ : Θ) :
    Real.log ((p (x, θ)).toReal / (q (x, θ)).toReal)
      = Real.log ((marginal_x p x).toReal / (marginal_x q x).toReal)
      + Real.log
          (((cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hposp x) θ).toReal)
            / ((cond_theta_given_x q x (marginal_x_full_support_of_joint_toReal_pos q hposq x) θ).toReal)) := by
  have hpxt : (p (x, θ)).toReal
      = (marginal_x p x).toReal *
        (cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hposp x) θ).toReal :=
    joint_toReal_factor_marginal_conditional p hposp x θ
  have hqxt : (q (x, θ)).toReal
      = (marginal_x q x).toReal *
        (cond_theta_given_x q x (marginal_x_full_support_of_joint_toReal_pos q hposq x) θ).toReal :=
    joint_toReal_factor_marginal_conditional q hposq x θ
  have hmxp_ne : (marginal_x p x).toReal ≠ 0 := by
    exact ne_of_gt (marginal_x_toReal_pos_of_joint_toReal_pos p hposp x)
  have hmxq_ne : (marginal_x q x).toReal ≠ 0 := by
    exact ne_of_gt (marginal_x_toReal_pos_of_joint_toReal_pos q hposq x)
  have hcp_ne :
      ((cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hposp x) θ).toReal) ≠ 0 := by
    rw [cond_theta_given_x_toReal_ratio p hposp x θ]
    exact div_ne_zero (ne_of_gt (hposp x θ)) hmxp_ne
  have hcq_ne :
      ((cond_theta_given_x q x (marginal_x_full_support_of_joint_toReal_pos q hposq x) θ).toReal) ≠ 0 := by
    rw [cond_theta_given_x_toReal_ratio q hposq x θ]
    exact div_ne_zero (ne_of_gt (hposq x θ)) hmxq_ne
  rw [hpxt, hqxt]
  have hdiv :
      ((marginal_x p x).toReal *
        (cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hposp x) θ).toReal)
        /
      (((marginal_x q x).toReal *
        (cond_theta_given_x q x (marginal_x_full_support_of_joint_toReal_pos q hposq x) θ).toReal))
      =
      (((marginal_x p x).toReal / (marginal_x q x).toReal) *
        (((cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hposp x) θ).toReal)
          / ((cond_theta_given_x q x (marginal_x_full_support_of_joint_toReal_pos q hposq x) θ).toReal))) := by
    field_simp [hmxq_ne, hcq_ne]
  rw [hdiv, Real.log_mul (div_ne_zero hmxp_ne hmxq_ne) (div_ne_zero hcp_ne hcq_ne)]

/--
Constructive finite KL chain rule in `toReal` form, under strict positivity.
-/
theorem kl_chain_rule_toReal_strict
    [DecidableEq X] [DecidableEq Θ]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Θ]
    [Nonempty Θ]
    (p q : Joint X Θ)
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal) :
    (kl p q).toReal =
      (InfoGeometry.kl_div (α := X) (marginal_x p).toMeasure (marginal_x q).toMeasure).toReal
      +
      (∑ x : X, (marginal_x p x).toReal *
        (InfoGeometry.kl_div (α := Θ)
          (cond_theta_given_x p x (marginal_x_full_support_of_joint_toReal_pos p hposp x)).toMeasure
          (cond_theta_given_x q x (marginal_x_full_support_of_joint_toReal_pos q hposq x)).toMeasure).toReal) := by
  let hp : ∀ x : X, x ∈ (marginal_x p).support := marginal_x_full_support_of_joint_toReal_pos p hposp
  let hq : ∀ x : X, x ∈ (marginal_x q).support := marginal_x_full_support_of_joint_toReal_pos q hposq
  let cp : X → Θ → ℝ := fun x θ => (cond_theta_given_x p x (hp x) θ).toReal
  let cq : X → Θ → ℝ := fun x θ => (cond_theta_given_x q x (hq x) θ).toReal
  let pj : X → Θ → ℝ := fun x θ => (p (x, θ)).toReal
  let logx : X → ℝ := fun x => Real.log ((marginal_x p x).toReal / (marginal_x q x).toReal)
  let logc : X → Θ → ℝ := fun x θ => Real.log (cp x θ / cq x θ)

  have hQ_joint : ∀ xt : X × Θ, 0 < (q xt).toReal := by
    intro xt
    exact hposq xt.1 xt.2
  have hQ_marg : ∀ x : X, 0 < (marginal_x q x).toReal :=
    marginal_x_toReal_pos_of_joint_toReal_pos q hposq
  have hQ_cond : ∀ x : X, ∀ θ : Θ, 0 < (cond_theta_given_x q x (hq x) θ).toReal := by
    intro x θ
    rw [cond_theta_given_x_toReal_ratio q hposq x θ]
    exact div_pos (hposq x θ) (marginal_x_toReal_pos_of_joint_toReal_pos q hposq x)

  have h_joint :
      (kl p q).toReal = ∑ xt : X × Θ, (p xt).toReal * Real.log ((p xt).toReal / (q xt).toReal) := by
    simpa [kl, InfoGeometry.kl_div] using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio (P := p) (Q := q) hQ_joint)
  have h_marg :
      (InfoGeometry.kl_div (α := X) (marginal_x p).toMeasure (marginal_x q).toMeasure).toReal
        = ∑ x : X, (marginal_x p x).toReal * logx x := by
    simpa [logx, InfoGeometry.kl_div] using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
        (P := marginal_x p) (Q := marginal_x q) hQ_marg)
  have h_cond_each :
      ∀ x : X,
        (InfoGeometry.kl_div (α := Θ)
          (cond_theta_given_x p x (hp x)).toMeasure
          (cond_theta_given_x q x (hq x)).toMeasure).toReal
        = ∑ θ : Θ, cp x θ * logc x θ := by
    intro x
    simpa [cp, logc, InfoGeometry.kl_div] using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
        (P := cond_theta_given_x p x (hp x))
        (Q := cond_theta_given_x q x (hq x))
        (hQ_cond x))

  rw [h_joint, h_marg]
  rw [Fintype.sum_prod_type]
  have hsplit :
      ∑ x : X, ∑ θ : Θ, pj x θ * Real.log ((p (x, θ)).toReal / (q (x, θ)).toReal)
      =
      ∑ x : X, ∑ θ : Θ, pj x θ * (logx x + logc x θ) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    refine Finset.sum_congr rfl ?_
    intro θ _hθ
    simp [pj, logx, logc, cp, cq, pointwise_log_split p q hposp hposq x θ]
  rw [hsplit]
  have hsplit2 :
      (∑ x : X, ∑ θ : Θ, pj x θ * (logx x + logc x θ))
      =
      (∑ x : X, ∑ θ : Θ, pj x θ * logx x)
      +
      (∑ x : X, ∑ θ : Θ, pj x θ * logc x θ) := by
    simp [mul_add, Finset.sum_add_distrib, add_comm]
  rw [hsplit2]

  have hfirst :
      (∑ x : X, ∑ θ : Θ, pj x θ * logx x)
      = ∑ x : X, (marginal_x p x).toReal * logx x := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [← Finset.sum_mul]
    congr 1
    simp [pj, marginal_x_apply_sum, ENNReal.toReal_sum, PMF.apply_ne_top]

  have hsecond :
      (∑ x : X, ∑ θ : Θ, pj x θ * logc x θ)
      = ∑ x : X, (marginal_x p x).toReal * (∑ θ : Θ, cp x θ * logc x θ) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    have hfac : ∀ θ : Θ, pj x θ = (marginal_x p x).toReal * cp x θ := by
      intro θ
      simp [pj, cp, joint_toReal_factor_marginal_conditional p hposp x θ]
    calc
      (∑ θ : Θ, pj x θ * logc x θ)
          = (∑ θ : Θ, ((marginal_x p x).toReal * cp x θ) * logc x θ) := by
              refine Finset.sum_congr rfl ?_
              intro θ _hθ
              rw [hfac θ]
      _ = (∑ θ : Θ, (marginal_x p x).toReal * (cp x θ * logc x θ)) := by
            refine Finset.sum_congr rfl ?_
            intro θ _hθ
            ring
      _ = (marginal_x p x).toReal * (∑ θ : Θ, cp x θ * logc x θ) := by
            rw [Finset.mul_sum]

  rw [hfirst, hsecond]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [h_cond_each x]

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  Conditionals of an assembled joint recover the input kernel.
  This is the finite `Θ | X` reconstruction lemma.
  -/
lemma cond_theta_given_x_assemble
    (p_x : FinProb X) (r : X → FinProb Θ)
    {x : X} (hx : x ∈ p_x.support) :
    cond_theta_given_x (assemble p_x r) x
      (by simpa [marginal_x_assemble] using hx) = r x := by
  ext θ
  have hx0 : p_x x ≠ 0 := (PMF.mem_support_iff p_x x).1 hx
  have hxtop : p_x x ≠ ⊤ := p_x.apply_ne_top x
  have hcancel : p_x x * (p_x x)⁻¹ = 1 := ENNReal.mul_inv_cancel hx0 hxtop
  calc
    cond_theta_given_x (assemble p_x r) x (by simpa [marginal_x_assemble] using hx) θ
        = p_x x * (r x θ * (p_x x)⁻¹) := by
          simp [cond_theta_given_x_apply, assemble_apply, marginal_x_assemble, mul_comm,
            mul_left_comm]
    _ = (p_x x * (p_x x)⁻¹) * r x θ := by ac_rfl
    _ = r x θ := by simp [hcancel]

  omit [MeasurableSpace X] [MeasurableSpace Θ] in
  /--
  Jeffrey update preserves the conditional family `q(θ | x)`.
  -/
lemma cond_theta_given_x_jeffrey_joint
    (q : Joint X Θ) (p_x : FinProb X)
    (hq : ∀ x : X, x ∈ (marginal_x q).support)
    {x : X} (hx : x ∈ p_x.support) :
    cond_theta_given_x (jeffrey_joint q p_x hq) x
      (by simpa [marginal_x_jeffrey_joint] using hx)
      =
    cond_theta_given_x q x (hq x) := by
  simpa [jeffrey_joint] using
    (cond_theta_given_x_assemble (p_x := p_x)
      (r := fun x => cond_theta_given_x q x (hq x)) (x := x) hx)

/--
Constructive KL-Pythagorean theorem in `toReal` form for strictly positive finite joints.

This version removes explicit `KlChainRule` hypotheses by deriving the chain-rule
equalities from `kl_chain_rule_toReal_strict`.
-/
theorem kl_pythagorean_jeffrey_toReal_strict
    [DecidableEq X] [DecidableEq Θ]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Θ]
    [Nonempty Θ]
    (p q : Joint X Θ)
    (p_x : FinProb X)
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal)
    (hmarg : marginal_x p = p_x) :
    (kl p q).toReal =
      (kl p (jeffrey_joint q p_x
        (marginal_x_full_support_of_joint_toReal_pos q hposq))).toReal
      +
      (InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal := by
  let hq : ∀ x : X, x ∈ (marginal_x q).support :=
    marginal_x_full_support_of_joint_toReal_pos q hposq
  let qStar : Joint X Θ := jeffrey_joint q p_x hq

  have hpos_p_x : ∀ x : X, 0 < (p_x x).toReal := by
    intro x
    simpa [hmarg] using (marginal_x_toReal_pos_of_joint_toReal_pos p hposp x)

  have hpos_qStar : ∀ x : X, ∀ θ : Θ, 0 < (qStar (x, θ)).toReal := by
    intro x θ
    have hcond_pos :
        0 <
          (cond_theta_given_x q x (hq x) θ).toReal := by
      rw [cond_theta_given_x_toReal_ratio q hposq x θ]
      exact div_pos (hposq x θ) (marginal_x_toReal_pos_of_joint_toReal_pos q hposq x)
    have hqStar_apply :
        qStar (x, θ) = p_x x * cond_theta_given_x q x (hq x) θ := by
      simpa [qStar, jeffrey_joint] using
        (assemble_apply p_x (fun x => cond_theta_given_x q x (hq x)) x θ)
    rw [hqStar_apply, ENNReal.toReal_mul]
    exact mul_pos (hpos_p_x x) hcond_pos

  have hqStar_support : ∀ x : X, x ∈ (marginal_x qStar).support :=
    marginal_x_full_support_of_joint_toReal_pos qStar hpos_qStar
  have hp_support : ∀ x : X, x ∈ (marginal_x p).support :=
    marginal_x_full_support_of_joint_toReal_pos p hposp

  have hmx_qstar : marginal_x qStar = p_x := by
    simpa [qStar] using marginal_x_jeffrey_joint (q := q) (p_x := p_x) hq

  have hkl_self_toReal :
      (InfoGeometry.kl_div (α := X) p_x.toMeasure p_x.toMeasure).toReal = 0 := by
      simp [InfoGeometry.kl_div]

  have hres :
      (kl p qStar).toReal =
        ∑ x : X, (marginal_x p x).toReal *
          (InfoGeometry.kl_div (α := Θ)
            (cond_theta_given_x p x (hp_support x)).toMeasure
            (cond_theta_given_x q x (hq x)).toMeasure).toReal := by
    have htmp :=
      kl_chain_rule_toReal_strict
        (p := p) (q := qStar) (hposp := hposp) (hposq := hpos_qStar)
    rw [htmp]
    rw [hmarg, hmx_qstar, hkl_self_toReal, zero_add]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxpx : x ∈ p_x.support := by
      have hne : p_x x ≠ 0 := by
        exact fun h0 => (ne_of_gt (hpos_p_x x)) (by simp [h0])
      exact (PMF.mem_support_iff p_x x).2 hne
    have hcond :
        cond_theta_given_x qStar x (hqStar_support x) =
          cond_theta_given_x q x (hq x) := by
      calc
        cond_theta_given_x qStar x (hqStar_support x)
            = cond_theta_given_x qStar x (by simpa [hmx_qstar] using hxpx) := by
                exact congrArg (fun h : x ∈ (marginal_x qStar).support =>
                  cond_theta_given_x qStar x h) (Subsingleton.elim _ _)
        _ = cond_theta_given_x q x (hq x) := by
            simpa [qStar] using
              (cond_theta_given_x_jeffrey_joint
                (q := q) (p_x := p_x) (hq := hq) (x := x) hxpx)
    rw [hcond]

  have hchain1 :=
    kl_chain_rule_toReal_strict (p := p) (q := q) (hposp := hposp) (hposq := hposq)

  calc
    (kl p q).toReal
        =
          (InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal
          +
          (∑ x : X, (marginal_x p x).toReal *
            (InfoGeometry.kl_div (α := Θ)
              (cond_theta_given_x p x (hp_support x)).toMeasure
              (cond_theta_given_x q x (hq x)).toMeasure).toReal) := by
      simpa [hmarg] using hchain1
    _ =
          (InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal
          +
          (kl p qStar).toReal := by
      rw [hres]
    _ =
          (kl p qStar).toReal
          +
          (InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal := by
      ring
    _ =
          (kl p (jeffrey_joint q p_x
            (marginal_x_full_support_of_joint_toReal_pos q hposq))).toReal
          +
          (InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal := by
        simp [qStar]

/--
If the right argument `Q` has strictly positive atoms (in `toReal`), then
`KL(P ‖ Q)` is finite (`≠ ⊤`) for finite PMFs.
-/
lemma kl_div_ne_top_of_right_toReal_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : FinProb α)
    (hQ : ∀ x : α, 0 < (Q x).toReal) :
    InfoGeometry.kl_div (α := α) P.toMeasure Q.toMeasure ≠ ⊤ := by
  change InformationTheory.klDiv P.toMeasure Q.toMeasure ≠ ⊤
  rw [InformationTheory.klDiv_ne_top_iff]
  refine ⟨?_, ?_⟩
  · intro s hQs
    have hs : MeasurableSet s := (Set.toFinite s).measurableSet
    have hQs' : Disjoint Q.support s := (Q.toMeasure_apply_eq_zero_iff hs).1 hQs
    refine (P.toMeasure_apply_eq_zero_iff hs).2 ?_
    refine Set.disjoint_left.2 ?_
    intro x _hxP hxS
    have hxQ : x ∈ Q.support := by
      refine (Q.mem_support_iff x).2 ?_
      intro h0
      have : 0 < (Q x).toReal := hQ x
      simp [h0] at this
    exact (Set.disjoint_left.1 hQs' hxQ) hxS
  · exact
      (InfoGeometry.MaxEnt.IProjection.integrable_of_fintype
        (f := MeasureTheory.llr P.toMeasure Q.toMeasure) (μ := P.toMeasure))

/--
Constructive KL-Pythagorean theorem in `ℝ≥0∞` form for strictly positive finite joints.

This is the `ℝ≥0∞` lift of `kl_pythagorean_jeffrey_toReal_strict`, with
finiteness discharged constructively from strict positivity.
-/
theorem kl_pythagorean_jeffrey_strict
    [DecidableEq X] [DecidableEq Θ]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Θ]
    [Nonempty Θ]
    (p q : Joint X Θ)
    (p_x : FinProb X)
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal)
    (hmarg : marginal_x p = p_x) :
    kl p q =
      kl p (jeffrey_joint q p_x
        (marginal_x_full_support_of_joint_toReal_pos q hposq))
      +
      InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure := by
  let hq : ∀ x : X, x ∈ (marginal_x q).support :=
    marginal_x_full_support_of_joint_toReal_pos q hposq
  let qStar : Joint X Θ := jeffrey_joint q p_x hq

  have htoReal :
      (kl p q).toReal =
        (kl p qStar).toReal +
        (InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal := by
    simpa [qStar, hq] using
      kl_pythagorean_jeffrey_toReal_strict
        (p := p) (q := q) (p_x := p_x) (hposp := hposp) (hposq := hposq) (hmarg := hmarg)

  have hpos_qStar : ∀ x : X, ∀ θ : Θ, 0 < (qStar (x, θ)).toReal := by
    intro x θ
    have hpos_px : 0 < (p_x x).toReal := by
      simpa [hmarg] using (marginal_x_toReal_pos_of_joint_toReal_pos p hposp x)
    have hcond_pos :
        0 < (cond_theta_given_x q x (hq x) θ).toReal := by
      rw [cond_theta_given_x_toReal_ratio q hposq x θ]
      exact div_pos (hposq x θ) (marginal_x_toReal_pos_of_joint_toReal_pos q hposq x)
    have hqStar_apply :
        qStar (x, θ) = p_x x * cond_theta_given_x q x (hq x) θ := by
      simpa [qStar, jeffrey_joint] using
        (assemble_apply p_x (fun x => cond_theta_given_x q x (hq x)) x θ)
    rw [hqStar_apply, ENNReal.toReal_mul]
    exact mul_pos hpos_px hcond_pos

  have hq_joint_pos : ∀ xt : X × Θ, 0 < (q xt).toReal := by
    intro xt
    exact hposq xt.1 xt.2

  have hqStar_joint_pos : ∀ xt : X × Θ, 0 < (qStar xt).toReal := by
    intro xt
    exact hpos_qStar xt.1 xt.2

  have hmxq_pos : ∀ x : X, 0 < (marginal_x q x).toReal :=
    marginal_x_toReal_pos_of_joint_toReal_pos q hposq

  have hleft_ne_top : kl p q ≠ ⊤ := by
    simpa [kl] using
      (kl_div_ne_top_of_right_toReal_pos (P := p) (Q := q) hq_joint_pos)

  have hright1_ne_top : kl p qStar ≠ ⊤ := by
    simpa [kl] using
      (kl_div_ne_top_of_right_toReal_pos (P := p) (Q := qStar) hqStar_joint_pos)

  have hright2_ne_top :
      InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure ≠ ⊤ := by
    exact kl_div_ne_top_of_right_toReal_pos (P := p_x) (Q := marginal_x q) hmxq_pos

  have hsum_ne_top :
      kl p qStar +
        InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨hright1_ne_top, hright2_ne_top⟩

  have htoReal_sum :
      (kl p q).toReal =
        (kl p qStar +
          InfoGeometry.kl_div (α := X) p_x.toMeasure (marginal_x q).toMeasure).toReal := by
    rw [ENNReal.toReal_add hright1_ne_top hright2_ne_top]
    exact htoReal

  apply (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hsum_ne_top).mp
  exact htoReal_sum

/-- Mutual information `I(X;Θ)`. -/
noncomputable def mutual_information (p : Joint X Θ) : ℝ≥0∞ :=
  kl p (assemble (marginal_x p) (fun _ => marginal_theta p))

/-- Dirac distribution at `x`. -/
noncomputable def dirac {α : Type*} (x : α) : FinProb α :=
  PMF.pure x

end Decompositions

end InfoGeometry.EntropicInference
