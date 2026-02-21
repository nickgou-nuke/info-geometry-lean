import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Grand Canonical Core

Finite-state thermodynamic models with Gibbs weights:
- canonical specialization (`β` and energy only),
- genuine grand-canonical extension (`β`, `μ`, energy and number).
-/

namespace InfoGeometry.GrandCanonical

open scoped BigOperators

/--
Canonical-specialization data: an energy observable on a finite state space.

This is the `μ = 0`/single-observable slice of the full grand-canonical model.
-/
structure GrandCanonicalParams (α : Type _) where
  energy : α → ℝ

section FiniteModel

variable {α : Type _} [Fintype α] [Nonempty α]

/-- Partition function `Z(β) = ∑ₓ exp(-β E(x))`. -/
noncomputable def partition (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, Real.exp (-β * params.energy x)

lemma partition_pos (params : GrandCanonicalParams α) (β : ℝ) :
    0 < partition params β := by
  classical
  unfold partition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset α))
      (f := fun x => Real.exp (-β * params.energy x))
      (by
        intro x hx
        exact Real.exp_pos _)
      Finset.univ_nonempty)

/-- Log-partition potential `ψ(β) = log Z(β)`. -/
noncomputable def potential (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  Real.log (partition params β)

/-- Gibbs weight at inverse temperature `β`. -/
noncomputable def gibbsWeight
    (params : GrandCanonicalParams α) (β : ℝ) (x : α) : ℝ :=
  Real.exp (-β * params.energy x) / partition params β

lemma gibbsWeight_nonneg
    (params : GrandCanonicalParams α) (β : ℝ) (x : α) :
    0 ≤ gibbsWeight params β x := by
  unfold gibbsWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (partition_pos params β))

lemma gibbsWeight_pos
    (params : GrandCanonicalParams α) (β : ℝ) (x : α) :
    0 < gibbsWeight params β x := by
  unfold gibbsWeight
  exact div_pos (Real.exp_pos _) (partition_pos params β)

lemma gibbsWeight_sum_one
    (params : GrandCanonicalParams α) (β : ℝ) :
    ∑ x, gibbsWeight params β x = 1 := by
  unfold gibbsWeight partition
  have hZne : (∑ y : α, Real.exp (-β * params.energy y)) ≠ 0 :=
    ne_of_gt (partition_pos params β)
  calc
    ∑ x : α, Real.exp (-β * params.energy x) / ∑ y : α, Real.exp (-β * params.energy y)
        = (∑ x : α, Real.exp (-β * params.energy x)) / ∑ y : α, Real.exp (-β * params.energy y) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset α))
                (f := fun x => Real.exp (-β * params.energy x))
                (a := ∑ y : α, Real.exp (-β * params.energy y)))
    _ = 1 := by exact div_self hZne

/-- Mean energy under the Gibbs distribution. -/
noncomputable def mean (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, gibbsWeight params β x * params.energy x

/-- Unnormalized first energy moment `M₁(β) = ∑ₓ E(x) exp(-β E(x))`. -/
noncomputable def firstMomentUnnormalized
    (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, params.energy x * Real.exp (-β * params.energy x)

/-- Unnormalized second energy moment `M₂(β) = ∑ₓ E(x)^2 exp(-β E(x))`. -/
noncomputable def secondMomentUnnormalized
    (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, (params.energy x) ^ (2 : ℕ) * Real.exp (-β * params.energy x)

/-- Normalized second energy moment under the Gibbs distribution. -/
noncomputable def secondMoment (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, gibbsWeight params β x * (params.energy x) ^ (2 : ℕ)

-- Pointwise derivative for Gibbs exponential kernels.
omit [Fintype α] [Nonempty α] in
lemma hasDerivAt_exp_neg_mul_energy
    (params : GrandCanonicalParams α) (β : ℝ) (x : α) :
    HasDerivAt
      (fun t : ℝ => Real.exp (-t * params.energy x))
      (-(params.energy x) * Real.exp (-β * params.energy x))
      β := by
  have hlin : HasDerivAt (fun t : ℝ => -t * params.energy x) (-(params.energy x)) β := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id' β).const_mul (-(params.energy x)))
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_exp (-β * params.energy x)).comp β hlin

/-- Derivative kernel for the partition function. -/
noncomputable def partitionDerivFun
    (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, -(params.energy x) * Real.exp (-β * params.energy x)

omit [Nonempty α] in
lemma partitionDerivFun_eq_neg_firstMoment
    (params : GrandCanonicalParams α) (β : ℝ) :
    partitionDerivFun params β = -firstMomentUnnormalized params β := by
  unfold partitionDerivFun firstMomentUnnormalized
  simp [Finset.sum_neg_distrib]

omit [Nonempty α] in
lemma hasDerivAt_partition
    (params : GrandCanonicalParams α) (β : ℝ) :
    HasDerivAt (partition params) (partitionDerivFun params β) β := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ x, Real.exp (-t * params.energy x))
        (∑ x, -(params.energy x) * Real.exp (-β * params.energy x))
        β := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset α))
        (fun x _hx => hasDerivAt_exp_neg_mul_energy params β x))
  unfold partition partitionDerivFun
  simpa [neg_mul] using hsum

omit [Nonempty α] in
lemma deriv_partition
    (params : GrandCanonicalParams α) (β : ℝ) :
    deriv (partition params) β = partitionDerivFun params β :=
  (hasDerivAt_partition params β).deriv

omit [Fintype α] [Nonempty α] in
lemma hasDerivAt_partitionDerivTerm
    (params : GrandCanonicalParams α) (β : ℝ) (x : α) :
    HasDerivAt
      (fun t : ℝ => -(params.energy x) * Real.exp (-t * params.energy x))
      ((params.energy x) ^ (2 : ℕ) * Real.exp (-β * params.energy x))
      β := by
  have hmul := (hasDerivAt_exp_neg_mul_energy params β x).const_mul (-(params.energy x))
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul

omit [Nonempty α] in
lemma hasDerivAt_partitionDerivFun
    (params : GrandCanonicalParams α) (β : ℝ) :
    HasDerivAt (partitionDerivFun params) (secondMomentUnnormalized params β) β := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ x, -(params.energy x) * Real.exp (-t * params.energy x))
        (∑ x, (params.energy x) ^ (2 : ℕ) * Real.exp (-β * params.energy x))
        β := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset α))
        (fun x _hx => hasDerivAt_partitionDerivTerm params β x))
  unfold partitionDerivFun secondMomentUnnormalized
  simpa [neg_mul, Finset.sum_neg_distrib] using hsum

omit [Nonempty α] in
lemma deriv_partitionDerivFun
    (params : GrandCanonicalParams α) (β : ℝ) :
    deriv (partitionDerivFun params) β = secondMomentUnnormalized params β :=
  (hasDerivAt_partitionDerivFun params β).deriv

lemma potential_deriv_eq_partitionDeriv_div_partition
    (params : GrandCanonicalParams α) (β : ℝ) :
    deriv (potential params) β = partitionDerivFun params β / partition params β := by
  unfold potential
  have hdiff : DifferentiableAt ℝ (partition params) β :=
    (hasDerivAt_partition params β).differentiableAt
  have hne : partition params β ≠ 0 := ne_of_gt (partition_pos params β)
  calc
    deriv (fun β => Real.log (partition params β)) β
        = deriv (partition params) β / partition params β := by
            simpa using (deriv.log (f := partition params) hdiff hne)
    _ = partitionDerivFun params β / partition params β := by
          rw [deriv_partition]

lemma mean_eq_firstMoment_div_partition
    (params : GrandCanonicalParams α) (β : ℝ) :
    mean params β = firstMomentUnnormalized params β / partition params β := by
  unfold mean firstMomentUnnormalized gibbsWeight
  have hZne : partition params β ≠ 0 := ne_of_gt (partition_pos params β)
  calc
    ∑ x, (Real.exp (-β * params.energy x) / partition params β) * params.energy x
        = ∑ x, (params.energy x * Real.exp (-β * params.energy x)) / partition params β := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            field_simp [hZne]
    _ = (∑ x, params.energy x * Real.exp (-β * params.energy x)) / partition params β := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset α))
              (f := fun x => params.energy x * Real.exp (-β * params.energy x))
              (a := partition params β))
    _ = firstMomentUnnormalized params β / partition params β := by
          rfl

lemma secondMoment_eq_secondMomentUnnormalized_div_partition
    (params : GrandCanonicalParams α) (β : ℝ) :
    secondMoment params β = secondMomentUnnormalized params β / partition params β := by
  unfold secondMoment secondMomentUnnormalized gibbsWeight
  have hZne : partition params β ≠ 0 := ne_of_gt (partition_pos params β)
  calc
    ∑ x, (Real.exp (-β * params.energy x) / partition params β) * params.energy x ^ (2 : ℕ)
        = ∑ x, (params.energy x ^ (2 : ℕ) * Real.exp (-β * params.energy x)) / partition params β := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            field_simp [hZne]
    _ = (∑ x, params.energy x ^ (2 : ℕ) * Real.exp (-β * params.energy x)) / partition params β := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset α))
              (f := fun x => params.energy x ^ (2 : ℕ) * Real.exp (-β * params.energy x))
              (a := partition params β))
    _ = secondMomentUnnormalized params β / partition params β := by
          rfl

/-- First derivative identity: `ψ'(β) = - E_β[E]`. -/
lemma potential_deriv_eq_neg_mean
    (params : GrandCanonicalParams α) (β : ℝ) :
    deriv (potential params) β = -mean params β := by
  rw [potential_deriv_eq_partitionDeriv_div_partition]
  rw [partitionDerivFun_eq_neg_firstMoment, neg_div, mean_eq_firstMoment_div_partition]

/-- Energy variance under the Gibbs distribution. -/
noncomputable def variance (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  ∑ x, gibbsWeight params β x * (params.energy x - mean params β) ^ (2 : ℕ)

lemma variance_nonneg
    (params : GrandCanonicalParams α) (β : ℝ) :
    0 ≤ variance params β := by
  unfold variance
  refine Finset.sum_nonneg ?_
  intro x hx
  exact mul_nonneg (gibbsWeight_nonneg params β x) (pow_two_nonneg _)

lemma variance_eq_zero_iff_energy_eq_mean
    (params : GrandCanonicalParams α) (β : ℝ) :
    variance params β = 0 ↔ ∀ x, params.energy x = mean params β := by
  constructor
  · intro hvar x
    have hnonneg :
        ∀ y ∈ (Finset.univ : Finset α),
          0 ≤ gibbsWeight params β y * (params.energy y - mean params β) ^ (2 : ℕ) := by
      intro y hy
      exact mul_nonneg (gibbsWeight_nonneg params β y) (pow_two_nonneg _)
    have hsum :
        ∑ y, gibbsWeight params β y * (params.energy y - mean params β) ^ (2 : ℕ) = 0 := by
      simpa [variance] using hvar
    have hterm :
        gibbsWeight params β x * (params.energy x - mean params β) ^ (2 : ℕ) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum x (Finset.mem_univ x)
    have hsq :
        (params.energy x - mean params β) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (gibbsWeight_pos params β x))
    have hdiff0 : params.energy x - mean params β = 0 := by
      exact (sq_eq_zero_iff).1 (by simpa [pow_two] using hsq)
    linarith
  · intro hE
    unfold variance
    refine Finset.sum_eq_zero ?_
    intro x hx
    simp [hE x]

/-- One-observable covariance, equal to variance. -/
noncomputable def covariance (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  variance params β

/-- Second derivative of the log-partition potential. -/
noncomputable def hessian (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  deriv (fun t => deriv (potential params) t) β

/-- Spinodal condition: vanishing Hessian of the log-partition potential. -/
def Spinodal (params : GrandCanonicalParams α) (β : ℝ) : Prop :=
  hessian params β = 0

lemma variance_eq_secondMoment_sub_mean_sq
    (params : GrandCanonicalParams α) (β : ℝ) :
    variance params β = secondMoment params β - (mean params β) ^ (2 : ℕ) := by
  have hexpand :
      variance params β
        = secondMoment params β
          - 2 * mean params β * (∑ x, gibbsWeight params β x * params.energy x)
          + (mean params β) ^ (2 : ℕ) * (∑ x, gibbsWeight params β x) := by
    unfold variance secondMoment
    calc
      ∑ x, gibbsWeight params β x * (params.energy x - mean params β) ^ (2 : ℕ)
          =
          ∑ x,
            (gibbsWeight params β x * params.energy x ^ (2 : ℕ)
              - (2 * mean params β) * (gibbsWeight params β x * params.energy x)
              + (mean params β) ^ (2 : ℕ) * gibbsWeight params β x) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                ring
      _ =
          (∑ x, gibbsWeight params β x * params.energy x ^ (2 : ℕ))
            - (2 * mean params β) * (∑ x, gibbsWeight params β x * params.energy x)
            + (mean params β) ^ (2 : ℕ) * (∑ x, gibbsWeight params β x) := by
              calc
                ∑ x,
                    (gibbsWeight params β x * params.energy x ^ (2 : ℕ)
                      - (2 * mean params β) * (gibbsWeight params β x * params.energy x)
                      + (mean params β) ^ (2 : ℕ) * gibbsWeight params β x)
                    =
                    (∑ x, gibbsWeight params β x * params.energy x ^ (2 : ℕ))
                      - (∑ x, (2 * mean params β) * (gibbsWeight params β x * params.energy x))
                      + (∑ x, (mean params β) ^ (2 : ℕ) * gibbsWeight params β x) := by
                        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                _ =
                    (∑ x, gibbsWeight params β x * params.energy x ^ (2 : ℕ))
                      - (2 * mean params β) * (∑ x, gibbsWeight params β x * params.energy x)
                      + (mean params β) ^ (2 : ℕ) * (∑ x, gibbsWeight params β x) := by
                        simp [Finset.mul_sum]
  rw [hexpand, gibbsWeight_sum_one]
  rw [show (∑ x, gibbsWeight params β x * params.energy x) = mean params β by rfl]
  ring

lemma hessian_eq_secondMoment_sub_mean_sq
    (params : GrandCanonicalParams α) (β : ℝ) :
    hessian params β = secondMoment params β - (mean params β) ^ (2 : ℕ) := by
  unfold hessian
  have hderivFun :
      (fun t => deriv (potential params) t)
        = fun t => partitionDerivFun params t / partition params t := by
    funext t
    exact potential_deriv_eq_partitionDeriv_div_partition params t
  rw [hderivFun]
  have hnumDiff : DifferentiableAt ℝ (partitionDerivFun params) β :=
    (hasDerivAt_partitionDerivFun params β).differentiableAt
  have hdenDiff : DifferentiableAt ℝ (partition params) β :=
    (hasDerivAt_partition params β).differentiableAt
  have hZne : partition params β ≠ 0 := ne_of_gt (partition_pos params β)
  have hquot :
      deriv (fun t => partitionDerivFun params t / partition params t) β
        =
        (deriv (partitionDerivFun params) β * partition params β
          - partitionDerivFun params β * deriv (partition params) β) /
          (partition params β) ^ (2 : ℕ) := by
    simpa using
      (deriv_div (c := partitionDerivFun params) (d := partition params)
        (x := β) hnumDiff hdenDiff hZne)
  rw [hquot]
  rw [deriv_partitionDerivFun, deriv_partition]
  set Z := partition params β
  set M1 := firstMomentUnnormalized params β
  set M2 := secondMomentUnnormalized params β
  have hZ : Z ≠ 0 := by
    simpa [Z] using hZne
  have hM1 : mean params β = M1 / Z := by
    simpa [M1, Z] using mean_eq_firstMoment_div_partition params β
  have hM2 : secondMoment params β = M2 / Z := by
    simpa [M2, Z] using secondMoment_eq_secondMomentUnnormalized_div_partition params β
  have hD : partitionDerivFun params β = -M1 := by
    simpa [M1] using partitionDerivFun_eq_neg_firstMoment params β
  rw [hM1, hM2, hD]
  field_simp [hZ]

/-- Main finite-model identity: Hessian log-partition equals Gibbs variance. -/
theorem potential_second_derivative_eq_variance
    (params : GrandCanonicalParams α)
    (β : ℝ) :
    hessian params β = variance params β := by
  rw [hessian_eq_secondMoment_sub_mean_sq, variance_eq_secondMoment_sub_mean_sq]

lemma spinodal_iff_variance_eq_zero
    (params : GrandCanonicalParams α) (β : ℝ) :
    Spinodal params β ↔ variance params β = 0 := by
  unfold Spinodal
  rw [potential_second_derivative_eq_variance]

lemma hessian_nonneg
    (params : GrandCanonicalParams α) (β : ℝ) :
    0 ≤ hessian params β := by
  rw [potential_second_derivative_eq_variance]
  exact variance_nonneg params β

lemma spinodal_iff_energy_eq_mean
    (params : GrandCanonicalParams α) (β : ℝ) :
    Spinodal params β ↔ ∀ x, params.energy x = mean params β := by
  rw [spinodal_iff_variance_eq_zero, variance_eq_zero_iff_energy_eq_mean]

end FiniteModel

/--
Genuine grand-canonical data: energy and number observables on a finite state space.
-/
structure GrandCanonicalTwoParam (α : Type _) where
  energy : α → ℝ
  number : α → ℝ

section FiniteGrandCanonicalModel

variable {α : Type _} [Fintype α] [Nonempty α]

/-- Shifted observable `E(x) - μ N(x)` entering the grand-canonical kernel. -/
noncomputable def shiftedEnergy
    (params : GrandCanonicalTwoParam α) (μ : ℝ) (x : α) : ℝ :=
  params.energy x - μ * params.number x

/-- Two-parameter grand-canonical partition function `Z(β, μ)`. -/
noncomputable def partitionGC
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, Real.exp (-β * shiftedEnergy params μ x)

lemma partitionGC_pos
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    0 < partitionGC params β μ := by
  classical
  unfold partitionGC
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset α))
      (f := fun x => Real.exp (-β * shiftedEnergy params μ x))
      (by
        intro x hx
        exact Real.exp_pos _)
      Finset.univ_nonempty)

/-- Log-partition potential `ψ(β, μ) = log Z(β, μ)`. -/
noncomputable def potentialGC
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  Real.log (partitionGC params β μ)

/-- Gibbs weight at thermodynamic parameters `(β, μ)`. -/
noncomputable def gibbsWeightGC
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) : ℝ :=
  Real.exp (-β * shiftedEnergy params μ x) / partitionGC params β μ

lemma gibbsWeightGC_nonneg
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    0 ≤ gibbsWeightGC params β μ x := by
  unfold gibbsWeightGC
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (partitionGC_pos params β μ))

lemma gibbsWeightGC_pos
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    0 < gibbsWeightGC params β μ x := by
  unfold gibbsWeightGC
  exact div_pos (Real.exp_pos _) (partitionGC_pos params β μ)

lemma gibbsWeightGC_sum_one
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    ∑ x, gibbsWeightGC params β μ x = 1 := by
  unfold gibbsWeightGC partitionGC
  have hZne : (∑ y : α, Real.exp (-β * shiftedEnergy params μ y)) ≠ 0 :=
    ne_of_gt (partitionGC_pos params β μ)
  calc
    ∑ x : α, Real.exp (-β * shiftedEnergy params μ x) / ∑ y : α, Real.exp (-β * shiftedEnergy params μ y)
        = (∑ x : α, Real.exp (-β * shiftedEnergy params μ x)) / ∑ y : α, Real.exp (-β * shiftedEnergy params μ y) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset α))
                (f := fun x => Real.exp (-β * shiftedEnergy params μ x))
                (a := ∑ y : α, Real.exp (-β * shiftedEnergy params μ y)))
    _ = 1 := by exact div_self hZne

/-- Mean value of `E - μN` under the grand-canonical Gibbs state. -/
noncomputable def meanShift
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, gibbsWeightGC params β μ x * shiftedEnergy params μ x

/-- Mean particle number under the grand-canonical Gibbs state. -/
noncomputable def meanNumber
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, gibbsWeightGC params β μ x * params.number x

/-- Unnormalized first moment of `E - μN`. -/
noncomputable def firstShiftUnnormalized
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, shiftedEnergy params μ x * Real.exp (-β * shiftedEnergy params μ x)

/-- Unnormalized first moment of `N`. -/
noncomputable def firstNumberUnnormalized
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, params.number x * Real.exp (-β * shiftedEnergy params μ x)

-- Pointwise derivative in `β`.
omit [Fintype α] [Nonempty α] in
lemma hasDerivAt_exp_neg_mul_shiftedEnergy_beta
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    HasDerivAt
      (fun t : ℝ => Real.exp (-t * shiftedEnergy params μ x))
      (-(shiftedEnergy params μ x) * Real.exp (-β * shiftedEnergy params μ x))
      β := by
  have hlin : HasDerivAt (fun t : ℝ => -t * shiftedEnergy params μ x)
      (-(shiftedEnergy params μ x)) β := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id' β).const_mul (-(shiftedEnergy params μ x)))
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_exp (-β * shiftedEnergy params μ x)).comp β hlin

/-- Derivative kernel `∂β Z(β, μ)`. -/
noncomputable def partitionGCDerivBetaFun
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, -(shiftedEnergy params μ x) * Real.exp (-β * shiftedEnergy params μ x)

omit [Nonempty α] in
lemma partitionGCDerivBetaFun_eq_neg_firstShift
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    partitionGCDerivBetaFun params β μ = -firstShiftUnnormalized params β μ := by
  unfold partitionGCDerivBetaFun firstShiftUnnormalized
  simp [Finset.sum_neg_distrib]

omit [Nonempty α] in
lemma hasDerivAt_partitionGC_beta
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    HasDerivAt (fun t : ℝ => partitionGC params t μ) (partitionGCDerivBetaFun params β μ) β := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ x, Real.exp (-t * shiftedEnergy params μ x))
        (∑ x, -(shiftedEnergy params μ x) * Real.exp (-β * shiftedEnergy params μ x))
        β := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset α))
        (fun x _hx => hasDerivAt_exp_neg_mul_shiftedEnergy_beta params β μ x))
  unfold partitionGC partitionGCDerivBetaFun
  simpa [neg_mul] using hsum

lemma potentialGC_deriv_beta_eq_partitionDeriv_div_partition
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => potentialGC params t μ) β
      = partitionGCDerivBetaFun params β μ / partitionGC params β μ := by
  unfold potentialGC
  have hdiff : DifferentiableAt ℝ (fun t => partitionGC params t μ) β :=
    (hasDerivAt_partitionGC_beta params β μ).differentiableAt
  have hne : partitionGC params β μ ≠ 0 := ne_of_gt (partitionGC_pos params β μ)
  calc
    deriv (fun t => Real.log (partitionGC params t μ)) β
        = deriv (fun t => partitionGC params t μ) β / partitionGC params β μ := by
            simpa using (deriv.log (f := fun t => partitionGC params t μ) hdiff hne)
    _ = partitionGCDerivBetaFun params β μ / partitionGC params β μ := by
          rw [(hasDerivAt_partitionGC_beta params β μ).deriv]

lemma meanShift_eq_firstShift_div_partition
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    meanShift params β μ = firstShiftUnnormalized params β μ / partitionGC params β μ := by
  unfold meanShift firstShiftUnnormalized gibbsWeightGC
  have hZne : partitionGC params β μ ≠ 0 := ne_of_gt (partitionGC_pos params β μ)
  calc
    ∑ x, (Real.exp (-β * shiftedEnergy params μ x) / partitionGC params β μ) * shiftedEnergy params μ x
        = ∑ x, (shiftedEnergy params μ x * Real.exp (-β * shiftedEnergy params μ x)) / partitionGC params β μ := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            field_simp [hZne]
    _ = (∑ x, shiftedEnergy params μ x * Real.exp (-β * shiftedEnergy params μ x)) / partitionGC params β μ := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset α))
              (f := fun x => shiftedEnergy params μ x * Real.exp (-β * shiftedEnergy params μ x))
              (a := partitionGC params β μ))
    _ = firstShiftUnnormalized params β μ / partitionGC params β μ := by
          rfl

/-- Grand-canonical `β`-derivative: `∂β ψ = - E_{β,μ}[E - μN]`. -/
lemma potentialGC_deriv_beta_eq_neg_meanShift
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => potentialGC params t μ) β = -meanShift params β μ := by
  rw [potentialGC_deriv_beta_eq_partitionDeriv_div_partition]
  rw [partitionGCDerivBetaFun_eq_neg_firstShift, neg_div, meanShift_eq_firstShift_div_partition]

-- Pointwise derivative in `μ`.
omit [Fintype α] [Nonempty α] in
lemma hasDerivAt_exp_neg_mul_shiftedEnergy_mu
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    HasDerivAt
      (fun t : ℝ => Real.exp (-β * shiftedEnergy params t x))
      ((β * params.number x) * Real.exp (-β * shiftedEnergy params μ x))
      μ := by
  have hmul : HasDerivAt (fun t : ℝ => t * params.number x) (params.number x) μ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id' μ).mul_const (params.number x))
  have hshift : HasDerivAt (fun t : ℝ => shiftedEnergy params t x) (-(params.number x)) μ := by
    unfold shiftedEnergy
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hmul.const_sub (params.energy x)
  have hlin : HasDerivAt
      (fun t : ℝ => -β * shiftedEnergy params t x)
      (β * params.number x)
      μ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hshift.const_mul (-β))
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_exp (-β * shiftedEnergy params μ x)).comp μ hlin

/-- Derivative kernel `∂μ Z(β, μ)`. -/
noncomputable def partitionGCDerivMuFun
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  ∑ x, (β * params.number x) * Real.exp (-β * shiftedEnergy params μ x)

omit [Nonempty α] in
lemma partitionGCDerivMuFun_eq_beta_mul_firstNumber
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    partitionGCDerivMuFun params β μ = β * firstNumberUnnormalized params β μ := by
  unfold partitionGCDerivMuFun firstNumberUnnormalized
  calc
    ∑ x, (β * params.number x) * Real.exp (-β * shiftedEnergy params μ x)
        = ∑ x, β * (params.number x * Real.exp (-β * shiftedEnergy params μ x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
    _ = β * ∑ x, params.number x * Real.exp (-β * shiftedEnergy params μ x) := by
          symm
          simpa using
            (Finset.mul_sum
              (s := (Finset.univ : Finset α))
              (a := β)
              (f := fun x => params.number x * Real.exp (-β * shiftedEnergy params μ x)))

omit [Nonempty α] in
lemma hasDerivAt_partitionGC_mu
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    HasDerivAt (fun t : ℝ => partitionGC params β t) (partitionGCDerivMuFun params β μ) μ := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ x, Real.exp (-β * shiftedEnergy params t x))
        (∑ x, (β * params.number x) * Real.exp (-β * shiftedEnergy params μ x))
        μ := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset α))
        (fun x _hx => hasDerivAt_exp_neg_mul_shiftedEnergy_mu params β μ x))
  unfold partitionGC partitionGCDerivMuFun
  simpa using hsum

lemma potentialGC_deriv_mu_eq_partitionDeriv_div_partition
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => potentialGC params β t) μ
      = partitionGCDerivMuFun params β μ / partitionGC params β μ := by
  unfold potentialGC
  have hdiff : DifferentiableAt ℝ (fun t => partitionGC params β t) μ :=
    (hasDerivAt_partitionGC_mu params β μ).differentiableAt
  have hne : partitionGC params β μ ≠ 0 := ne_of_gt (partitionGC_pos params β μ)
  calc
    deriv (fun t => Real.log (partitionGC params β t)) μ
        = deriv (fun t => partitionGC params β t) μ / partitionGC params β μ := by
            simpa using (deriv.log (f := fun t => partitionGC params β t) hdiff hne)
    _ = partitionGCDerivMuFun params β μ / partitionGC params β μ := by
          rw [(hasDerivAt_partitionGC_mu params β μ).deriv]

lemma meanNumber_eq_firstNumber_div_partition
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    meanNumber params β μ = firstNumberUnnormalized params β μ / partitionGC params β μ := by
  unfold meanNumber firstNumberUnnormalized gibbsWeightGC
  have hZne : partitionGC params β μ ≠ 0 := ne_of_gt (partitionGC_pos params β μ)
  calc
    ∑ x, (Real.exp (-β * shiftedEnergy params μ x) / partitionGC params β μ) * params.number x
        = ∑ x, (params.number x * Real.exp (-β * shiftedEnergy params μ x)) / partitionGC params β μ := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            field_simp [hZne]
    _ = (∑ x, params.number x * Real.exp (-β * shiftedEnergy params μ x)) / partitionGC params β μ := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset α))
              (f := fun x => params.number x * Real.exp (-β * shiftedEnergy params μ x))
              (a := partitionGC params β μ))
    _ = firstNumberUnnormalized params β μ / partitionGC params β μ := by
          rfl

/-- Grand-canonical `μ`-derivative: `∂μ ψ = β E_{β,μ}[N]`. -/
lemma potentialGC_deriv_mu_eq_beta_meanNumber
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => potentialGC params β t) μ = β * meanNumber params β μ := by
  rw [potentialGC_deriv_mu_eq_partitionDeriv_div_partition]
  rw [partitionGCDerivMuFun_eq_beta_mul_firstNumber, meanNumber_eq_firstNumber_div_partition]
  simpa [mul_assoc] using
    (mul_div_assoc β (firstNumberUnnormalized params β μ) (partitionGC params β μ))

end FiniteGrandCanonicalModel

end InfoGeometry.GrandCanonical
