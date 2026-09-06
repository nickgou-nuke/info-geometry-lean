import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Basic
import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.ExponentialFamily.Finite

set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal
open Finset

namespace InfoGeometry

/-!
# Finite Exponential Family and Jaynes MaxEnt

Combined primitives for finite exponential families and MaxEnt.
-/

namespace MaxEnt

section Finite

variable {n : ℕ}

/-- Shannon entropy with scale factor `K`. -/
noncomputable def entropy (p : Fin n → ℝ) (K : ℝ) : ℝ :=
  -K * ∑ i, p i * Real.log (p i)

/-- Finite MaxEnt feasibility package with one moment constraint. -/
structure MaxEntProblem
    (f : Fin n → ℝ) (expectationVal : ℝ) where
  p : Fin n → ℝ
  norm : ∑ i, p i = 1
  expectation : ∑ i, p i * f i = expectationVal
  nonneg : ∀ i, 0 ≤ p i

/-- Jaynes partition function `Z(lam) = ∑ᵢ exp(-lam fᵢ)`. -/
noncomputable def partition (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, Real.exp (-lam * f i)

/-- Log-partition `log Z(lam)`. -/
noncomputable def logPartition (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  Real.log (partition f lam)

/-- Jaynes Gibbs form `pᵢ(lam) = exp(-lam fᵢ) / Z(lam)`. -/
noncomputable def gibbs (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) : ℝ :=
  Real.exp (-lam * f i) / partition f lam

/-- Gibbs expectation of the observable `f`. -/
noncomputable def gibbsExpectation (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, gibbs f lam i * f i

lemma partition_pos
    (f : Fin n → ℝ) (lam : ℝ) [Nonempty (Fin n)] :
    0 < partition f lam := by
  classical
  unfold partition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => Real.exp (-lam * f i))
      (by
        intro i _
        exact Real.exp_pos _)
      Finset.univ_nonempty)

lemma partition_ne_zero
    (f : Fin n → ℝ) (lam : ℝ) [Nonempty (Fin n)] :
    partition f lam ≠ 0 :=
  (partition_pos f lam).ne'

lemma gibbs_pos
    (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) [Nonempty (Fin n)] :
    0 < gibbs f lam i := by
  unfold gibbs
  exact div_pos (Real.exp_pos _) (partition_pos f lam)

lemma gibbs_nonneg
    (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) [Nonempty (Fin n)] :
    0 ≤ gibbs f lam i :=
  (gibbs_pos f lam i).le

lemma gibbs_sum_one
    (f : Fin n → ℝ) (lam : ℝ) [Nonempty (Fin n)] :
    ∑ i, gibbs f lam i = 1 := by
  unfold gibbs partition
  have hZne : (∑ j : Fin n, Real.exp (-lam * f j)) ≠ 0 := by
    exact (partition_pos f lam).ne'
  calc
    ∑ i : Fin n, Real.exp (-lam * f i) / ∑ j : Fin n, Real.exp (-lam * f j)
        = (∑ i : Fin n, Real.exp (-lam * f i)) / ∑ j : Fin n, Real.exp (-lam * f j) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => Real.exp (-lam * f i))
                (a := ∑ j : Fin n, Real.exp (-lam * f j)))
    _ = 1 := by
          exact div_self hZne

lemma gibbs_eq_exp_sub_logPartition
    (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) [Nonempty (Fin n)] :
    gibbs f lam i = Real.exp (-lam * f i - logPartition f lam) := by
  unfold gibbs logPartition
  have hZpos : 0 < partition f lam := partition_pos f lam
  calc
    Real.exp (-lam * f i) / partition f lam
        = Real.exp (-lam * f i) / Real.exp (Real.log (partition f lam)) := by
            rw [Real.exp_log hZpos]
    _ = Real.exp (-lam * f i - Real.log (partition f lam)) := by
          rw [Real.exp_sub]

noncomputable def gibbsMaxEntProblemOfExpectation
    (f : Fin n → ℝ) (lam expectationVal : ℝ)
    [Nonempty (Fin n)]
    (hE : gibbsExpectation f lam = expectationVal) :
    MaxEntProblem (n := n) f expectationVal where
  p := gibbs f lam
  norm := gibbs_sum_one f lam
  expectation := by
    simpa [gibbsExpectation] using hE
  nonneg := by
    intro i
    exact gibbs_nonneg f lam i

/--
Open MaxEnt closure target: existence of a Lagrange multiplier matching a
feasible one-dimensional moment.

This is kept as a proposition target, not a proved theorem.  The current file
does not provide the continuity/intermediate-value argument needed to promote
the statement from feasibility data to a native Lean proof.
-/
def exists_lam_of_feasible_expectation
    (f : Fin n → ℝ) (expectationVal : ℝ)
    [Nonempty (Fin n)]
    (_p_opt : Fin n → ℝ)
    (_hp_opt_pos : ∀ i, 0 < _p_opt i)
    (_hp_opt_norm : ∑ i, _p_opt i = 1)
    (_hp_opt_exp : ∑ i, _p_opt i * f i = expectationVal) : Prop :=
  ∃ lam : ℝ, gibbsExpectation f lam = expectationVal

end Finite

namespace Finite

noncomputable section

variable {α ι : Type*}
variable [Fintype α] [DecidableEq α]
variable [DecidableEq ι]

/-- Finite Jaynes problem data: prior + finite feature family + targets. -/
structure FiniteJaynesProblem (α ι : Type*) [Fintype α] [DecidableEq α] [DecidableEq ι] where
  prior : ProbabilityDist α
  index : Finset ι
  feature : ι → α → ℝ
  target : ι → ℝ

namespace FiniteJaynesProblem

def energy (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) : ℝ :=
  ∑ i ∈ J.index, lam i * J.feature i x

@[simp] lemma energy_zero (J : FiniteJaynesProblem α ι) (x : α) :
    J.energy (fun _ => 0) x = 0 := by
  simp [energy]

def partition (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) : ℝ :=
  ∑ x, (J.prior x).toReal * Real.exp (J.energy lam x)

lemma partition_nonneg (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) :
    0 ≤ J.partition lam := by
  unfold partition
  refine Finset.sum_nonneg ?_
  intro x _hx
  exact mul_nonneg (J.prior x).toReal_nonneg (le_of_lt (Real.exp_pos _))

def FullSupportPrior (J : FiniteJaynesProblem α ι) : Prop :=
  ∀ x, 0 < (J.prior x).toReal

lemma partition_pos_of_fullSupport
    (J : FiniteJaynesProblem α ι)
    [Nonempty α]
    (hprior : J.FullSupportPrior) (lam : ι → ℝ) :
    0 < J.partition lam := by
  unfold partition
  exact
    Finset.sum_pos
      (fun x _hx => mul_pos (hprior x) (Real.exp_pos _))
      Finset.univ_nonempty

lemma partition_ne_zero_of_fullSupport
    (J : FiniteJaynesProblem α ι)
    [Nonempty α]
    (hprior : J.FullSupportPrior) (lam : ι → ℝ) :
    J.partition lam ≠ 0 :=
  (J.partition_pos_of_fullSupport hprior lam).ne'

def gibbsWeight (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) : ℝ :=
  (J.prior x).toReal * Real.exp (J.energy lam x)

@[simp] lemma gibbsWeight_nonneg
    (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) :
    0 ≤ J.gibbsWeight lam x := by
  exact mul_nonneg (J.prior x).toReal_nonneg (le_of_lt (Real.exp_pos _))

def gibbsProb
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (_hZ : J.partition lam ≠ 0) (x : α) : ℝ :=
  J.gibbsWeight lam x / J.partition lam

lemma gibbsProb_nonneg
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) (x : α) :
    0 ≤ J.gibbsProb lam hZ x := by
  unfold gibbsProb
  have hZnonneg : 0 ≤ J.partition lam := J.partition_nonneg lam
  have hZpos : 0 < J.partition lam := lt_of_le_of_ne hZnonneg (Ne.symm hZ)
  exact div_nonneg (J.gibbsWeight_nonneg lam x) (le_of_lt hZpos)

lemma sum_gibbsProb_eq_one
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) :
    ∑ x, J.gibbsProb lam hZ x = 1 := by
  unfold gibbsProb
  rw [← Finset.sum_div]
  change J.partition lam / J.partition lam = 1
  exact div_self hZ

noncomputable def gibbsDist
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) : ProbabilityDist α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (J.gibbsProb lam hZ x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => J.gibbsProb_nonneg lam hZ x)]
    rw [J.sum_gibbsProb_eq_one lam hZ]
    exact ENNReal.ofReal_one
  )

lemma sum_toReal_eq_one (P : ProbabilityDist α) :
    ∑ x, (P x).toReal = 1 := by
  have h' : ∑ x, P x = (1 : ℝ≥0∞) := by
    simpa [tsum_fintype] using P.tsum_coe
  have h'' := congrArg ENNReal.toReal h'
  have h''' : (∑ x, P x).toReal = ∑ x, (P x).toReal := by
    rw [ENNReal.toReal_sum]
    intro a _ha
    exact (ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one P a) ENNReal.one_lt_top))
  rw [h'''] at h''
  simpa using h''

noncomputable def logPartition (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) : ℝ :=
  Real.log (J.partition lam)

lemma partition_zero (J : FiniteJaynesProblem α ι) :
    J.partition (fun _ => 0) = 1 := by
  unfold partition energy
  simpa using sum_toReal_eq_one J.prior

lemma logPartition_zero (J : FiniteJaynesProblem α ι) :
    J.logPartition (fun _ => 0) = 0 := by
  unfold logPartition
  rw [J.partition_zero]
  simp

def moment (_J : FiniteJaynesProblem α ι) (P : ProbabilityDist α) (f : α → ℝ) : ℝ :=
  ∑ x, (P x).toReal * f x

def SatisfiesTargetMoments
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) : Prop :=
  ∀ i ∈ J.index, J.moment (J.gibbsDist lam hZ) (J.feature i) = J.target i

/--
Open finite Jaynes closure target: existence of multipliers matching all target
moments.

This is deliberately a proposition target rather than a theorem; proving it
requires the missing finite-dimensional convex duality/existence argument.
-/
def exists_satisfiesTargetMoments
    (J : FiniteJaynesProblem α ι)
    [Nonempty α]
    (_hprior : J.FullSupportPrior)
    (_P_opt : ProbabilityDist α)
    (_h_P_opt_full : ∀ x, 0 < (_P_opt x).toReal)
    (_h_P_opt_moments : ∀ i ∈ J.index, J.moment _P_opt (J.feature i) = J.target i) : Prop :=
  ∃ (lam : ι → ℝ) (hZ : J.partition lam ≠ 0),
    J.SatisfiesTargetMoments lam hZ

lemma sum_prob_mul_energy
    (J : FiniteJaynesProblem α ι)
    (P : ProbabilityDist α)
    (lam : ι → ℝ) :
    ∑ x, (P x).toReal * J.energy lam x
      = ∑ i ∈ J.index, lam i * J.moment P (J.feature i) := by
  unfold FiniteJaynesProblem.energy FiniteJaynesProblem.moment
  calc
    ∑ x, (P x).toReal * ∑ i ∈ J.index, lam i * J.feature i x
        = ∑ x, ∑ i ∈ J.index, (P x).toReal * (lam i * J.feature i x) := by
            simp [Finset.mul_sum]
    _ = ∑ i ∈ J.index, ∑ x, (P x).toReal * (lam i * J.feature i x) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ J.index, lam i * ∑ x, (P x).toReal * J.feature i x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have h_mul : ∑ x, (P x).toReal * (lam i * J.feature i x) = ∑ x, lam i * ((P x).toReal * J.feature i x) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            ring
          rw [h_mul, ← Finset.mul_sum]
    _ = ∑ i ∈ J.index, lam i * J.moment P (J.feature i) := by
          rfl

noncomputable def dualObjective (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) : ℝ :=
  J.logPartition lam - ∑ i ∈ J.index, lam i * J.target i

noncomputable def gibbsMoment
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) (f : α → ℝ) : ℝ :=
  J.moment (J.gibbsDist lam hZ) f

lemma dualObjective_zero (J : FiniteJaynesProblem α ι) :
    J.dualObjective (fun _ => 0) = 0 := by
  unfold dualObjective
  rw [J.logPartition_zero]
  simp

lemma gibbsDist_pointwise
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) (x : α) :
    ((J.gibbsDist lam hZ) x).toReal = J.gibbsProb lam hZ x := by
  unfold gibbsDist
  have h_nonneg : ∀ x, 0 ≤ J.gibbsProb lam hZ x :=
    fun x => J.gibbsProb_nonneg lam hZ x
  simp [PMF.ofFintype, h_nonneg]

lemma gibbsMoment_eq_sum
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) (f : α → ℝ) :
    J.gibbsMoment lam hZ f = ∑ x, J.gibbsProb lam hZ x * f x := by
  unfold gibbsMoment moment
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [gibbsDist_pointwise]

lemma satisfiesTargetMoments_iff
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) :
    J.SatisfiesTargetMoments lam hZ ↔
      ∀ i ∈ J.index, ∑ x, J.gibbsProb lam hZ x * J.feature i x = J.target i := by
  unfold SatisfiesTargetMoments
  have h_eq : ∀ i, J.moment (J.gibbsDist lam hZ) (J.feature i) = ∑ x, J.gibbsProb lam hZ x * J.feature i x := by
    intro i
    exact J.gibbsMoment_eq_sum lam hZ (J.feature i)
  constructor <;> intro h i hi
  · have h_hi := h i hi
    rw [h_eq i] at h_hi
    exact h_hi
  · have h_hi := h i hi
    rw [← h_eq i] at h_hi
    exact h_hi

lemma gibbsProb_eq_prior_mul_exp_tilt
    (J : FiniteJaynesProblem α ι)
    (lam : ι → ℝ)
    (hZ : J.partition lam ≠ 0)
    (x : α) :
    J.gibbsProb lam hZ x
      = (J.prior x).toReal * Real.exp (J.energy lam x - J.logPartition lam) := by
  have hZnonneg : 0 ≤ J.partition lam := J.partition_nonneg lam
  have hZpos : 0 < J.partition lam := lt_of_le_of_ne hZnonneg (Ne.symm hZ)
  unfold gibbsProb gibbsWeight logPartition
  calc
    (J.prior x).toReal * Real.exp (J.energy lam x) / J.partition lam
        = (J.prior x).toReal * (Real.exp (J.energy lam x) / J.partition lam) := by ring
    _ = (J.prior x).toReal * (Real.exp (J.energy lam x) / Real.exp (Real.log (J.partition lam))) := by
          rw [Real.exp_log hZpos]
    _ = (J.prior x).toReal * Real.exp (J.energy lam x - Real.log (J.partition lam)) := by
          rw [Real.exp_sub]

lemma log_gibbsRatio_eq_energy_sub_logPartition
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    (lam : ι → ℝ)
    (hZ : J.partition lam ≠ 0)
    (x : α) :
    Real.log (J.gibbsProb lam hZ x / (J.prior x).toReal)
      = J.energy lam x - J.logPartition lam := by
  have hqx : (J.prior x).toReal ≠ 0 := (hprior x).ne'
  have hExp : Real.exp (J.energy lam x) ≠ 0 := (Real.exp_pos _).ne'
  have hratio :
      J.gibbsProb lam hZ x / (J.prior x).toReal
        = Real.exp (J.energy lam x) / J.partition lam := by
    unfold gibbsProb gibbsWeight
    field_simp [hqx, hZ]
  rw [hratio]
  have hZnonneg : 0 ≤ J.partition lam := J.partition_nonneg lam
  have hZpos : 0 < J.partition lam := lt_of_le_of_ne hZnonneg (Ne.symm hZ)
  rw [Real.log_div hExp hZpos.ne', Real.log_exp]
  rfl

private lemma mul_log_ratio_to_gibbs_eq
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (P : ProbabilityDist α) (x : α) :
    (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x)
      =
      (P x).toReal *
        (Real.log ((P x).toReal / (J.prior x).toReal)
          - (J.energy lam x - J.logPartition lam)) := by
  by_cases hPx : (P x).toReal = 0
  · simp [hPx]
  · have hqx : (J.prior x).toReal ≠ 0 := (hprior x).ne'
    have hgpos : 0 < J.gibbsProb lam hZ x := by
      rw [J.gibbsProb_eq_prior_mul_exp_tilt lam hZ x]
      exact mul_pos (hprior x) (Real.exp_pos _)
    have hgx : J.gibbsProb lam hZ x ≠ 0 := hgpos.ne'
    have hlog := J.log_gibbsRatio_eq_energy_sub_logPartition hprior lam hZ x
    rw [Real.log_div hgx hqx] at hlog
    have hmain :
        Real.log ((P x).toReal / J.gibbsProb lam hZ x)
          =
          Real.log ((P x).toReal / (J.prior x).toReal)
            - (J.energy lam x - J.logPartition lam) := by
      rw [Real.log_div hPx hgx, Real.log_div hPx hqx]
      linarith
    rw [hmain]

/-- Extracted sum rewriting lemma to break up kl_gibbs_variational_identity -/
lemma sum_mul_log_ratio_to_gibbs_eq
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (P : ProbabilityDist α) :
    (∑ x, (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x))
    = ∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal)
      - ∑ x, (P x).toReal * J.energy lam x
      + ∑ x, (P x).toReal * J.logPartition lam := by
  calc
    (∑ x, (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x))
      = ∑ x, (P x).toReal *
        (Real.log ((P x).toReal / (J.prior x).toReal)
          - (J.energy lam x - J.logPartition lam)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact mul_log_ratio_to_gibbs_eq J hprior lam hZ P x
    _ = ∑ x,
        ((P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal)
          - (P x).toReal * J.energy lam x
          + (P x).toReal * J.logPartition lam) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
    _ = (∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal))
        - (∑ x, (P x).toReal * J.energy lam x)
        + (∑ x, (P x).toReal * J.logPartition lam) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma kl_gibbs_variational_identity
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (P : ProbabilityDist α) :
    (∑ x, (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x))
      =
      (∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal))
        - (∑ i ∈ J.index, lam i * J.moment P (J.feature i))
        + J.logPartition lam := by
  rw [sum_mul_log_ratio_to_gibbs_eq J hprior lam hZ P]
  rw [J.sum_prob_mul_energy P lam]
  have hsum : ∑ x, (P x).toReal = 1 := sum_toReal_eq_one P
  rw [← Finset.sum_mul, hsum, one_mul]

lemma kl_prior_eq_kl_gibbs_add_dualObjective
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (P : ProbabilityDist α)
    (h_feasible : ∀ i ∈ J.index, J.moment P (J.feature i) = J.target i) :
    (∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal))
      =
      (∑ x, (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x))
        - J.dualObjective lam := by
  have hvar := J.kl_gibbs_variational_identity hprior lam hZ P
  have hmom :
      (∑ i ∈ J.index, lam i * J.moment P (J.feature i))
        =
      (∑ i ∈ J.index, lam i * J.target i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [h_feasible i hi]
  unfold FiniteJaynesProblem.dualObjective
  rw [hmom] at hvar
  linarith

lemma dual_objective_le_kl_prior
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (P : ProbabilityDist α)
    (h_feasible : ∀ i ∈ J.index, J.moment P (J.feature i) = J.target i)
    (hKL_nonneg : 0 ≤ ∑ x, (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x)) :
    - J.dualObjective lam ≤ ∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal) := by
  rw [J.kl_prior_eq_kl_gibbs_add_dualObjective hprior lam hZ P h_feasible]
  linarith

def ofLogLikelihood (prior : ProbabilityDist α) (ℓ : α → ℝ) :
    FiniteJaynesProblem α Unit where
  prior := prior
  index := {()}
  feature := fun _ => ℓ
  target := fun _ => 0

@[simp] lemma ofLogLikelihood_energy
    (prior : ProbabilityDist α) (ℓ : α → ℝ) (t : Unit → ℝ) (x : α) :
    (ofLogLikelihood (α := α) prior ℓ).energy t x = t () * ℓ x := by
  simp [ofLogLikelihood, energy]

end FiniteJaynesProblem
end
end Finite
end MaxEnt
end InfoGeometry
