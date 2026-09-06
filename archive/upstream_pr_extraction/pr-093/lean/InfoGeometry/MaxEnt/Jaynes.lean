import InfoGeometry.MaxEnt.Optimality
import Mathlib.Data.Nat.Choose.Multinomial
set_option linter.unnecessarySimpa false

open scoped BigOperators

/-!
# Jaynes Entropy Views (Finite Lean Layer)

This module packages finite, Mathlib-native pieces of Jaynes' rationale:

- Shannon entropy on finite simplices
- combinatorial multiplicity via multinomial coefficients
- linear-constraint feasible classes
- entropy concentration as a formal property interface
- Gibbs canonical form as MaxEnt optimizer
- time-series autocovariance and Burg-style AR spectral form
-/

namespace InfoGeometry.MaxEnt

section EntropyBasics

variable {n : ℕ}

/-- Normalization constraint `∑ pᵢ = 1`. -/
def Normalized (p : Fin n → ℝ) : Prop :=
  ∑ i, p i = 1

/-- Pointwise nonnegativity for finite probabilities. -/
def PointwiseNonneg (p : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ p i

/-- Finite probability simplex on `Fin n`. -/
def Simplex (n : ℕ) : Set (Fin n → ℝ) :=
  { p | PointwiseNonneg p ∧ Normalized p }

/-- Shannon entropy (`K = 1`) in the existing finite MaxEnt convention. -/
noncomputable def ShannonEntropy (p : Fin n → ℝ) : ℝ :=
  entropy (n := n) p 1

/-!
`xlogx` helper with the explicit Shannon convention at `0`.
This keeps later analytic statements independent of Lean's `Real.log 0 = 0` choice.
-/
/-- Conventioned entropy kernel: `x log x` for `x ≠ 0`, and `0` at `x = 0`. -/
noncomputable def xlogx (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log x

@[simp] lemma xlogx_zero : xlogx 0 = 0 := by
  simp [xlogx]

/-- The helper kernel agrees with `x * log x` away from case analysis. -/
lemma xlogx_eq_mul_log (x : ℝ) : xlogx x = x * Real.log x := by
  by_cases hx : x = 0
  · simp [xlogx, hx]
  · simp [xlogx, hx]

/-- Shannon entropy written through `xlogx`. -/
noncomputable def ShannonEntropyXlogx (p : Fin n → ℝ) : ℝ :=
  -∑ i, xlogx (p i)

/-- Shannon entropy agrees with the `xlogx` representation. -/
lemma ShannonEntropy_eq_xlogx (p : Fin n → ℝ) :
    ShannonEntropy (n := n) p = ShannonEntropyXlogx (n := n) p := by
  unfold ShannonEntropy ShannonEntropyXlogx entropy
  simp [xlogx_eq_mul_log]

@[simp] lemma ShannonEntropy_eq_entropy (p : Fin n → ℝ) :
    ShannonEntropy (n := n) p = entropy (n := n) p 1 := rfl

@[simp] lemma mem_simplex_iff (p : Fin n → ℝ) :
    p ∈ Simplex n ↔ PointwiseNonneg p ∧ Normalized p := Iff.rfl

/-- Membership in the simplex implies normalization. -/
lemma normalized_of_mem_simplex {p : Fin n → ℝ} (hp : p ∈ Simplex n) :
    Normalized p :=
  hp.2

end EntropyBasics

section PriorWeightedGibbs

variable {n : ℕ}

/-- Prior-weighted Jaynes partition function `Z_q(lam) = ∑ᵢ qᵢ exp(-lam fᵢ)`. -/
noncomputable def partitionWithPrior
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, (q i).toReal * Real.exp (-lam * f i)

/-- Prior-weighted Gibbs form `pᵢ(lam) = qᵢ exp(-lam fᵢ) / Z_q(lam)`. -/
noncomputable def gibbsWithPrior
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) : ℝ :=
  (q i).toReal * Real.exp (-lam * f i) / partitionWithPrior q f lam

/-- Prior-weighted Gibbs expectation of the observable `f`. -/
noncomputable def gibbsExpectationWithPrior
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, gibbsWithPrior q f lam i * f i

/-- The prior-weighted partition function is strictly positive. -/
lemma partitionWithPrior_pos
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) :
    0 < partitionWithPrior q f lam := by
  unfold partitionWithPrior
  have hnonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (q i).toReal * Real.exp (-lam * f i) := by
    intro i hi
    exact mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _))
  have hposWitness :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < (q i).toReal * Real.exp (-lam * f i) := by
    classical
    have hsum_ennreal :
        (Finset.univ.sum fun i : Fin n => q i) = (1 : ENNReal) := by
      simpa [tsum_fintype] using q.tsum_coe
    have hsum_toReal :
        (Finset.univ.sum fun i : Fin n => (q i).toReal) = 1 := by
      have htoReal :
          (Finset.univ.sum fun i : Fin n => (q i).toReal)
            = ENNReal.toReal (Finset.univ.sum fun i : Fin n => q i) := by
        simpa using
          (ENNReal.toReal_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun i => q i) (by
              intro i hi
              exact q.apply_ne_top i)).symm
      simpa [hsum_ennreal] using htoReal
    have hsum_ne_zero :
        (Finset.univ.sum fun i : Fin n => (q i).toReal) ≠ 0 := by
      simpa [hsum_toReal] using (one_ne_zero : (1 : ℝ) ≠ 0)
    rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne_zero with ⟨i, hi, hne⟩
    have hpos_q : 0 < (q i).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (by simpa [eq_comm] using hne)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos hpos_q (Real.exp_pos _)
  exact Finset.sum_pos' hnonneg hposWitness

/-- The prior-weighted partition function is nonzero. -/
lemma partitionWithPrior_ne_zero
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) :
    partitionWithPrior q f lam ≠ 0 :=
  (partitionWithPrior_pos q f lam).ne'

/-- Prior-weighted Gibbs probabilities are pointwise nonnegative. -/
lemma gibbsWithPrior_nonneg
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) :
    0 ≤ gibbsWithPrior q f lam i := by
  unfold gibbsWithPrior
  exact div_nonneg
    (mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _)))
    (le_of_lt (partitionWithPrior_pos q f lam))

/-- Prior-weighted Gibbs probabilities sum to one. -/
lemma gibbsWithPrior_sum_one
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) :
    ∑ i, gibbsWithPrior q f lam i = 1 := by
  unfold gibbsWithPrior partitionWithPrior
  have hZne : (∑ j : Fin n, (q j).toReal * Real.exp (-lam * f j)) ≠ 0 := by
    exact (partitionWithPrior_pos q f lam).ne'
  calc
    ∑ i : Fin n, (q i).toReal * Real.exp (-lam * f i) /
        ∑ j : Fin n, (q j).toReal * Real.exp (-lam * f j)
      = (∑ i : Fin n, (q i).toReal * Real.exp (-lam * f i)) /
          ∑ j : Fin n, (q j).toReal * Real.exp (-lam * f j) := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun i : Fin n => (q i).toReal * Real.exp (-lam * f i))
              (a := ∑ j : Fin n, (q j).toReal * Real.exp (-lam * f j)))
    _ = 1 := by
          exact div_self hZne

/-- Prior-weighted log-partition `log Z_q(lam)`. -/
noncomputable def logPartitionWithPrior
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  Real.log (partitionWithPrior q f lam)

/-- Prior-weighted Gibbs form as an exponential tilt with log-partition. -/
lemma gibbsWithPrior_eq_exp_sub_logPartition
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) :
    gibbsWithPrior q f lam i =
      (q i).toReal * Real.exp (-lam * f i - logPartitionWithPrior q f lam) := by
  unfold gibbsWithPrior logPartitionWithPrior
  have hZpos : 0 < partitionWithPrior q f lam := partitionWithPrior_pos q f lam
  calc
    (q i).toReal * Real.exp (-lam * f i) / partitionWithPrior q f lam
        = (q i).toReal * Real.exp (-lam * f i) /
            Real.exp (Real.log (partitionWithPrior q f lam)) := by
              rw [Real.exp_log hZpos]
    _ = (q i).toReal * (Real.exp (-lam * f i) /
            Real.exp (Real.log (partitionWithPrior q f lam))) := by
          rw [mul_div_assoc]
    _ = (q i).toReal * Real.exp (-lam * f i - Real.log (partitionWithPrior q f lam)) := by
          rw [Real.exp_sub]

/-- Prior-weighted Gibbs point packaged as a feasible MaxEnt point once moments match. -/
noncomputable def gibbsWithPriorMaxEntProblemOfExpectation
    (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam expectationVal : ℝ)
    (hE : gibbsExpectationWithPrior q f lam = expectationVal) :
    MaxEntProblem (n := n) f expectationVal where
  p := gibbsWithPrior q f lam
  norm := gibbsWithPrior_sum_one q f lam
  expectation := by
    simpa [gibbsExpectationWithPrior] using hE
  nonneg := by
    intro i
    exact gibbsWithPrior_nonneg q f lam i

end PriorWeightedGibbs

section Multiplicity

variable {n : ℕ}

/-- Total number of trials encoded by counts. -/
noncomputable def totalCount (counts : Fin n → ℕ) : ℕ :=
  ∑ i, counts i

/-- Empirical frequency associated to a finite count profile. -/
noncomputable def empiricalFreq (counts : Fin n → ℕ) (i : Fin n) : ℝ :=
  (counts i : ℝ) / (totalCount counts : ℝ)

/-- Empirical frequencies are pointwise nonnegative. -/
lemma empiricalFreq_nonneg (counts : Fin n → ℕ) (i : Fin n) :
    0 ≤ empiricalFreq counts i := by
  unfold empiricalFreq
  exact div_nonneg (by positivity) (by positivity)

/-- Empirical frequencies normalize to one when total count is nonzero. -/
lemma empiricalFreq_sum_one
    (counts : Fin n → ℕ)
    (hN : totalCount counts ≠ 0) :
    ∑ i, empiricalFreq counts i = 1 := by
  unfold empiricalFreq
  have hN' : (totalCount counts : ℝ) ≠ 0 := by
    exact_mod_cast hN
  calc
    ∑ i, (counts i : ℝ) / (totalCount counts : ℝ)
        = (∑ i, (counts i : ℝ)) / (totalCount counts : ℝ) := by
            symm
            simpa using
              (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
                (f := fun i => (counts i : ℝ))
                (a := (totalCount counts : ℝ)))
    _ = (totalCount counts : ℝ) / (totalCount counts : ℝ) := by
          simp [totalCount]
    _ = 1 := by
          field_simp [hN']

/-- Shannon entropy of the empirical frequencies induced by counts. -/
noncomputable def empiricalShannonEntropy (counts : Fin n → ℕ) : ℝ :=
  ShannonEntropy (n := n) (empiricalFreq counts)

/-- Jaynes multiplicity (number of sequences with fixed count profile). -/
noncomputable def multiplicity (counts : Fin n → ℕ) : ℕ :=
  Nat.multinomial Finset.univ counts

/-- Jaynes multiplicity is strictly positive. -/
lemma multiplicity_pos (counts : Fin n → ℕ) :
    0 < multiplicity counts := by
  simpa [multiplicity] using
    (Nat.multinomial_pos (s := (Finset.univ : Finset (Fin n))) (f := counts))

/-- Multinomial specification identity for Jaynes multiplicity. -/
lemma multiplicity_spec (counts : Fin n → ℕ) :
    (∏ i, Nat.factorial (counts i)) * multiplicity counts
      = Nat.factorial (totalCount counts) := by
  simpa [multiplicity, totalCount] using
    (Nat.multinomial_spec (s := (Finset.univ : Finset (Fin n))) (f := counts))

/-- Jaynes multiplicity is at least one. -/
lemma multiplicity_one_le (counts : Fin n → ℕ) :
    1 ≤ multiplicity counts :=
  Nat.succ_le_of_lt (multiplicity_pos counts)

/-- Log-multiplicity. -/
noncomputable def logMultiplicity (counts : Fin n → ℕ) : ℝ :=
  Real.log (multiplicity counts)

/-- Log-multiplicity is nonnegative. -/
lemma logMultiplicity_nonneg (counts : Fin n → ℕ) :
    0 ≤ logMultiplicity counts := by
  unfold logMultiplicity
  have h1 : (1 : ℝ) ≤ (multiplicity counts : ℝ) := by
    exact_mod_cast multiplicity_one_le counts
  exact Real.log_nonneg h1

/-- Normalized log-multiplicity `log W / N`, the AEP quantity. -/
noncomputable def normalizedLogMultiplicity (counts : Fin n → ℕ) : ℝ :=
  logMultiplicity counts / (totalCount counts : ℝ)

/-- Jaynes thermodynamic preference ratio at scale `N`.
Larger entropy/log-multiplicity is exponentially preferred. -/
noncomputable def thermodynamicPreference
    (N : ℝ) (counts₁ counts₂ : Fin n → ℕ) : ℝ :=
  Real.exp (N * (logMultiplicity counts₁ - logMultiplicity counts₂))

/-- Thermodynamic preference ratio is strictly positive. -/
lemma thermodynamicPreference_pos
    (N : ℝ) (counts₁ counts₂ : Fin n → ℕ) :
    0 < thermodynamicPreference N counts₁ counts₂ := by
  unfold thermodynamicPreference
  exact Real.exp_pos _

end Multiplicity

section LinearConstraints

variable {m n : ℕ}

/-- Finite linear constraints `A p = b`. -/
def SatisfiesLinearConstraints
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (p : Fin n → ℝ) : Prop :=
  ∀ j, ∑ i, A j i * p i = b j

/-- Feasible class = simplex intersected with linear constraints. -/
def FeasibleClass
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  { p | p ∈ Simplex n ∧ SatisfiesLinearConstraints A b p }

@[simp] lemma mem_feasibleClass_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (p : Fin n → ℝ) :
    p ∈ FeasibleClass A b ↔
      p ∈ Simplex n ∧ SatisfiesLinearConstraints A b p := Iff.rfl

/-- Membership in a feasible class implies normalization. -/
lemma normalized_of_mem_feasibleClass
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {p : Fin n → ℝ}
    (hp : p ∈ FeasibleClass A b) :
    Normalized p :=
  hp.1.2

/-- Dimension heuristic `n - m` for `m` independent affine constraints on `n` variables. -/
def expectedAffineDimension (m n : ℕ) : ℕ :=
  n - m

end LinearConstraints

section Concentration

variable {n : ℕ}

/-- Entropy band `|H(p) - H*| ≤ ε`. -/
def EntropyBand (Hstar eps : ℝ) (p : Fin n → ℝ) : Prop :=
  |ShannonEntropy p - Hstar| ≤ eps

/-- Profiles in a finite class whose entropy lies in the specified band. -/
noncomputable def goodProfiles
    (S : Finset (Fin n → ℝ))
    (Hstar eps : ℝ) : Finset (Fin n → ℝ) :=
  by
    classical
    exact S.filter (fun p => EntropyBand Hstar eps p)

/-- Fraction of profiles in a finite class falling inside the entropy band. -/
noncomputable def goodFraction
    (S : Finset (Fin n → ℝ))
    (Hstar eps : ℝ) : ℝ :=
  ((goodProfiles S Hstar eps).card : ℝ) / (S.card : ℝ)

/-- The good-profile fraction is nonnegative. -/
lemma goodFraction_nonneg
    (S : Finset (Fin n → ℝ))
    (Hstar eps : ℝ) :
    0 ≤ goodFraction S Hstar eps := by
  unfold goodFraction
  positivity

/-- The good-profile fraction is at most one on nonempty finite classes. -/
lemma goodFraction_le_one
    (S : Finset (Fin n → ℝ))
    (Hstar eps : ℝ)
    (hS : S.Nonempty) :
    goodFraction S Hstar eps ≤ 1 := by
  unfold goodFraction
  have hcard :
      (goodProfiles S Hstar eps).card ≤ S.card :=
    by
      classical
      simpa [goodProfiles] using
        (Finset.card_filter_le
          (s := S) (p := fun p : Fin n → ℝ => EntropyBand Hstar eps p))
  have hcard' :
      ((goodProfiles S Hstar eps).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hS)
  have hdiv :
      ((goodProfiles S Hstar eps).card : ℝ) / (S.card : ℝ)
        ≤ (S.card : ℝ) / (S.card : ℝ) := by
    exact div_le_div_of_nonneg_right hcard' (le_of_lt hSpos)
  have hS0 : (S.card : ℝ) ≠ 0 := by
    exact ne_of_gt hSpos
  calc
    ((goodProfiles S Hstar eps).card : ℝ) / (S.card : ℝ)
        ≤ (S.card : ℝ) / (S.card : ℝ) := hdiv
    _ = 1 := by field_simp [hS0]

/-- Symmetric confidence interval centered at `H*` with half-width `ε`. -/
def entropyConfidenceInterval (Hstar eps : ℝ) : Set ℝ :=
  Set.Icc (Hstar - eps) (Hstar + eps)



/-- Membership in the entropy confidence interval implies entropy-band control. -/
lemma entropyBand_of_mem_confidenceInterval
    {Hstar eps x : ℝ}
    (hx : x ∈ entropyConfidenceInterval Hstar eps) :
    |x - Hstar| ≤ eps := by
  rcases hx with ⟨hlo, hhi⟩
  have hleft : -eps ≤ x - Hstar := by linarith
  have hright : x - Hstar ≤ eps := by linarith
  exact abs_le.mpr ⟨hleft, hright⟩

/-- Entropy-band control implies membership in the confidence interval. -/
lemma mem_confidenceInterval_of_entropyBand
    {Hstar eps x : ℝ}
    (hx : |x - Hstar| ≤ eps) :
    x ∈ entropyConfidenceInterval Hstar eps := by
  rcases abs_le.mp hx with ⟨hleft, hright⟩
  constructor <;> linarith

end Concentration

section GibbsCanonical

variable {n : ℕ} [Nonempty (Fin n)]

/-- Jaynes canonical form solves finite MaxEnt under one moment constraint. -/
theorem gibbs_maximizes_shannon_under_moment
    (f : Fin n → ℝ) (E lam : ℝ)
    (p : Fin n → ℝ)
    (hp : p ∈ MaxEntConstraint (n := n) f E)
    (h_dist : ∀ i, p i = gibbs f lam i) :
    ∀ q, q ∈ MaxEntConstraint (n := n) f E →
      ShannonEntropy q ≤ ShannonEntropy p := by
  simpa [ShannonEntropy] using
    (max_ent_lagrange_multiplier_gibbs
      (n := n) (f := f) (E := E) (lam := lam)
      (p := p) hp h_dist)

/-- Canonical finite Jaynes problem:
simplex + linear constraints + one distinguished moment observable. -/
structure CanonicalProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  obs : Fin n → ℝ
  expected : ℝ

namespace CanonicalProblem

variable {m n : ℕ} [Nonempty (Fin n)]

/-- Feasible set for a canonical Jaynes problem. -/
def feasible (P : CanonicalProblem m n) : Set (Fin n → ℝ) :=
  { p |
      p ∈ FeasibleClass P.A P.b ∧
      ∑ i, p i * P.obs i = P.expected }

/-- Gibbs candidate associated to a Lagrange multiplier. -/
noncomputable def gibbsCandidate (P : CanonicalProblem m n) (lam : ℝ) : Fin n → ℝ :=
  gibbs P.obs lam

/-- A Gibbs candidate is feasible once linear and moment constraints are supplied. -/
lemma gibbsCandidate_mem_feasible
    (P : CanonicalProblem m n) (lam : ℝ)
    (hlin : SatisfiesLinearConstraints P.A P.b (P.gibbsCandidate lam))
    (hE : gibbsExpectation P.obs lam = P.expected) :
    P.gibbsCandidate lam ∈ P.feasible := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, hlin⟩
    refine ⟨?_, ?_⟩
    · intro i
      simpa [gibbsCandidate] using gibbs_nonneg (f := P.obs) (lam := lam) i
    · simpa [gibbsCandidate] using gibbs_sum_one (f := P.obs) (lam := lam)
  · simpa [gibbsCandidate] using hE

/-- Canonicalized Gibbs optimality:
on any additional linear-feasible class, entropy is maximized by the Gibbs candidate
for the moment constraint. -/
theorem gibbsCandidate_maximizes_entropy_on_feasible
    (P : CanonicalProblem m n) (lam : ℝ)
    (hE : gibbsExpectation P.obs lam = P.expected) :
    ∀ q, q ∈ P.feasible →
      ShannonEntropy q ≤ ShannonEntropy (P.gibbsCandidate lam) := by
  have hpMoment :
      P.gibbsCandidate lam ∈ MaxEntConstraint (n := n) P.obs P.expected := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        simpa [gibbsCandidate] using gibbs_nonneg (f := P.obs) (lam := lam) i
      · simpa [gibbsCandidate] using gibbs_sum_one (f := P.obs) (lam := lam)
    · simpa [gibbsCandidate] using hE
  have hopt :=
    gibbs_maximizes_shannon_under_moment
      (f := P.obs) (E := P.expected) (lam := lam)
      (p := P.gibbsCandidate lam) hpMoment (by intro i; rfl)
  intro q hq
  have hqMoment : q ∈ MaxEntConstraint (n := n) P.obs P.expected := by
    exact ⟨hq.1.1, hq.2⟩
  exact hopt q hqMoment

end CanonicalProblem

end GibbsCanonical

section TimeSeries

/-- Finite-sample mean for a real time series. -/
noncomputable def sampleMean (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.sum (Finset.range N) (fun t => x t)) / (N : ℝ)

/-- Empirical autocovariance at lag `k` (periodic indexing modulo `N`). -/
noncomputable def empiricalAutocovariance (x : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (Finset.sum (Finset.range N)
      (fun t => (x t - sampleMean x N) * (x ((t + k) % N) - sampleMean x N))) / (N : ℝ)

/-- Constraint vector of autocovariances up to order `p - 1`. -/
noncomputable def autocovarianceData (x : ℕ → ℝ) (N p : ℕ) : Fin p → ℝ :=
  fun k => empiricalAutocovariance x N k.1

/-- Burg-style AR spectral density for coefficients `a` and noise variance `σ²`. -/
noncomputable def arSpectralDensity
    {p : ℕ} (a : Fin p → ℝ) (σ2 ω : ℝ) : ℝ :=
  σ2 /
    ((1 - ∑ k, a k * Real.cos (((k.1 : ℝ) + 1) * ω)) ^ (2 : ℕ)
      + (∑ k, a k * Real.sin (((k.1 : ℝ) + 1) * ω)) ^ (2 : ℕ))

/-- Burg AR spectral density is nonnegative for nonnegative noise variance. -/
lemma arSpectralDensity_nonneg
    {p : ℕ} (a : Fin p → ℝ) (σ2 ω : ℝ)
    (hσ2 : 0 ≤ σ2) :
    0 ≤ arSpectralDensity a σ2 ω := by
  unfold arSpectralDensity
  refine div_nonneg hσ2 ?_
  nlinarith [pow_two_nonneg (1 - ∑ k, a k * Real.cos (((k.1 : ℝ) + 1) * ω)),
    pow_two_nonneg (∑ k, a k * Real.sin (((k.1 : ℝ) + 1) * ω))]

/-- Packaged Burg model data. -/
structure BurgModel (p : ℕ) where
  coeff : Fin p → ℝ
  noiseVar : ℝ
  noiseVar_nonneg : 0 ≤ noiseVar

/-- Burg model spectral density. -/
noncomputable def BurgModel.spectrum
    {p : ℕ} (M : BurgModel p) (ω : ℝ) : ℝ :=
  arSpectralDensity M.coeff M.noiseVar ω

/-- A Burg model has nonnegative spectrum at every frequency. -/
lemma BurgModel.spectrum_nonneg
    {p : ℕ} (M : BurgModel p) (ω : ℝ) :
    0 ≤ M.spectrum ω :=
  arSpectralDensity_nonneg M.coeff M.noiseVar ω M.noiseVar_nonneg

end TimeSeries

end InfoGeometry.MaxEnt
