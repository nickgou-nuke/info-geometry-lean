import InfoGeometry.MaxEnt.Optimality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

/-!
# Jaynes Entropy Views (Finite Lean Layer)

This module packages finite, Mathlib-native pieces of Jaynes' rationale:

- Shannon entropy on finite simplices
- combinatorial multiplicity via multinomial coefficients
- linear-constraint feasible classes
- entropy concentration as a formal certificate interface
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

@[simp] lemma ShannonEntropy_eq_entropy (p : Fin n → ℝ) :
    ShannonEntropy (n := n) p = entropy (n := n) p 1 := rfl

@[simp] lemma mem_simplex_iff (p : Fin n → ℝ) :
    p ∈ Simplex n ↔ PointwiseNonneg p ∧ Normalized p := Iff.rfl

lemma normalized_of_mem_simplex {p : Fin n → ℝ} (hp : p ∈ Simplex n) :
    Normalized p :=
  hp.2

end EntropyBasics

section Multiplicity

variable {n : ℕ}

/-- Total number of trials encoded by counts. -/
noncomputable def totalCount (counts : Fin n → ℕ) : ℕ :=
  ∑ i, counts i

/-- Empirical frequency associated to a finite count profile. -/
noncomputable def empiricalFreq (counts : Fin n → ℕ) (i : Fin n) : ℝ :=
  (counts i : ℝ) / (totalCount counts : ℝ)

lemma empiricalFreq_nonneg (counts : Fin n → ℕ) (i : Fin n) :
    0 ≤ empiricalFreq counts i := by
  unfold empiricalFreq
  exact div_nonneg (by positivity) (by positivity)

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

lemma multiplicity_pos (counts : Fin n → ℕ) :
    0 < multiplicity counts := by
  simpa [multiplicity] using
    (Nat.multinomial_pos (s := (Finset.univ : Finset (Fin n))) (f := counts))

lemma multiplicity_spec (counts : Fin n → ℕ) :
    (∏ i, Nat.factorial (counts i)) * multiplicity counts
      = Nat.factorial (totalCount counts) := by
  simpa [multiplicity, totalCount] using
    (Nat.multinomial_spec (s := (Finset.univ : Finset (Fin n))) (f := counts))

lemma multiplicity_one_le (counts : Fin n → ℕ) :
    1 ≤ multiplicity counts :=
  Nat.succ_le_of_lt (multiplicity_pos counts)

/-- Log-multiplicity. -/
noncomputable def logMultiplicity (counts : Fin n → ℕ) : ℝ :=
  Real.log (multiplicity counts)

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

lemma thermodynamicPreference_pos
    (N : ℝ) (counts₁ counts₂ : Fin n → ℕ) :
    0 < thermodynamicPreference N counts₁ counts₂ := by
  unfold thermodynamicPreference
  exact Real.exp_pos _

/-- A formal witness for the asymptotic equipartition statement. -/
structure AsymptoticEquipartitionWitness (p : Fin n → ℝ) where
  countsSeq : ℕ → Fin n → ℕ
  total_pos : ∀ N, 0 < totalCount (countsSeq N)
  tendsToEntropy :
    Filter.Tendsto (fun N => normalizedLogMultiplicity (countsSeq N))
      Filter.atTop (nhds (ShannonEntropy p))

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

lemma goodFraction_nonneg
    (S : Finset (Fin n → ℝ))
    (Hstar eps : ℝ) :
    0 ≤ goodFraction S Hstar eps := by
  unfold goodFraction
  positivity

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

/-- Finite concentration certificate mirroring Jaynes-style concentration statements. -/
structure EntropyConcentrationCertificate
    (S : Finset (Fin n → ℝ))
    (Hstar eps eta : ℝ) where
  eps_nonneg : 0 ≤ eps
  eta_bounds : 0 ≤ eta ∧ eta ≤ 1
  nonempty : S.Nonempty
  lower_fraction_bound : eta ≤ goodFraction S Hstar eps

lemma entropyBand_of_mem_confidenceInterval
    {Hstar eps x : ℝ}
    (hx : x ∈ entropyConfidenceInterval Hstar eps) :
    |x - Hstar| ≤ eps := by
  rcases hx with ⟨hlo, hhi⟩
  have hleft : -eps ≤ x - Hstar := by linarith
  have hright : x - Hstar ≤ eps := by linarith
  exact abs_le.mpr ⟨hleft, hright⟩

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

lemma BurgModel.spectrum_nonneg
    {p : ℕ} (M : BurgModel p) (ω : ℝ) :
    0 ≤ M.spectrum ω :=
  arSpectralDensity_nonneg M.coeff M.noiseVar ω M.noiseVar_nonneg

end TimeSeries

end InfoGeometry.MaxEnt
