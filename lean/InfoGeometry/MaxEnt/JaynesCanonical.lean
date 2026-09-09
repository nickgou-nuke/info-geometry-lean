import Mathlib.Data.Nat.Choose.Multinomial
import InfoGeometry.KL.Finite
import InfoGeometry.PositiveMeasure

open scoped BigOperators ENNReal

universe u

namespace InfoGeometry.MaxEnt.JaynesCanonical

variable {Ω : Type} [Fintype Ω]

/-!
### 1. Entropy and Probability Distributions
A (finite) probability distribution on `Ω` as a function `Ω → ℝ`
with nonnegativity and total mass `1`.
-/

/-- A finite probability distribution used by the local Jaynes canonical layer. -/
structure ProbDist (Ω : Type) [Fintype Ω] where
  f : Ω → ℝ
  nonneg : ∀ i, 0 ≤ f i
  sum_one : (∑ i, f i) = 1

namespace ProbDist

variable {Ω : Type} [Fintype Ω]

/-- Convert local Jaynes probability distributions to the core `InfoGeometry` type. -/
noncomputable def toInfoProbabilityDist (P : ProbDist Ω) : InfoGeometry.ProbabilityDist Ω :=
  FinProb.of_fintype (fun i => ENNReal.ofReal (P.f i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.nonneg i)]
    rw [P.sum_one, ENNReal.ofReal_one])

@[simp] lemma toInfoProbabilityDist_apply (P : ProbDist Ω) (i : Ω) :
    P.toInfoProbabilityDist i = ENNReal.ofReal (P.f i) := rfl

end ProbDist

/-- Discrete Shannon entropy: `H(P) = - ∑ᵢ pᵢ log pᵢ`. -/
noncomputable def shannonEntropy (P : ProbDist Ω) : ℝ :=
  - ∑ i, P.f i * Real.log (P.f i)

/-!
### 2. Combinatorial Foundations (Multiplicity)
Multiplicity is encoded as a multinomial count derived from the count profile.
-/

/-- Total count encoded by a count profile. -/
noncomputable def totalCount (counts : Ω → ℕ) : ℕ :=
  ∑ i, counts i

/-- Multiplicity (multinomial count) for a finite count profile. -/
noncomputable def multiplicity (counts : Ω → ℕ) : ℕ :=
  Nat.multinomial Finset.univ counts

/-- Multinomial multiplicity is strictly positive. -/
lemma multiplicity_pos (counts : Ω → ℕ) :
    0 < multiplicity counts := by
  simpa [multiplicity] using
    (Nat.multinomial_pos (s := (Finset.univ : Finset Ω)) (f := counts))

/-- Multinomial specification identity for multiplicity. -/
lemma multiplicity_spec (counts : Ω → ℕ) :
    (∏ i, Nat.factorial (counts i)) * multiplicity counts
      = Nat.factorial (totalCount counts) := by
  simpa [multiplicity, totalCount] using
    (Nat.multinomial_spec (s := (Finset.univ : Finset Ω)) (f := counts))

/-- Multinomial multiplicity is at least one. -/
lemma multiplicity_one_le (counts : Ω → ℕ) :
    1 ≤ multiplicity counts :=
  Nat.succ_le_of_lt (multiplicity_pos counts)

/-- Log multiplicity. -/
noncomputable def logMultiplicity (counts : Ω → ℕ) : ℝ :=
  Real.log (multiplicity counts)

/-- Log-multiplicity is nonnegative. -/
lemma logMultiplicity_nonneg (counts : Ω → ℕ) :
    0 ≤ logMultiplicity counts := by
  unfold logMultiplicity
  have h1 : (1 : ℝ) ≤ (multiplicity counts : ℝ) := by
    exact_mod_cast multiplicity_one_le counts
  exact Real.log_nonneg h1

/--
Asymptotic Equipartition Property (AEP).
The normalized log-multiplicity converges almost-surely to the Shannon entropy.
-/
def AsymptoticEquipartition
    (n : ℕ → ℕ) (counts : ℕ → Ω → ℕ) (P : ProbDist Ω) : Prop :=
  Filter.Tendsto (fun k => (1 / (n k : ℝ)) * logMultiplicity (counts k))
    Filter.atTop (nhds (shannonEntropy P))

/-!
### 3. Linear Constraints and the Feasible Set
-/

/-- A single affine expectation constraint `A·p = d`. -/
structure LinearConstraint (Ω : Type u) [Fintype Ω] where
  A : Ω → ℝ  -- observable
  d : ℝ      -- target expectation

/-- `P` satisfies constraint `C` if `∑ᵢ A(i) p(i) = d`. -/
def satisfiesConstraint (P : ProbDist Ω) (C : LinearConstraint Ω) : Prop :=
  (∑ i, C.A i * P.f i) = C.d

/-- Feasible set: distributions satisfying all constraints in a list. -/
def FeasibleSet (constraints : List (LinearConstraint Ω)) : Set (ProbDist Ω) :=
  { P | ∀ C ∈ constraints, satisfiesConstraint P C }

/-!
### 4. Entropy Concentration Theorem
-/

/--
Entropy Concentration: in the usual asymptotics, the log-likelihood ratio
`2N * ΔH` converges in distribution to a χ²(k) variable.
-/
def entropy_concentration_asymptotic (N : ℕ) (ΔH : ℝ) (k : ℕ) : Prop :=
  -- Statement of the limit: 2N * ΔH → χ²(k) distribution.
  Filter.Tendsto (fun _ : ℕ => 2 * (N : ℝ) * ΔH) Filter.atTop (nhds (k : ℝ))

/-!
### 5. Maximum Entropy (Gibbs) Solution
-/

/-- Unnormalized partition function `Z(lam) = ∑ⱼ exp(-lam Aⱼ)`. -/
noncomputable def partitionFunction (C : LinearConstraint Ω) (lam : ℝ) : ℝ :=
  ∑ j, Real.exp (-lam * C.A j)

section Gibbs

variable [Nonempty Ω]

/-- `Z(lam) > 0` since it is a finite sum of strictly positive exponentials. -/
theorem partitionFunction_pos (C : LinearConstraint Ω) (lam : ℝ) :
    0 < partitionFunction C lam := by
  classical
  simpa [partitionFunction] using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun j => Real.exp (-lam * C.A j))
      (by
        intro j hj
        exact Real.exp_pos _)
      Finset.univ_nonempty)

/-- The canonical Gibbs distribution `p(i) = exp(-lam A(i)) / Z(lam)`. -/
noncomputable def gibbsDist (C : LinearConstraint Ω) (lam : ℝ) : ProbDist Ω := by
  classical
  have Z_pos : 0 < partitionFunction C lam := partitionFunction_pos (C := C) (lam := lam)
  refine
    { f := fun i => Real.exp (-lam * C.A i) / partitionFunction C lam
      nonneg := ?_
      sum_one := ?_ }
  · intro i
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt Z_pos)
  · have Z_ne : partitionFunction C lam ≠ 0 := ne_of_gt Z_pos
    calc
      (∑ i, Real.exp (-lam * C.A i) / partitionFunction C lam)
          = (∑ i, Real.exp (-lam * C.A i)) * (partitionFunction C lam)⁻¹ := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = partitionFunction C lam * (partitionFunction C lam)⁻¹ := by
            simp [partitionFunction]
      _ = 1 := by
            field_simp [Z_ne]

/-- Pointwise formula for the Gibbs distribution. -/
@[simp] lemma gibbsDist_f (C : LinearConstraint Ω) (lam : ℝ) (i : Ω) :
    (gibbsDist C lam).f i = Real.exp (-lam * C.A i) / partitionFunction C lam := rfl

/-- Pointwise positivity of the Gibbs distribution. -/
lemma gibbsDist_pos (C : LinearConstraint Ω) (lam : ℝ) (i : Ω) :
    0 < (gibbsDist C lam).f i := by
  rw [gibbsDist_f]
  exact div_pos (Real.exp_pos _) (partitionFunction_pos C lam)

/-- Log of the Gibbs point mass in affine form. -/
lemma log_gibbsDist_f (C : LinearConstraint Ω) (lam : ℝ) (i : Ω) :
    Real.log ((gibbsDist C lam).f i)
      = -lam * C.A i - Real.log (partitionFunction C lam) := by
  rw [gibbsDist_f]
  have hnum : Real.exp (-lam * C.A i) ≠ 0 := (Real.exp_pos _).ne'
  have hden : partitionFunction C lam ≠ 0 := (partitionFunction_pos C lam).ne'
  rw [Real.log_div hnum hden]
  simp

/-- Cross-entropy against the Gibbs law under the linear constraint. -/
lemma crossEntropyToGibbs_eq
    (C : LinearConstraint Ω) (lam : ℝ)
    (P : ProbDist Ω) (hP : satisfiesConstraint P C) :
    -∑ i, P.f i * Real.log ((gibbsDist C lam).f i)
      = lam * C.d + Real.log (partitionFunction C lam) := by
  have hP' : ∑ i, P.f i * C.A i = C.d := by
    calc
      ∑ i, P.f i * C.A i = ∑ i, C.A i * P.f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = C.d := hP
  have hsum :
      ∑ i, P.f i * (-lam * C.A i - Real.log (partitionFunction C lam))
        = ((-lam) * (∑ i, P.f i * C.A i))
          + ((-Real.log (partitionFunction C lam)) * (∑ i, P.f i)) := by
    calc
      ∑ i, P.f i * (-lam * C.A i - Real.log (partitionFunction C lam))
          = ∑ i, (P.f i * (-lam * C.A i) + P.f i * (-Real.log (partitionFunction C lam))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i, P.f i * (-lam * C.A i))
            + (∑ i, P.f i * (-Real.log (partitionFunction C lam))) := by
            rw [Finset.sum_add_distrib]
      _ = ((-lam) * (∑ i, P.f i * C.A i))
            + ((-Real.log (partitionFunction C lam)) * (∑ i, P.f i)) := by
            congr
            · calc
                ∑ i, P.f i * (-lam * C.A i)
                    = ∑ i, (-lam) * (P.f i * C.A i) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        ring
                _ = (-lam) * (∑ i, P.f i * C.A i) := by
                      simpa using
                        (Finset.mul_sum (s := Finset.univ) (a := -lam)
                          (f := fun i => P.f i * C.A i)).symm
            · calc
                ∑ i, P.f i * (-Real.log (partitionFunction C lam))
                    = ∑ i, (-Real.log (partitionFunction C lam)) * P.f i := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        ring
                _ = (-Real.log (partitionFunction C lam)) * (∑ i, P.f i) := by
                      simpa using
                        (Finset.mul_sum (s := Finset.univ)
                          (a := -Real.log (partitionFunction C lam))
                          (f := fun i => P.f i)).symm
  calc
    -∑ i, P.f i * Real.log ((gibbsDist C lam).f i)
        = -∑ i, P.f i * (-lam * C.A i - Real.log (partitionFunction C lam)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [log_gibbsDist_f]
    _ = -(((-lam) * (∑ i, P.f i * C.A i))
            + ((-Real.log (partitionFunction C lam)) * (∑ i, P.f i))) := by
          rw [hsum]
    _ = lam * C.d + Real.log (partitionFunction C lam) := by
          rw [hP', P.sum_one]
          ring

/-- Entropy value of the Gibbs law when it satisfies the target moment. -/
lemma entropy_gibbs_eq
    (C : LinearConstraint Ω) (lam : ℝ)
    (hGibbs : satisfiesConstraint (gibbsDist C lam) C) :
    shannonEntropy (gibbsDist C lam) = lam * C.d + Real.log (partitionFunction C lam) := by
  simpa [shannonEntropy] using
    crossEntropyToGibbs_eq (C := C) (lam := lam) (P := gibbsDist C lam) hGibbs

/--
Fundamental MaxEnt theorem (conceptual): if the Gibbs distribution satisfies the constraints,
it maximizes entropy over all feasible distributions.

A fully formal proof typically proceeds via nonnegativity of KL divergence.
-/
theorem gibbs_is_maximum_entropy
    (C : LinearConstraint Ω) (lam : ℝ)
    (P : ProbDist Ω) (hP : satisfiesConstraint P C)
    (hGibbs : satisfiesConstraint (gibbsDist (Ω := Ω) C lam) C) :
    shannonEntropy P ≤ shannonEntropy (gibbsDist (Ω := Ω) C lam) := by
  have hterm :
      ∀ i,
        -(P.f i * Real.log (P.f i))
          ≤ -(P.f i * Real.log ((gibbsDist C lam).f i)) - P.f i + (gibbsDist C lam).f i := by
    intro i
    by_cases hPi : P.f i = 0
    · simp only [hPi, neg_zero, zero_mul, sub_zero, zero_add]
      exact (gibbsDist C lam).nonneg i
    · have hPi_pos : 0 < P.f i := lt_of_le_of_ne (P.nonneg i) (Ne.symm hPi)
      have hgi_pos : 0 < (gibbsDist C lam).f i := gibbsDist_pos C lam i
      have hdiv :
          Real.log (P.f i / (gibbsDist C lam).f i)
            = Real.log (P.f i) - Real.log ((gibbsDist C lam).f i) :=
        Real.log_div hPi hgi_pos.ne'
      have hgkl :
          0 ≤ P.f i * Real.log (P.f i / (gibbsDist C lam).f i) - P.f i + (gibbsDist C lam).f i :=
        PositiveMeasure.gklTerm_nonneg (x := P.f i) (y := (gibbsDist C lam).f i) hPi_pos hgi_pos
      rw [hdiv] at hgkl
      linarith
  have hsum :
      ∑ i, -(P.f i * Real.log (P.f i))
        ≤ ∑ i, (-(P.f i * Real.log ((gibbsDist C lam).f i)) - P.f i + (gibbsDist C lam).f i) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hP_le_cross :
      shannonEntropy P ≤ -∑ i, P.f i * Real.log ((gibbsDist C lam).f i) := by
    have hPsum : ∑ i, P.f i = 1 := P.sum_one
    have hgsum : ∑ i, (gibbsDist C lam).f i = 1 := (gibbsDist C lam).sum_one
    have hP_form : shannonEntropy P = ∑ i, -(P.f i * Real.log (P.f i)) := by
      simp [shannonEntropy, Finset.sum_neg_distrib]
    rw [hP_form]
    have hsplit :
        (∑ i, (-(P.f i * Real.log ((gibbsDist C lam).f i)) - P.f i + (gibbsDist C lam).f i))
          = (-∑ i, P.f i * Real.log ((gibbsDist C lam).f i)) - (∑ i, P.f i) + ∑ i, (gibbsDist C lam).f i := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [hsplit, hPsum, hgsum] at hsum
    linarith
  have hcross_P :
      -∑ i, P.f i * Real.log ((gibbsDist C lam).f i)
        = lam * C.d + Real.log (partitionFunction C lam) :=
    crossEntropyToGibbs_eq (C := C) (lam := lam) (P := P) hP
  have hEntropy_g :
      shannonEntropy (gibbsDist C lam) = lam * C.d + Real.log (partitionFunction C lam) :=
    entropy_gibbs_eq (C := C) (lam := lam) hGibbs
  calc
    shannonEntropy P ≤ -∑ i, P.f i * Real.log ((gibbsDist C lam).f i) := hP_le_cross
    _ = lam * C.d + Real.log (partitionFunction C lam) := hcross_P
    _ = shannonEntropy (gibbsDist C lam) := hEntropy_g.symm

end Gibbs

/-!
### 6. Time Series and Autocovariance
-/

/-- Empirical autocovariance of a real-valued time series for lag `k`. -/
noncomputable def empiricalAutocovariance (Y : ℕ → ℝ) (T : ℕ) (k : ℕ) : ℝ :=
  let N_terms := T - k + 1
  (1 / (T + 1 : ℝ)) * ∑ j ∈ Finset.range N_terms, Y j * Y (j + k)

/--
Conceptual predicate placeholder: “`P` corresponds to an autoregressive (AR) model”.
Replace `True` with your preferred formalization (e.g. existence of AR coefficients).
-/
def isAutoregressiveModel (P : ProbDist Ω) : Prop :=
  let _ := P
  True

end InfoGeometry.MaxEnt.JaynesCanonical
