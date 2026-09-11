import InfoGeometry.MaxEnt.Finite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KL.Finite
import InfoGeometry.PositiveMeasure

open scoped BigOperators

/-!
# Finite MaxEnt Optimality

A finite-dimensional Jaynes-style optimality theorem:
if a candidate distribution has Gibbs form and matches the moment constraint,
then it maximizes Shannon entropy on the constrained simplex.
-/

namespace InfoGeometry.MaxEnt

section FiniteOptimization

variable {n : ℕ} [Nonempty (Fin n)]

/-- The finite probability simplex on `Fin n`. -/
def ProbabilitySimplex (n : ℕ) : Set (Fin n → ℝ) :=
  { p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 }

/-- MaxEnt constraint set: simplex + one moment equality. -/
def MaxEntConstraint (f : Fin n → ℝ) (E : ℝ) : Set (Fin n → ℝ) :=
  { p | p ∈ ProbabilitySimplex n ∧ ∑ i, p i * f i = E }

/-- Build a `ProbabilityDist` from a point in the simplex. -/
noncomputable def probDistOfSimplex
    (p : Fin n → ℝ) (hp : p ∈ ProbabilitySimplex n) :
    InfoGeometry.FinProb (Fin n) := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ p i := by
    intro i hi
    exact hp.1 i
  have hsum : ∑ i, ENNReal.ofReal (p i) = 1 := by
    calc
      ∑ i, ENNReal.ofReal (p i)
          = ENNReal.ofReal (∑ i, p i) := by
              simpa using
                (ENNReal.ofReal_sum_of_nonneg
                  (s := (Finset.univ : Finset (Fin n)))
                  (f := fun i => p i)
                  hnonneg).symm
      _ = ENNReal.ofReal 1 := by simp [hp.2]
      _ = 1 := by simp
  exact InfoGeometry.FinProb.of_fintype (fun i => ENNReal.ofReal (p i)) hsum

/-- Gibbs distribution packaged as a `ProbabilityDist`. -/
noncomputable def gibbsDist (f : Fin n → ℝ) (lam : ℝ) :
    InfoGeometry.FinProb (Fin n) := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ gibbs f lam i := by
    intro i hi
    exact gibbs_nonneg f lam i
  have hsum : ∑ i, ENNReal.ofReal (gibbs f lam i) = 1 := by
    calc
      ∑ i, ENNReal.ofReal (gibbs f lam i)
          = ENNReal.ofReal (∑ i, gibbs f lam i) := by
              simpa using
                (ENNReal.ofReal_sum_of_nonneg
                  (s := (Finset.univ : Finset (Fin n)))
                  (f := fun i => gibbs f lam i)
                  hnonneg).symm
      _ = ENNReal.ofReal 1 := by simp [gibbs_sum_one f lam]
      _ = 1 := by simp
  exact InfoGeometry.FinProb.of_fintype (fun i => ENNReal.ofReal (gibbs f lam i)) hsum

/-- Cross-entropy to Gibbs equals `funE + log Z` on the constraint set. -/
lemma crossEntropyToGibbs_eq
    (f : Fin n → ℝ) (E lam : ℝ)
    {q : Fin n → ℝ}
    (hq : q ∈ MaxEntConstraint (n := n) f E) :
    -∑ i, q i * Real.log (gibbs f lam i) = lam * E + logPartition f lam := by
  rcases hq with ⟨⟨_, hq_norm⟩, hqE⟩
  have hsum :
      ∑ i, q i * (-lam * f i - logPartition f lam)
        = ((-lam) * (∑ i, q i * f i)) + ((-logPartition f lam) * (∑ i, q i)) := by
    calc
      ∑ i, q i * (-lam * f i - logPartition f lam)
          = ∑ i, (q i * (-lam * f i) + q i * (-logPartition f lam)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i, q i * (-lam * f i)) + (∑ i, q i * (-logPartition f lam)) := by
            rw [Finset.sum_add_distrib]
      _ = ((-lam) * (∑ i, q i * f i)) + ((-logPartition f lam) * (∑ i, q i)) := by
            congr
            · calc
                ∑ i, q i * (-lam * f i) = ∑ i, (-lam) * (q i * f i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  ring
                _ = (-lam) * (∑ i, q i * f i) := by
                  simpa using
                    (Finset.mul_sum (s := Finset.univ) (a := -lam) (f := fun i => q i * f i)).symm
            · calc
                ∑ i, q i * (-logPartition f lam)
                    = ∑ i, (-logPartition f lam) * q i := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        ring
                _ = (-logPartition f lam) * (∑ i, q i) := by
                      simpa using
                        (Finset.mul_sum (s := Finset.univ)
                          (a := -logPartition f lam) (f := fun i => q i)).symm
  calc
    -∑ i, q i * Real.log (gibbs f lam i)
        = -∑ i, q i * (-lam * f i - logPartition f lam) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [gibbs_eq_exp_sub_logPartition (f := f) (lam := lam) (i := i)]
            simp
    _ = -(((-lam) * (∑ i, q i * f i)) + ((-logPartition f lam) * (∑ i, q i))) := by
          rw [hsum]
    _ = lam * E + logPartition f lam := by
          rw [hqE, hq_norm]
          ring

/-- Entropy of the Gibbs law under matched moments equals `funE + log Z`. -/
lemma entropy_gibbs_eq
    (f : Fin n → ℝ) (E lam : ℝ)
    (hE : gibbsExpectation f lam = E) :
    entropy (gibbs f lam) 1 = lam * E + logPartition f lam := by
  have hg_mem : gibbs f lam ∈ MaxEntConstraint (n := n) f E := by
    refine ⟨?_, ?_⟩
    · exact ⟨(fun i => gibbs_nonneg f lam i), gibbs_sum_one f lam⟩
    · simpa [gibbsExpectation] using hE
  have hcross := crossEntropyToGibbs_eq (n := n) (f := f) (E := E) (lam := lam) hg_mem
  simpa [entropy] using hcross

/-- MaxEnt optimality using Gibbs form and moment matching. -/
theorem max_ent_lagrange_multiplier_gibbs
    (f : Fin n → ℝ) (E lam : ℝ)
    (p : Fin n → ℝ)
    (hp : p ∈ MaxEntConstraint (n := n) f E)
    (h_dist : ∀ i, p i = gibbs f lam i) :
    ∀ q, q ∈ MaxEntConstraint (n := n) f E → entropy q 1 ≤ entropy p 1 := by
  intro q hq
  have hterm :
      ∀ i,
        -(q i * Real.log (q i))
          ≤ -(q i * Real.log (gibbs f lam i)) - q i + gibbs f lam i := by
    intro i
    by_cases hqi : q i = 0
    · have hgi : 0 ≤ gibbs f lam i := gibbs_nonneg f lam i
      simp [hqi]
      linarith
    · have hqi_pos : 0 < q i := lt_of_le_of_ne (hq.1.1 i) (Ne.symm hqi)
      have hgi_pos : 0 < gibbs f lam i := gibbs_pos f lam i
      have hdiv :
          Real.log (q i / gibbs f lam i)
            = Real.log (q i) - Real.log (gibbs f lam i) :=
        Real.log_div hqi hgi_pos.ne'
      have hgkl :
          0 ≤ q i * Real.log (q i / gibbs f lam i) - q i + gibbs f lam i :=
        PositiveMeasure.gklTerm_nonneg (x := q i) (y := gibbs f lam i) hqi_pos hgi_pos
      rw [hdiv] at hgkl
      linarith
  have hsum :
      ∑ i, -(q i * Real.log (q i))
        ≤ ∑ i, (-(q i * Real.log (gibbs f lam i)) - q i + gibbs f lam i) := by
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hq_le_cross :
      entropy q 1 ≤ -∑ i, q i * Real.log (gibbs f lam i) := by
    have hqsum : ∑ i, q i = 1 := hq.1.2
    have hgsum : ∑ i, gibbs f lam i = 1 := gibbs_sum_one f lam
    have hq_form : entropy q 1 = ∑ i, -(q i * Real.log (q i)) := by
      simp [entropy]
    have hcross_form :
        ∑ i, (-(q i * Real.log (gibbs f lam i)) - q i + gibbs f lam i)
          = (-∑ i, q i * Real.log (gibbs f lam i)) - (∑ i, q i) + (∑ i, gibbs f lam i) := by
      calc
        ∑ i, (-(q i * Real.log (gibbs f lam i)) - q i + gibbs f lam i)
            = ∑ i, (-(q i * Real.log (gibbs f lam i)) + (-q i) + gibbs f lam i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, -(q i * Real.log (gibbs f lam i))) + (∑ i, -q i) + (∑ i, gibbs f lam i) := by
              simp [Finset.sum_add_distrib, add_left_comm, add_comm]
        _ = (-∑ i, q i * Real.log (gibbs f lam i)) - (∑ i, q i) + (∑ i, gibbs f lam i) := by
              simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hsum' :
        entropy q 1
          ≤ (-∑ i, q i * Real.log (gibbs f lam i)) - (∑ i, q i) + (∑ i, gibbs f lam i) := by
      simpa [hq_form, hcross_form] using hsum
    linarith
  have hp_eq_gibbs : p = gibbs f lam := by
    funext i
    exact h_dist i
  have hE : gibbsExpectation f lam = E := by
    simpa [gibbsExpectation, hp_eq_gibbs] using hp.2
  have hp_entropy : entropy p 1 = lam * E + logPartition f lam := by
    simpa [hp_eq_gibbs] using entropy_gibbs_eq (n := n) (f := f) (E := E) (lam := lam) hE
  calc
    entropy q 1 ≤ -∑ i, q i * Real.log (gibbs f lam i) := hq_le_cross
    _ = lam * E + logPartition f lam :=
      crossEntropyToGibbs_eq (n := n) (f := f) (E := E) (lam := lam) hq
    _ = entropy p 1 := hp_entropy.symm

/-- MaxEnt optimality in explicit Boltzmann form `exp(-lam fᵢ)/Z`. -/
theorem max_ent_lagrange_multiplier
    (f : Fin n → ℝ) (E lam : ℝ)
    (p : Fin n → ℝ)
    (hp : p ∈ MaxEntConstraint (n := n) f E)
    (Z : ℝ) (hZ : Z = partition f lam)
    (h_dist : ∀ i, p i = Real.exp (-lam * f i) / Z) :
    ∀ q, q ∈ MaxEntConstraint (n := n) f E → entropy q 1 ≤ entropy p 1 := by
  apply max_ent_lagrange_multiplier_gibbs (n := n) (f := f) (E := E) (lam := lam) (p := p) hp
  intro i
  rw [h_dist i, hZ, gibbs]

end FiniteOptimization

end InfoGeometry.MaxEnt
