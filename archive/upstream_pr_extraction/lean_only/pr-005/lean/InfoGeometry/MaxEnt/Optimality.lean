import InfoGeometry.MaxEnt.Finite
import InfoGeometry.KL.Finite

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
    InfoGeometry.ProbabilityDist (Fin n) where
  prob := p
  sum_one := hp.2
  nonneg := hp.1

/-- Gibbs distribution packaged as a `ProbabilityDist`. -/
noncomputable def gibbsDist (f : Fin n → ℝ) (lam : ℝ) :
    InfoGeometry.ProbabilityDist (Fin n) where
  prob := gibbs f lam
  sum_one := gibbs_sum_one f lam
  nonneg := fun i => gibbs_nonneg f lam i

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
  have hKLnonneg :
      0 ≤ InfoGeometry.klDiv
        (probDistOfSimplex (n := n) q hq.1)
        (gibbsDist (n := n) f lam) := by
    apply InfoGeometry.KL.klDiv_nonneg_of_fullSupport
    intro i
    show 0 < (gibbsDist (n := n) f lam).prob i
    simpa [gibbsDist] using gibbs_pos (f := f) (lam := lam) i
  have hKLexpand :
      InfoGeometry.klDiv
        (probDistOfSimplex (n := n) q hq.1)
        (gibbsDist (n := n) f lam)
        = ∑ i, q i * (Real.log (q i) - Real.log (gibbs f lam i)) := by
    unfold InfoGeometry.klDiv InfoGeometry.expectation InfoGeometry.logDensity
    simp [probDistOfSimplex, gibbsDist]
  have hkl :
      0 ≤ (∑ i, q i * Real.log (q i)) - (∑ i, q i * Real.log (gibbs f lam i)) := by
    have htmp := hKLnonneg
    rw [hKLexpand] at htmp
    have hsum :
        ∑ i, q i * (Real.log (q i) - Real.log (gibbs f lam i))
          = (∑ i, q i * Real.log (q i)) - (∑ i, q i * Real.log (gibbs f lam i)) := by
      calc
        ∑ i, q i * (Real.log (q i) - Real.log (gibbs f lam i))
            = ∑ i, (q i * Real.log (q i) - q i * Real.log (gibbs f lam i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, q i * Real.log (q i)) - (∑ i, q i * Real.log (gibbs f lam i)) := by
              rw [Finset.sum_sub_distrib]
    exact hsum ▸ htmp
  have hq_le_cross :
      entropy q 1 ≤ -∑ i, q i * Real.log (gibbs f lam i) := by
    have hq_form : entropy q 1 = -∑ i, q i * Real.log (q i) := by
      simp [entropy]
    linarith [hkl, hq_form]
  have hE_gibbs : gibbsExpectation f lam = E := by
    have hpE : ∑ i, p i * f i = E := hp.2
    unfold gibbsExpectation
    calc
      ∑ i, gibbs f lam i * f i = ∑ i, p i * f i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [← h_dist i]
      _ = E := hpE
  have hcross_q :
      -∑ i, q i * Real.log (gibbs f lam i) = lam * E + logPartition f lam :=
    crossEntropyToGibbs_eq (n := n) (f := f) (E := E) (lam := lam) hq
  have hEntropy_g :
      entropy (gibbs f lam) 1 = lam * E + logPartition f lam :=
    entropy_gibbs_eq (n := n) (f := f) (E := E) (lam := lam) hE_gibbs
  have hq_le_gibbs : entropy q 1 ≤ entropy (gibbs f lam) 1 := by
    calc
      entropy q 1 ≤ -∑ i, q i * Real.log (gibbs f lam i) := hq_le_cross
      _ = lam * E + logPartition f lam := hcross_q
      _ = entropy (gibbs f lam) 1 := hEntropy_g.symm
  have hp_eq_gibbs : entropy p 1 = entropy (gibbs f lam) 1 := by
    unfold entropy
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [h_dist i]
  calc
    entropy q 1 ≤ entropy (gibbs f lam) 1 := hq_le_gibbs
    _ = entropy p 1 := hp_eq_gibbs.symm

/-- MaxEnt optimality in explicit Boltzmann form `exp(-λ fᵢ)/Z`. -/
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
