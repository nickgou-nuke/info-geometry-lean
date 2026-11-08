import InfoGeometry.Prequantum.JaynesKLPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Probability.FiniteGibbsDeformationReadout
import InfoGeometry.PositiveMeasure

noncomputable section

namespace InfoGeometry.Probability.FiniteGibbsVariational

open scoped BigOperators
open InfoGeometry.Prequantum.JaynesKLPotential
open InfoGeometry.Probability.FiniteDeformationEntropyReadout
open InfoGeometry.Probability.FiniteGibbsDeformationReadout

variable {X : Type*}

/-- Real-valued KL divergence of two strictly positive finite weights. -/
def finiteRelativeEntropy
    [Fintype X]
    (p q : X → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- Shannon entropy of a strictly positive finite weight. -/
def finiteEntropy
    [Fintype X]
    (p : X → ℝ) : ℝ :=
  ∑ x, p x * (-Real.log (p x))

/-- Mean of an energy function under a finite weight. -/
def finiteMeanEnergy
    [Fintype X]
    (p energy : X → ℝ) : ℝ :=
  ∑ x, p x * energy x

/-- Free energy of a finite weight at inverse temperature `β`. -/
def finiteFreeEnergy
    [Fintype X]
    (p energy : X → ℝ)
    (β : ℝ) : ℝ :=
  finiteMeanEnergy p energy - β⁻¹ * finiteEntropy p

/--
For normalized positive weights, ordinary KL is the sum of the scalar
generalized-KL potentials.
-/
theorem finiteRelativeEntropy_eq_sum_scalarKLDivergence
    [Fintype X]
    (p q : X → ℝ)
    (hp_sum : ∑ x, p x = 1)
    (hq_sum : ∑ x, q x = 1) :
    finiteRelativeEntropy p q =
      ∑ x, scalarKLDivergence (p x) (q x) := by
  unfold finiteRelativeEntropy scalarKLDivergence
  have hcancel : (∑ x, (p x - q x)) = 0 := by
    rw [Finset.sum_sub_distrib, hp_sum, hq_sum]
    ring
  calc
    (∑ x, p x * Real.log (p x / q x)) =
        (∑ x,
          ((p x * Real.log (p x / q x) - p x + q x) +
            (p x - q x))) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ =
        (∑ x, (p x * Real.log (p x / q x) - p x + q x)) +
          ∑ x, (p x - q x) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ x, (p x * Real.log (p x / q x) - p x + q x) := by
      rw [hcancel, add_zero]

/-- Gibbs inequality for strictly positive normalized finite weights. -/
theorem finiteRelativeEntropy_nonneg
    [Fintype X]
    (p q : X → ℝ)
    (hp : ∀ x, 0 < p x)
    (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1)
    (hq_sum : ∑ x, q x = 1) :
    0 ≤ finiteRelativeEntropy p q := by
  rw [finiteRelativeEntropy_eq_sum_scalarKLDivergence p q hp_sum hq_sum]
  exact Finset.sum_nonneg fun x _ =>
    scalarKLDivergence_nonneg (p x) (q x) (hp x) (hq x)

/-- The scalar generalized-KL potential vanishes exactly on the diagonal. -/
theorem scalarKLDivergence_eq_zero_iff
    (x y : ℝ)
    (hx : 0 < x)
    (hy : 0 < y) :
    scalarKLDivergence x y = 0 ↔ x = y := by
  simpa [scalarKLDivergence, InfoGeometry.PositiveMeasure.gklTerm] using
    (InfoGeometry.PositiveMeasure.gklTerm_eq_zero_iff x y hx hy)

/-- Strict equality case of finite Gibbs inequality. -/
theorem finiteRelativeEntropy_eq_zero_iff
    [Fintype X]
    (p q : X → ℝ)
    (hp : ∀ x, 0 < p x)
    (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1)
    (hq_sum : ∑ x, q x = 1) :
    finiteRelativeEntropy p q = 0 ↔ p = q := by
  rw [finiteRelativeEntropy_eq_sum_scalarKLDivergence
    p q hp_sum hq_sum]
  constructor
  · intro hsum
    have hterms :
        ∀ x, scalarKLDivergence (p x) (q x) = 0 := by
      have hzero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset X))
          (f := fun x => scalarKLDivergence (p x) (q x))
          (by
            intro x _
            exact scalarKLDivergence_nonneg
              (p x) (q x) (hp x) (hq x))).1 hsum
      intro x
      exact hzero x (Finset.mem_univ x)
    funext x
    exact (scalarKLDivergence_eq_zero_iff
      (p x) (q x) (hp x) (hq x)).1 (hterms x)
  · rintro rfl
    exact Finset.sum_eq_zero fun x _ =>
      scalarKLDivergence_self_zero (p x) (hp x)

/-- Pointwise logarithmic ratio of a positive weight to a Gibbs law. -/
theorem log_ratio_gibbsDistribution
    [Fintype X]
    [Nonempty X]
    (p energy : X → ℝ)
    (β : ℝ)
    (hp : ∀ x, 0 < p x)
    (x : X) :
    Real.log (p x / gibbsDistribution energy β x) =
      Real.log (p x) + β * energy x +
        Real.log (gibbsPartition energy β) := by
  have hg : 0 < gibbsDistribution energy β x := by
    unfold gibbsDistribution normalizedDistribution
    exact div_pos
      (gibbsWeight_pos energy β x)
      (gibbsPartition_pos energy β)
  rw [Real.log_div (hp x).ne' hg.ne']
  have hs := gibbs_normalizedSurprisal energy β x
  linarith

/-- KL divergence to a Gibbs law expanded into entropy, energy, and `log Z`. -/
theorem finiteRelativeEntropy_gibbs_eq
    [Fintype X]
    [Nonempty X]
    (p energy : X → ℝ)
    (β : ℝ)
    (hp : ∀ x, 0 < p x)
    (hp_sum : ∑ x, p x = 1) :
    finiteRelativeEntropy p (gibbsDistribution energy β) =
      -finiteEntropy p +
        β * finiteMeanEnergy p energy +
          Real.log (gibbsPartition energy β) := by
  unfold finiteRelativeEntropy finiteEntropy finiteMeanEnergy
  simp_rw [log_ratio_gibbsDistribution p energy β hp]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hp_sum, one_mul]
  have hentropy :
      (∑ x, p x * Real.log (p x)) =
        -(∑ x, p x * (-Real.log (p x))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have henergy :
      (∑ x, p x * (β * energy x)) =
        β * ∑ x, p x * energy x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hentropy, henergy]

/-- Exact finite Gibbs variational identity for an arbitrary positive law. -/
theorem finite_gibbs_variational_identity
    [Fintype X]
    [Nonempty X]
    (p energy : X → ℝ)
    (β : ℝ)
    (hβ : β ≠ 0)
    (hp : ∀ x, 0 < p x)
    (hp_sum : ∑ x, p x = 1) :
    finiteRelativeEntropy p (gibbsDistribution energy β) =
      β *
        (finiteFreeEnergy p energy β -
          gibbsFreeEnergy energy β) := by
  rw [finiteRelativeEntropy_gibbs_eq p energy β hp hp_sum]
  rw [gibbsFreeEnergy_eq_neg_logPartition energy β hβ]
  unfold finiteFreeEnergy
  field_simp [hβ]
  ring

/-- The finite Gibbs law minimizes free energy among positive normalized laws. -/
theorem gibbsFreeEnergy_le
    [Fintype X]
    [Nonempty X]
    (p energy : X → ℝ)
    (β : ℝ)
    (hβ : 0 < β)
    (hp : ∀ x, 0 < p x)
    (hp_sum : ∑ x, p x = 1) :
    gibbsFreeEnergy energy β ≤ finiteFreeEnergy p energy β := by
  have hγ_pos : ∀ x, 0 < gibbsDistribution energy β x := by
    intro x
    unfold gibbsDistribution normalizedDistribution
    exact div_pos
      (gibbsWeight_pos energy β x)
      (gibbsPartition_pos energy β)
  have hKL :
      0 ≤ finiteRelativeEntropy p (gibbsDistribution energy β) :=
    finiteRelativeEntropy_nonneg
      p (gibbsDistribution energy β)
      hp hγ_pos hp_sum (sum_gibbsDistribution energy β)
  rw [finite_gibbs_variational_identity
    p energy β hβ.ne' hp hp_sum] at hKL
  have hdiff :
      0 ≤ finiteFreeEnergy p energy β -
        gibbsFreeEnergy energy β := by
    nlinarith
  exact sub_nonneg.mp hdiff

/-- KL divergence to a Gibbs law vanishes exactly at the Gibbs law. -/
theorem finiteRelativeEntropy_gibbs_eq_zero_iff
    [Fintype X]
    [Nonempty X]
    (p energy : X → ℝ)
    (β : ℝ)
    (hp : ∀ x, 0 < p x)
    (hp_sum : ∑ x, p x = 1) :
    finiteRelativeEntropy p (gibbsDistribution energy β) = 0 ↔
      p = gibbsDistribution energy β := by
  have hγ_pos : ∀ x, 0 < gibbsDistribution energy β x := by
    intro x
    unfold gibbsDistribution normalizedDistribution
    exact div_pos
      (gibbsWeight_pos energy β x)
      (gibbsPartition_pos energy β)
  exact finiteRelativeEntropy_eq_zero_iff
    p (gibbsDistribution energy β)
    hp hγ_pos hp_sum (sum_gibbsDistribution energy β)

/-- The Gibbs law is the unique positive normalized free-energy minimizer. -/
theorem finiteFreeEnergy_eq_gibbsFreeEnergy_iff
    [Fintype X]
    [Nonempty X]
    (p energy : X → ℝ)
    (β : ℝ)
    (hβ : 0 < β)
    (hp : ∀ x, 0 < p x)
    (hp_sum : ∑ x, p x = 1) :
    finiteFreeEnergy p energy β = gibbsFreeEnergy energy β ↔
      p = gibbsDistribution energy β := by
  constructor
  · intro hfree
    have hvar := finite_gibbs_variational_identity
      p energy β hβ.ne' hp hp_sum
    have hKL :
        finiteRelativeEntropy p (gibbsDistribution energy β) = 0 := by
      rw [hvar, hfree, sub_self, mul_zero]
    exact (finiteRelativeEntropy_gibbs_eq_zero_iff
      p energy β hp hp_sum).1 hKL
  · rintro rfl
    rfl

end InfoGeometry.Probability.FiniteGibbsVariational
