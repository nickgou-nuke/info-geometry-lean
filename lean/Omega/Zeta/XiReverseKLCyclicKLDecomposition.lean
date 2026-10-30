import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Probability.FiniteGibbsVariational

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Orbit mass of a positive cyclic sample. -/
def xiOrbitMass {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, x j

/-- Orbit average of a positive cyclic sample. -/
def xiOrbitAverage {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  xiOrbitMass x / (n + 1 : ℝ)

/-- Orbit-averaged discrete weight. -/
def xiOrbitWeight {n : ℕ} (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  x j / xiOrbitMass x

/-- Uniform weight on the `n + 1` cyclic samples. -/
def xiUniformWeight (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

/-- The entropy-gap integrand written in orbit coordinates. -/
def xiReverseKLCyclicGap {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, xiUniformWeight n * (-Real.log (x j) + Real.log (xiOrbitAverage x))

/-- The discrete reverse-KL divergence from the uniform law to the orbit-averaged weights. -/
def xiReverseKLCyclicKL {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, xiUniformWeight n * Real.log (xiUniformWeight n / xiOrbitWeight x j)

private lemma xiOrbitMass_pos {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 < x j) :
    0 < xiOrbitMass x := by
  unfold xiOrbitMass
  have hle : x 0 ≤ ∑ j : Fin (n + 1), x j := by
    exact Finset.single_le_sum (fun j _ => le_of_lt (hx j)) (by simp)
  exact lt_of_lt_of_le (hx 0) hle

private lemma xiUniformWeight_pos (n : ℕ) (_j : Fin (n + 1)) :
    0 < xiUniformWeight n := by
  dsimp [xiUniformWeight]
  positivity

private lemma xiUniformWeight_sum (n : ℕ) :
    ∑ _j : Fin (n + 1), xiUniformWeight n = 1 := by
  have hcard : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  simp only [xiUniformWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [hcard.ne']

private lemma xiOrbitWeight_pos {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < x j) (j : Fin (n + 1)) :
    0 < xiOrbitWeight x j :=
  div_pos (hx j) (xiOrbitMass_pos x hx)

private lemma xiOrbitWeight_sum {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < x j) :
    ∑ j : Fin (n + 1), xiOrbitWeight x j = 1 := by
  have hmass : 0 < xiOrbitMass x := xiOrbitMass_pos x hx
  unfold xiOrbitWeight xiOrbitMass
  rw [← Finset.sum_div]
  exact div_self hmass.ne'

/-- Paper label: `thm:xi-reversekl-cyclic-kl-decomposition`. The entropy-gap integrand built from
the cyclic orbit average matches the reverse KL divergence from the uniform law to the explicit
orbit-averaged weights. -/
theorem paper_xi_reversekl_cyclic_kl_decomposition (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < x j) :
    xiReverseKLCyclicGap x = xiReverseKLCyclicKL x := by
  have hmass : 0 < xiOrbitMass x := xiOrbitMass_pos x hx
  have hcard : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have havg : 0 < xiOrbitAverage x := by
    exact div_pos hmass hcard
  unfold xiReverseKLCyclicGap xiReverseKLCyclicKL
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hxj : 0 < x j := hx j
  have hratio :
      xiUniformWeight n / xiOrbitWeight x j = xiOrbitAverage x / x j := by
    unfold xiUniformWeight xiOrbitWeight xiOrbitAverage xiOrbitMass
    field_simp [hmass.ne', hxj.ne']
  rw [hratio, Real.log_div havg.ne' hxj.ne']
  unfold xiUniformWeight
  ring

/-- The cyclic entropy gap is nonnegative for every strictly positive finite
profile. This general statement replaces conclusions inferred only from the
single four-site example. -/
theorem xiReverseKLCyclicKL_nonneg (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < x j) : 0 ≤ xiReverseKLCyclicKL x := by
  let p : Fin (n + 1) → ℝ := fun _ => xiUniformWeight n
  let q : Fin (n + 1) → ℝ := fun j => xiOrbitWeight x j
  have hp : ∀ j, 0 < p j := by
    intro j
    exact xiUniformWeight_pos n j
  have hq : ∀ j, 0 < q j := by
    intro j
    exact xiOrbitWeight_pos x hx j
  have hp_sum : ∑ j, p j = 1 := by simpa [p] using xiUniformWeight_sum n
  have hq_sum : ∑ j, q j = 1 := by simpa [q] using xiOrbitWeight_sum x hx
  have hkl := InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy_nonneg
    p q hp hq hp_sum hq_sum
  simpa [p, q, xiReverseKLCyclicKL,
    InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy] using hkl

/-- Equality in the cyclic reverse-KL gap holds precisely when the normalized
orbit weights are uniform. -/
theorem xiReverseKLCyclicKL_eq_zero_iff_uniform (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 < x j) :
    xiReverseKLCyclicKL x = 0 ↔
      ∀ j, xiOrbitWeight x j = xiUniformWeight n := by
  let p : Fin (n + 1) → ℝ := fun _ => xiUniformWeight n
  let q : Fin (n + 1) → ℝ := fun j => xiOrbitWeight x j
  have hp : ∀ j, 0 < p j := by
    intro j
    exact xiUniformWeight_pos n j
  have hq : ∀ j, 0 < q j := by
    intro j
    exact xiOrbitWeight_pos x hx j
  have hp_sum : ∑ j, p j = 1 := by simpa [p] using xiUniformWeight_sum n
  have hq_sum : ∑ j, q j = 1 := by simpa [q] using xiOrbitWeight_sum x hx
  have hzero := InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy_eq_zero_iff
    p q hp hq hp_sum hq_sum
  change InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy p q = 0 ↔
    ∀ j, q j = p j
  rw [hzero]
  constructor
  · intro h j
    exact (congrFun h j).symm
  · intro h
    funext j
    exact (h j).symm

/-- The cyclic reverse-KL gap vanishes exactly when the finite profile is
constant, expressed without a pairwise-equality side condition: each entry is
its orbit average. -/
theorem xiReverseKLCyclicKL_eq_zero_iff_profile_eq_average (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 < x j) :
    xiReverseKLCyclicKL x = 0 ↔ ∀ j, x j = xiOrbitAverage x := by
  have hmass : 0 < xiOrbitMass x := xiOrbitMass_pos x hx
  have hcard : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  rw [xiReverseKLCyclicKL_eq_zero_iff_uniform n x hx]
  constructor
  · intro h j
    have hratio : x j / xiOrbitMass x = 1 / (n + 1 : ℝ) := by
      simpa [xiOrbitWeight, xiUniformWeight] using h j
    dsimp [xiOrbitAverage]
    field_simp [hmass.ne', hcard.ne'] at hratio ⊢
    linarith
  · intro h j
    have hratio : x j / xiOrbitMass x = 1 / (n + 1 : ℝ) := by
      rw [h j]
      dsimp [xiOrbitAverage]
      field_simp [hmass.ne', hcard.ne']
    simpa [xiOrbitWeight, xiUniformWeight] using hratio

end

end Omega.Zeta
