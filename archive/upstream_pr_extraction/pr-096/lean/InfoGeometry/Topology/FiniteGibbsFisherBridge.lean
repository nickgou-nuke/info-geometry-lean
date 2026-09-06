import Mathlib.Tactic

/-!
# Finite Gibbs variance and Fisher positivity

For a finite probability vector `p`, this owner proves the exact algebraic
identity between the centered second moment and the usual variance formula.
It is the finite theorem-safe shadow of the real Gibbs Fisher information
layer; no infinite zeta sum or convergence assertion is used.
-/

noncomputable section

namespace InfoGeometry.Topology.FiniteGibbsFisherBridge

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def finiteGibbsMean (p x : ι → ℝ) : ℝ :=
  ∑ i, p i * x i

def finiteGibbsVariance (p x : ι → ℝ) : ℝ :=
  ∑ i, p i * (x i - finiteGibbsMean p x) ^ (2 : ℕ)

theorem finiteGibbsVariance_eq_usual
    (p x : ι → ℝ) (hp : ∑ i, p i = 1) :
    finiteGibbsVariance p x =
      (∑ i, p i * x i ^ (2 : ℕ)) - (finiteGibbsMean p x) ^ (2 : ℕ) := by
  unfold finiteGibbsVariance finiteGibbsMean
  simp_rw [sub_sq]
  simp only [mul_sub, mul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hmean :
      (∑ i, p i * (2 * x i * (∑ j, p j * x j))) =
        2 * (∑ i, p i * x i) * (∑ j, p j * x j) := by
    have hpoint : (∑ i, p i * (2 * x i * (∑ j, p j * x j))) =
        ∑ i, (2 * (p i * x i)) * (∑ j, p j * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hpoint]
    let m : ℝ := ∑ j, p j * x j
    change (∑ i, (2 * (p i * x i)) * m) =
      2 * (∑ i, p i * x i) * m
    calc
      (∑ i, (2 * (p i * x i)) * (∑ j, p j * x j)) =
          (∑ i, 2 * (p i * x i)) * (∑ j, p j * x j) := by
            exact (Finset.sum_mul (Finset.univ : Finset ι)
              (fun i => 2 * (p i * x i)) m).symm
      _ = (2 * (∑ i, p i * x i)) * (∑ j, p j * x j) := by
            congr 1
            exact Finset.mul_sum (Finset.univ : Finset ι)
              (fun i => p i * x i) 2 |>.symm
      _ = 2 * (∑ i, p i * x i) * (∑ j, p j * x j) := by ring
  have hconst :
      (∑ i, p i * (∑ j, p j * x j) ^ (2 : ℕ)) =
        (∑ i, p i) * (∑ j, p j * x j) ^ (2 : ℕ) := by
    rw [← Finset.sum_mul]
  rw [hmean, hconst, hp]
  ring

theorem finiteGibbsVariance_nonnegative
    (p x : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) :
    0 ≤ finiteGibbsVariance p x := by
  unfold finiteGibbsVariance
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp_nonneg i) (sq_nonneg _)

theorem finiteGibbsVariance_usual_nonnegative
    (p x : ι → ℝ) (hp : ∑ i, p i = 1)
    (hp_nonneg : ∀ i, 0 ≤ p i) :
    0 ≤ (∑ i, p i * x i ^ (2 : ℕ)) -
      (finiteGibbsMean p x) ^ (2 : ℕ) := by
  rw [← finiteGibbsVariance_eq_usual p x hp]
  exact finiteGibbsVariance_nonnegative p x hp_nonneg

theorem finiteGibbsVariance_eq_zero_iff
    (p x : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_pos : ∀ i, 0 < p i) :
    finiteGibbsVariance p x = 0 ↔
      ∀ i, x i = finiteGibbsMean p x := by
  constructor
  · intro h i
    have hsum := Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hp_nonneg j) (sq_nonneg _)) |>.mp h
    have hi := hsum i (Finset.mem_univ i)
    have hsq : (x i - finiteGibbsMean p x) ^ (2 : ℕ) = 0 := by
      have hpi : p i ≠ 0 := ne_of_gt (hp_pos i)
      exact (mul_eq_zero.mp hi).resolve_left hpi
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h
    unfold finiteGibbsVariance
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i, sub_self, zero_pow (by norm_num), mul_zero]

theorem finiteGibbsFisher_master_packet
    (p x : ι → ℝ) (hp : ∑ i, p i = 1)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_pos : ∀ i, 0 < p i) :
    (finiteGibbsVariance p x =
      (∑ i, p i * x i ^ (2 : ℕ)) - (finiteGibbsMean p x) ^ (2 : ℕ)) ∧
    (0 ≤ finiteGibbsVariance p x) ∧
    (0 ≤ (∑ i, p i * x i ^ (2 : ℕ)) -
      (finiteGibbsMean p x) ^ (2 : ℕ)) ∧
    (finiteGibbsVariance p x = 0 ↔
      ∀ i, x i = finiteGibbsMean p x) := by
  exact ⟨finiteGibbsVariance_eq_usual p x hp,
    finiteGibbsVariance_nonnegative p x hp_nonneg,
    finiteGibbsVariance_usual_nonnegative p x hp hp_nonneg,
    finiteGibbsVariance_eq_zero_iff p x hp_nonneg hp_pos⟩

end InfoGeometry.Topology.FiniteGibbsFisherBridge
