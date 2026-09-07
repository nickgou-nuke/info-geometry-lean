import Mathlib

/-!
# Finite absolute-deviation shift estimation

A median is a global minimizer of the sum of absolute deviations. Existence
is proved by compact minimization and an explicit projection argument. The
majority bound allows arbitrary values on the remaining energy lines.
No probabilistic independence or asymptotic precision is assumed.
-/

noncomputable section
open scoped BigOperators
namespace InfoGeometry.Probability.FiniteMedianShift

def loss {n : ℕ} (x : Fin n → ℝ) (s : ℝ) : ℝ := ∑ i, |x i - s|

theorem loss_continuous {n : ℕ} (x : Fin n → ℝ) : Continuous (loss x) := by
  unfold loss
  fun_prop

/-- A minimizer exists for every finite row, including the empty row. -/
theorem exists_median {n : ℕ} (x : Fin n → ℝ) :
    ∃ s, ∀ t, loss x s ≤ loss x t := by
  let M := ∑ i, |x i|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  have hx : ∀ i, -M ≤ x i ∧ x i ≤ M := by
    intro i
    have h : |x i| ≤ M := Finset.single_le_sum (fun k _ => abs_nonneg (x k))
      (Finset.mem_univ i)
    exact abs_le.mp h
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-M) M).Nonempty from ⟨0, by constructor <;> linarith⟩)
    (loss_continuous x).continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases hlo : t < -M
  · have hbound := hmin (show -M ∈ Set.Icc (-M) M by constructor <;> linarith)
    apply hbound.trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (by linarith [(hx i).1] : 0 ≤ x i - -M),
      abs_of_nonneg (by linarith [(hx i).1] : 0 ≤ x i - t)]
    linarith
  · by_cases hhi : M < t
    · have hbound := hmin (show M ∈ Set.Icc (-M) M by constructor <;> linarith)
      apply hbound.trans
      apply Finset.sum_le_sum
      intro i _
      rw [abs_of_nonpos (by linarith [(hx i).2] : x i - M ≤ 0),
        abs_of_nonpos (by linarith [(hx i).2] : x i - t ≤ 0)]
      linarith
    · exact hmin ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

/-- The minimizer set translates with the data; no reference spectrum is used. -/
theorem median_translation {n : ℕ} (x : Fin n → ℝ) (s c : ℝ) :
    (∀ t, loss (fun i => x i + c) (s + c) ≤ loss (fun i => x i + c) t) ↔
      (∀ t, loss x s ≤ loss x t) := by
  have shift (u : ℝ) : loss (fun i => x i + c) (u + c) = loss x u := by
    unfold loss
    congr 1
    funext i
    congr 1
    ring
  constructor
  · intro h t
    simpa only [shift] using h (t + c)
  · intro h t
    have ht : t = (t - c) + c := by ring
    rw [ht, shift, shift]
    exact h (t - c)

/-- A strict majority controls the estimate regardless of the other values.
The inequality is useful before division and also proves exact recovery when
the good observations coincide. -/
theorem majority_bound {n : ℕ} (x : Fin n → ℝ) (s θ δ : ℝ)
    (hs : ∀ t, loss x s ≤ loss x t) (good : Finset (Fin n))
    (hgood : ∀ i ∈ good, |x i - θ| ≤ δ) :
    ((good.card : ℝ) - (goodᶜ.card : ℝ)) * |s - θ| ≤ 2 * good.card * δ := by
  classical
  have hg : ∀ i ∈ good, |s - θ| - 2 * δ ≤ |x i - s| - |x i - θ| := by
    intro i hi
    have htri := abs_add_le (s - x i) (x i - θ)
    rw [show s - x i + (x i - θ) = s - θ by ring, abs_sub_comm s (x i)] at htri
    linarith [hgood i hi]
  have hb : ∀ i ∈ goodᶜ, -|s - θ| ≤ |x i - s| - |x i - θ| := by
    intro i _
    have htri := abs_add_le (x i - s) (s - θ)
    rw [show x i - s + (s - θ) = x i - θ by ring] at htri
    linarith
  have hgs := Finset.sum_le_sum hg
  have hbs := Finset.sum_le_sum hb
  simp only [Finset.sum_const, nsmul_eq_mul] at hgs hbs
  have hsplit := Finset.sum_add_sum_compl good (fun i => |x i - s| - |x i - θ|)
  simp only [Finset.sum_sub_distrib] at hsplit hgs hbs
  have hmin := hs θ
  unfold loss at hmin
  nlinarith

theorem strict_majority_exact {n : ℕ} (x : Fin n → ℝ) (s θ : ℝ)
    (hs : ∀ t, loss x s ≤ loss x t) (good : Finset (Fin n))
    (hmajority : goodᶜ.card < good.card) (hgood : ∀ i ∈ good, x i = θ) : s = θ := by
  have h := majority_bound x s θ 0 hs good (by intro i hi; simp [hgood i hi])
  have hc : (goodᶜ.card : ℝ) < good.card := by exact_mod_cast hmajority
  have hzero : |s - θ| = 0 := by nlinarith [abs_nonneg (s - θ)]
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- A concrete choice from the nonempty set of L1 minimizers. With an even
sample the minimizer need not be unique; no tie-breaking equivariance is claimed. -/
def median {n : ℕ} (x : Fin n → ℝ) : ℝ := Classical.choose (exists_median x)

theorem median_minimizes {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    loss x (median x) ≤ loss x t := Classical.choose_spec (exists_median x) t

theorem median_constant {n : ℕ} (hn : 0 < n) (c : ℝ) :
    median (fun _ : Fin n => c) = c := by
  apply strict_majority_exact _ _ c (median_minimizes _) Finset.univ
  · simpa using hn
  · intro i _
    rfl

/-- A strict majority below a threshold forces every median below it. -/
theorem median_le_of_majority {n : ℕ} (x : Fin n → ℝ) (s u : ℝ)
    (hs : ∀ t, loss x s ≤ loss x t) (good : Finset (Fin n))
    (hmajority : goodᶜ.card < good.card) (hgood : ∀ i ∈ good, x i ≤ u) : s ≤ u := by
  by_contra h
  have hus : u < s := lt_of_not_ge h
  have hg : ∀ i ∈ good, s - u ≤ |x i - s| - |x i - u| := by
    intro i hi
    rw [abs_of_nonpos (by linarith [hgood i hi] : x i - s ≤ 0),
      abs_of_nonpos (sub_nonpos.mpr (hgood i hi))]
    linarith
  have hb : ∀ i ∈ goodᶜ, -(s - u) ≤ |x i - s| - |x i - u| := by
    intro i _
    have ht := abs_add_le (x i - s) (s - u)
    rw [show x i - s + (s - u) = x i - u by ring,
      abs_of_pos (sub_pos.mpr hus)] at ht
    linarith
  have hgs := Finset.sum_le_sum hg
  have hbs := Finset.sum_le_sum hb
  simp only [Finset.sum_const, nsmul_eq_mul] at hgs hbs
  have hsplit := Finset.sum_add_sum_compl good (fun i => |x i - s| - |x i - u|)
  simp only [Finset.sum_sub_distrib] at hsplit hgs hbs
  have hmin := hs u
  unfold loss at hmin
  have hc : (goodᶜ.card : ℝ) < good.card := by exact_mod_cast hmajority
  nlinarith

/-- The sharp majority robustness statement: arbitrary outliers cannot move
any L1 median outside an interval containing a strict majority. -/
theorem median_interval {n : ℕ} (x : Fin n → ℝ) (s θ δ : ℝ)
    (hs : ∀ t, loss x s ≤ loss x t) (good : Finset (Fin n))
    (hmajority : goodᶜ.card < good.card)
    (hgood : ∀ i ∈ good, |x i - θ| ≤ δ) : |s - θ| ≤ δ := by
  have hu : s ≤ θ + δ := median_le_of_majority x s (θ + δ) hs good hmajority
    (by intro i hi; have h := (abs_le.mp (hgood i hi)).2; linarith)
  have hneg : ∀ t, loss (fun i => -x i) (-s) ≤ loss (fun i => -x i) t := by
    intro t
    have h := hs (-t)
    have heq (v : ℝ) : loss (fun i => -x i) (-v) = loss x v := by
      unfold loss
      congr 1
      funext i
      rw [show -x i - -v = -(x i - v) by ring, abs_neg]
    rw [heq, show t = -(-t) by ring, heq]
    exact h
  have hl := median_le_of_majority (fun i => -x i) (-s) (-θ + δ)
    hneg good hmajority (by
      intro i hi
      have h := (abs_le.mp (hgood i hi)).1
      linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end InfoGeometry.Probability.FiniteMedianShift
