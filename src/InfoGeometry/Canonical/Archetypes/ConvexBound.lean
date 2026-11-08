import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Function
import InfoGeometry.Core.ProjectiveSimplex

open Pointwise

theorem convexOn_stdSimplex_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : ConvexOn ℝ (stdSimplex ℝ ι) f) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    {M : ℝ} (hM : ∀ i, f (Pi.single i 1) ≤ M) : f x ≤ M := by
  have H : x = Finset.univ.centerMass x (fun i => Pi.single i 1) := by
    rw [Finset.centerMass]
    simp only [hx.2, inv_one, one_smul]
    ext j
    rw [Finset.sum_apply]
    simp [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [H]
  have h_w0 : ∀ i ∈ Finset.univ, 0 ≤ x i := fun i _ => hx.1 i
  have h_w1 : 0 < ∑ i : ι, x i := by rw [hx.2]; exact zero_lt_one
  have h_p : ∀ i ∈ Finset.univ, Pi.single i 1 ∈ stdSimplex ℝ ι := by
    intro i _
    constructor
    · intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    · simp
  have H2 := hf.map_centerMass_le h_w0 h_w1 h_p
  refine le_trans H2 ?_
  have H3 : Finset.univ.centerMass x (f ∘ fun i => Pi.single i 1) = ∑ i : ι, x i * f (Pi.single i 1) := by
    rw [Finset.centerMass]
    simp [hx.2]
  rw [H3]
  have H4 : ∑ i : ι, x i * f (Pi.single i 1) ≤ ∑ i : ι, x i * M := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hM i) (hx.1 i)
  refine le_trans H4 ?_
  rw [← Finset.sum_mul, hx.2, one_mul]
