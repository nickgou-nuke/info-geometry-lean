import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Finite Aitchison coordinates

This file contains the finite, strictly positive simplex part of the
Aitchison construction.  It deliberately does not identify a density
operator, a partial trace, or a Radon transform with a probability vector.
Those are separate constructions which may be connected by additional data.
-/

open scoped BigOperators

namespace InfoGeometry.Probability.AitchisonFinite

/-- The strictly positive finite probability simplex. -/
abbrev PositiveSimplex (n : ℕ) :=
  {p : Fin n → ℝ // (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

/-- The mean of the logarithmic coordinates of a positive composition. -/
noncomputable def logMean {n : ℕ} (p : PositiveSimplex n) (_hn : 0 < n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, Real.log (p.1 i)

/-- Centered log-ratio coordinates. -/
noncomputable def clr {n : ℕ} (p : PositiveSimplex n) (hn : 0 < n) : Fin n → ℝ :=
  fun i => Real.log (p.1 i) - logMean p hn

theorem sum_clr {n : ℕ} (p : PositiveSimplex n) (hn : 0 < n) :
    ∑ i, clr p hn i = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold clr logMean
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem clr_sub_eq_log_ratio {n : ℕ} (p : PositiveSimplex n) (hn : 0 < n)
    (i j : Fin n) :
    clr p hn i - clr p hn j = Real.log (p.1 i / p.1 j) := by
  unfold clr
  rw [sub_sub_sub_cancel_right]
  rw [Real.log_div (ne_of_gt (p.2.1 i)) (ne_of_gt (p.2.1 j))]

theorem continuous_clr {n : ℕ} (hn : 0 < n) :
    Continuous (fun p : PositiveSimplex n => clr p hn) := by
  apply continuous_pi
  intro i
  unfold clr logMean
  have hcoord : Continuous (fun p : PositiveSimplex n => Real.log (p.1 i)) := by
    let f : PositiveSimplex n → {x : ℝ // 0 < x} :=
      fun p => ⟨p.1 i, p.2.1 i⟩
    have hf : Continuous f := by
      exact Continuous.subtype_mk
        ((continuous_apply i).comp continuous_subtype_val)
        (fun p => p.2.1 i)
    simpa only [f, Function.comp_apply] using Real.continuous_log'.comp hf
  have hsum : Continuous
      (fun p : PositiveSimplex n => ∑ j : Fin n, Real.log (p.1 j)) := by
    exact continuous_finset_sum _ (fun j _ => by
      let f : PositiveSimplex n → {x : ℝ // 0 < x} :=
        fun p => ⟨p.1 j, p.2.1 j⟩
      have hf : Continuous f := by
        exact Continuous.subtype_mk
          ((continuous_apply j).comp continuous_subtype_val)
          (fun p => p.2.1 j)
      simpa only [f, Function.comp_apply] using Real.continuous_log'.comp hf)
  fun_prop

/-- The Aitchison bilinear expression in centered coordinates. -/
noncomputable def inner (p q : PositiveSimplex n) (hn : 0 < n) : ℝ :=
  ∑ i, clr p hn i * clr q hn i

theorem inner_symm {n : ℕ} (p q : PositiveSimplex n) (hn : 0 < n) :
    inner p q hn = inner q p hn := by
  unfold inner
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem inner_self_nonneg {n : ℕ} (p : PositiveSimplex n) (hn : 0 < n) :
    0 ≤ inner p p hn := by
  unfold inner
  simpa [pow_two] using
    (Finset.sum_nonneg (fun i hi => sq_nonneg (clr p hn i)))

/-- The normalized exponential (softmax) composition. -/
noncomputable def softmax (n : ℕ) (z : Fin n → ℝ) (hn : 0 < n) :
    PositiveSimplex n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Z : ℝ := ∑ i, Real.exp (z i)
  have hZ : 0 < Z := by
    dsimp [Z]
    exact Finset.sum_pos' (fun i hi => le_of_lt (Real.exp_pos (z i)))
      ⟨⟨0, hn⟩, Finset.mem_univ _, Real.exp_pos (z ⟨0, hn⟩)⟩
  exact ⟨fun i => Real.exp (z i) / Z,
    ⟨fun i => div_pos (Real.exp_pos _) hZ,
      by
        dsimp [Z]
        rw [← Finset.sum_div]
        exact div_self hZ.ne'⟩⟩

theorem softmax_apply {n : ℕ} (z : Fin n → ℝ) (hn : 0 < n) (i : Fin n) :
    (softmax n z hn).1 i =
      Real.exp (z i) / ∑ j, Real.exp (z j) := by
  rfl

theorem continuous_softmax {n : ℕ} (hn : 0 < n) :
    Continuous (fun z : Fin n → ℝ => softmax n z hn) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply Continuous.subtype_mk
  · apply continuous_pi
    intro i
    apply Continuous.div₀
    · exact Real.continuous_exp.comp (continuous_apply i)
    · exact continuous_finset_sum _ (fun j _ =>
        Real.continuous_exp.comp (continuous_apply j))
    · intro z
      exact ne_of_gt (Finset.sum_pos' (fun j _ => le_of_lt (Real.exp_pos (z j)))
        ⟨⟨0, hn⟩, Finset.mem_univ _, Real.exp_pos (z ⟨0, hn⟩)⟩)

theorem softmax_clr {n : ℕ} (p : PositiveSimplex n) (hn : 0 < n) :
    softmax n (clr p hn) hn = p := by
  apply Subtype.ext
  funext i
  rw [softmax_apply]
  unfold clr logMean
  have hlog : ∀ j : Fin n, Real.exp (Real.log (p.1 j)) = p.1 j := by
    intro j
    exact Real.exp_log (p.2.1 j)
  rw [Real.exp_sub]
  rw [hlog i]
  have hsum :
      (∑ j : Fin n, Real.exp (Real.log (p.1 j) -
        (n : ℝ)⁻¹ * ∑ k : Fin n, Real.log (p.1 k))) =
        (∑ j : Fin n, p.1 j) /
          Real.exp ((n : ℝ)⁻¹ * ∑ k : Fin n, Real.log (p.1 k)) := by
    simp_rw [Real.exp_sub, hlog]
    rw [Finset.sum_div]
  rw [hsum, p.2.2]
  field_simp

theorem softmax_uniform_shift {n : ℕ} (z : Fin n → ℝ) (c : ℝ) (hn : 0 < n) :
    softmax n (fun i => z i + c) hn = softmax n z hn := by
  apply Subtype.ext
  funext i
  rw [softmax_apply, softmax_apply]
  have hsum : (∑ j : Fin n, Real.exp (z j + c)) =
      Real.exp c * ∑ j : Fin n, Real.exp (z j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.exp_add]
    ring
  rw [hsum, Real.exp_add]
  field_simp

theorem clr_softmax_centered {n : ℕ} (z : Fin n → ℝ) (hn : 0 < n)
    (hz : ∑ i, z i = 0) (i : Fin n) :
    clr (softmax n z hn) hn i = z i := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hZ : 0 < ∑ j : Fin n, Real.exp (z j) := by
    exact Finset.sum_pos' (fun j hj => le_of_lt (Real.exp_pos (z j)))
      ⟨⟨0, hn⟩, Finset.mem_univ _, Real.exp_pos (z ⟨0, hn⟩)⟩
  have hlog : ∀ j : Fin n,
      Real.log ((softmax n z hn).1 j) =
        z j - Real.log (∑ k : Fin n, Real.exp (z k)) := by
    intro j
    rw [softmax_apply, Real.log_div (ne_of_gt (Real.exp_pos (z j))) hZ.ne']
    rw [Real.log_exp]
  unfold clr logMean
  rw [hlog i]
  have hsumlog : (∑ j : Fin n, Real.log ((softmax n z hn).1 j)) =
      ∑ j : Fin n, z j - (n : ℝ) * Real.log (∑ k : Fin n, Real.exp (z k)) := by
    simp_rw [hlog]
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsumlog, hz]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

end InfoGeometry.Probability.AitchisonFinite
