import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import InfoGeometry.Physics.AmariSurprisalIwasawaSynthesis
import InfoGeometry.Physics.PositiveDistSphereInjectionBridge
import InfoGeometry.Algebra.BhattacharyyaFisherRaoBridge
import Mathlib.LinearAlgebra.Matrix.DotProduct

open scoped BigOperators

namespace InfoGeometry.Physics.AmariSurprisalIwasawa

noncomputable section

variable {D : ℕ}

/-- Bhattacharyya overlap of two strictly positive finite distributions. -/
def bhattacharyyaOverlap (P Q : PositiveDist D) : ℝ :=
  ∑ i, Real.sqrt (P.p i * Q.p i)

theorem bhattacharyyaOverlap_eq_dotProduct (P Q : PositiveDist D) :
    bhattacharyyaOverlap P Q =
      dotProduct (fun i => Real.sqrt (P.p i)) (fun i => Real.sqrt (Q.p i)) := by
  unfold bhattacharyyaOverlap dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.sqrt_mul (le_of_lt (P.h_pos i))]

theorem amplitude_dotProduct_self (P : PositiveDist D) :
    dotProduct (fun i => Real.sqrt (P.p i)) (fun i => Real.sqrt (P.p i)) = 1 := by
  unfold dotProduct
  have hsq : ∀ i : Fin D, (Real.sqrt (P.p i)) ^ 2 = P.p i := fun i =>
    Real.sq_sqrt (le_of_lt (P.h_pos i))
  simp_rw [show ∀ i : Fin D, Real.sqrt (P.p i) * Real.sqrt (P.p i) = P.p i by
    intro i
    nlinarith [hsq i]]
  exact P.h_sum

theorem bhattacharyyaOverlap_eq_canonicalCoeff
    (P Q : PositiveDist D) :
    bhattacharyyaOverlap P Q =
      InfoGeometry.Algebra.BhattacharyyaFisherRaoBridge.bhattacharyyaCoeff P.p Q.p := by
  rfl

/-- The overlap is symmetric. -/
theorem bhattacharyyaOverlap_comm (P Q : PositiveDist D) :
    bhattacharyyaOverlap P Q = bhattacharyyaOverlap Q P := by
  unfold bhattacharyyaOverlap
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- Self-overlap is one, using the finite square-root normalization. -/
theorem bhattacharyyaOverlap_self (P : PositiveDist D) :
    bhattacharyyaOverlap P P = 1 := by
  unfold bhattacharyyaOverlap
  exact PositiveDist.wootters_self_overlap_one P

theorem bhattacharyyaOverlap_pos (P Q : PositiveDist D) (hD : 0 < D) :
    0 < bhattacharyyaOverlap P Q := by
  unfold bhattacharyyaOverlap
  exact Finset.sum_pos' (fun i _ => by
    exact le_of_lt (Real.sqrt_pos.2 (mul_pos (P.h_pos i) (Q.h_pos i))))
    ⟨⟨0, hD⟩, Finset.mem_univ _,
      Real.sqrt_pos.2 (mul_pos (P.h_pos ⟨0, hD⟩) (Q.h_pos ⟨0, hD⟩))⟩

theorem bhattacharyyaOverlap_eq_one_imp_prob_eq
    (P Q : PositiveDist D) (h : bhattacharyyaOverlap P Q = 1) : P.p = Q.p := by
  have hterm : ∀ i : Fin D, 0 ≤ (P.p i + Q.p i) / 2 - Real.sqrt (P.p i * Q.p i) := by
    intro i
    have hp := le_of_lt (P.h_pos i)
    have hq := le_of_lt (Q.h_pos i)
    have hs := sq_nonneg (Real.sqrt (P.p i) - Real.sqrt (Q.p i))
    have hp_sq := Real.sq_sqrt hp
    have hq_sq := Real.sq_sqrt hq
    have hm := Real.sqrt_mul hp (Q.p i)
    rw [hm]
    nlinarith
  have hsum : ∑ i, ((P.p i + Q.p i) / 2 - Real.sqrt (P.p i * Q.p i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ i, (P.p i + Q.p i) / 2 = (1 : ℝ) := by
      simp_rw [add_div]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
        P.h_sum, Q.h_sum]
      norm_num
    rw [h1]
    change 1 - bhattacharyyaOverlap P Q = 0
    rw [h, sub_self]
  have hzero : ∀ i : Fin D, (P.p i + Q.p i) / 2 - Real.sqrt (P.p i * Q.p i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp hsum i (Finset.mem_univ i)
  funext i
  have hi := hzero i
  have hp := le_of_lt (P.h_pos i)
  have hq := le_of_lt (Q.h_pos i)
  have hm := Real.sqrt_mul hp (Q.p i)
  have hp_sq := Real.sq_sqrt hp
  have hq_sq := Real.sq_sqrt hq
  have h_diff_sq : (Real.sqrt (P.p i) - Real.sqrt (Q.p i)) ^ 2 = 0 := by
    have h2 : 2 * ((P.p i + Q.p i) / 2 - Real.sqrt (P.p i * Q.p i)) = 0 := by
      rw [hi, mul_zero]
    rw [hm] at h2
    nlinarith
  have h_sub_zero : Real.sqrt (P.p i) - Real.sqrt (Q.p i) = 0 :=
    sq_eq_zero_iff.mp h_diff_sq
  have h_sqrt_eq : Real.sqrt (P.p i) = Real.sqrt (Q.p i) :=
    sub_eq_zero.mp h_sub_zero
  have hs2 := congrArg (fun x : ℝ => x ^ 2) h_sqrt_eq
  simpa [Real.sq_sqrt hp, Real.sq_sqrt hq] using hs2

theorem bhattacharyyaOverlap_le_one (P Q : PositiveDist D) :
    bhattacharyyaOverlap P Q ≤ 1 := by
  unfold bhattacharyyaOverlap
  have hterm : ∀ i : Fin D,
      Real.sqrt (P.p i * Q.p i) ≤ (P.p i + Q.p i) / 2 := by
    intro i
    have hs := sq_nonneg (Real.sqrt (P.p i) - Real.sqrt (Q.p i))
    have hp := Real.sq_sqrt (le_of_lt (P.h_pos i))
    have hq := Real.sq_sqrt (le_of_lt (Q.h_pos i))
    have hm := Real.sqrt_mul (le_of_lt (P.h_pos i)) (Q.p i)
    rw [hm]
    nlinarith
  calc
    ∑ i, Real.sqrt (P.p i * Q.p i) ≤ ∑ i, (P.p i + Q.p i) / 2 :=
      Finset.sum_le_sum (fun i hi => hterm i)
    _ = 1 := by
      simp_rw [add_div]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
        P.h_sum, Q.h_sum]
      norm_num

/-- Fisher--Rao spherical distance induced by the square-root embedding. -/
noncomputable def fisherRaoDistance (P Q : PositiveDist D) : ℝ :=
  2 * Real.arccos (bhattacharyyaOverlap P Q)

/-- The induced distance is symmetric. -/
theorem fisherRaoDistance_comm (P Q : PositiveDist D) :
    fisherRaoDistance P Q = fisherRaoDistance Q P := by
  unfold fisherRaoDistance
  rw [bhattacharyyaOverlap_comm]

/-- Every state has zero Fisher--Rao distance from itself. -/
theorem fisherRaoDistance_self (P : PositiveDist D) :
    fisherRaoDistance P P = 0 := by
  unfold fisherRaoDistance
  rw [bhattacharyyaOverlap_self, Real.arccos_one]
  ring

theorem fisherRaoDistance_nonneg (P Q : PositiveDist D) :
    0 ≤ fisherRaoDistance P Q := by
  unfold fisherRaoDistance
  exact mul_nonneg (by norm_num) (Real.arccos_nonneg _)

theorem fisherRaoDistance_eq_zero_iff_overlap_eq_one
    (P Q : PositiveDist D) :
    fisherRaoDistance P Q = 0 ↔ bhattacharyyaOverlap P Q = 1 := by
  unfold fisherRaoDistance
  constructor
  · intro h
    have ha : Real.arccos (bhattacharyyaOverlap P Q) = 0 := by linarith
    have hone : 1 ≤ bhattacharyyaOverlap P Q :=
      (Real.arccos_eq_zero.mp ha)
    exact le_antisymm (bhattacharyyaOverlap_le_one P Q) hone
  · intro h
    rw [h, Real.arccos_one]
    ring


theorem fisherRaoDistance_eq_zero_of_amplitude_eq
    (P Q : PositiveDist D)
    (h : ∀ i, amplitude P i = amplitude Q i) :
    fisherRaoDistance P Q = 0 := by
  have hpq : P.p = Q.p := amplitude_map_injective P Q h
  cases P with
  | mk p hp hs =>
    cases Q with
    | mk q hq hqs =>
      dsimp at hpq ⊢
      subst q
      exact fisherRaoDistance_self ⟨p, hp, hs⟩

end
end InfoGeometry.Physics.AmariSurprisalIwasawa
