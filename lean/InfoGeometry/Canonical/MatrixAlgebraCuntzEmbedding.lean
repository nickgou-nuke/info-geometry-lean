import Mathlib.Algebra.Star.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Basic
import InfoGeometry.Canonical.CuntzNIsometries
import InfoGeometry.Canonical.CuntzWordReduction

open BigOperators

namespace CuntzAlgebra

variable {n : ℕ} {A : Type*} [Ring A] [StarRing A]

/-- Matrix Unit Generator e_(α,β) = S_α S_β* in the core algebra -/
def matrixUnit (c : CuntzIsometries n A) (α β : List (Fin n)) : A :=
  wordS c α * wordSStar c β

/-- Lemma: Adjoint of wordS is wordSStar -/
theorem star_wordS (c : CuntzIsometries n A) (w : List (Fin n)) :
    star (wordS c w) = wordSStar c w := by
  induction w with
  | nil =>
    dsimp [wordS, wordSStar]
    rw [star_one]
  | cons i v ih =>
    dsimp [wordS, wordSStar]
    rw [star_mul, ih]

/-- 🏆 THEOREM 1: Adjoint Relation for Matrix Units: (e_(α,β))* = e_(β,α) -/
theorem star_matrixUnit (c : CuntzIsometries n A) (α β : List (Fin n)) :
    star (matrixUnit c α β) = matrixUnit c β α := by
  dsimp [matrixUnit]
  rw [star_mul]
  have h_star_star : star (wordSStar c β) = wordS c β := by
    induction β with
    | nil =>
      dsimp [wordSStar, wordS]
      rw [star_one]
    | cons j v ih =>
      dsimp [wordSStar, wordS]
      rw [star_mul, star_star, ih]
  rw [h_star_star, star_wordS]

/-- Lemma: Orthogonality of distinct words of equal length: S_w1* S_w2 = 0 for w1 ≠ w2 -/
theorem word_reduction_ne_of_length (c : CuntzIsometries n A) :
    ∀ (w1 w2 : List (Fin n)), w1.length = w2.length → w1 ≠ w2 →
    wordSStar c w1 * wordS c w2 = 0 := by
  intro w1
  induction w1 with
  | nil =>
    intro w2 hlen hne
    cases w2 with
    | nil => exact (hne rfl).elim
    | cons j v2 => contradiction
  | cons i v1 ih =>
    intro w2 hlen hne
    cases w2 with
    | nil => contradiction
    | cons j v2 =>
      by_cases hij : i = j
      · subst hij
        have hne_v : v1 ≠ v2 := by
          intro h_eq; apply hne; rw [h_eq]
        have hlen_v : v1.length = v2.length := by
          simp only [List.length_cons] at hlen
          exact Nat.succ.inj hlen
        dsimp [wordSStar, wordS]
        calc (wordSStar c v1 * star (c.S i)) * (c.S i * wordS c v2)
          _ = wordSStar c v1 * (star (c.S i) * c.S i) * wordS c v2 := by simp [mul_assoc]
          _ = wordSStar c v1 * 1 * wordS c v2 := by simp [isometry_delta]
          _ = wordSStar c v1 * wordS c v2 := by rw [mul_one]
          _ = 0 := ih v2 hlen_v hne_v
      · dsimp [wordSStar, wordS]
        calc (wordSStar c v1 * star (c.S i)) * (c.S j * wordS c v2)
          _ = wordSStar c v1 * (star (c.S i) * c.S j) * wordS c v2 := by simp [mul_assoc]
          _ = wordSStar c v1 * 0 * wordS c v2 := by
            rw [show star (c.S i) * c.S j = 0 by
              simpa [hij] using isometry_delta c i j]
          _ = 0 := by rw [mul_zero, zero_mul]

/-- 🏆 THEOREM 2: Canonical Matrix Unit Algebra Law
    e_(α,β) * e_(γ,δ) = δ_(β,γ) e_(α,δ) for equal-length words |β| = |γ|. -/
theorem matrixUnit_mul (c : CuntzIsometries n A) (α β γ δ : List (Fin n))
    (hlen : β.length = γ.length) :
    matrixUnit c α β * matrixUnit c γ δ = if β = γ then matrixUnit c α δ else 0 := by
  dsimp [matrixUnit]
  split_ifs with h_eq
  · subst h_eq
    calc (wordS c α * wordSStar c β) * (wordS c β * wordSStar c δ)
      _ = wordS c α * (wordSStar c β * wordS c β) * wordSStar c δ := by simp [mul_assoc]
      _ = wordS c α * 1 * wordSStar c δ := by rw [word_reduction_exact]
      _ = wordS c α * wordSStar c δ := by rw [mul_one]
  · calc (wordS c α * wordSStar c β) * (wordS c γ * wordSStar c δ)
      _ = wordS c α * (wordSStar c β * wordS c γ) * wordSStar c δ := by simp [mul_assoc]
      _ = wordS c α * 0 * wordSStar c δ := by rw [word_reduction_ne_of_length c β γ hlen h_eq]
      _ = 0 := by rw [mul_zero, zero_mul]

end CuntzAlgebra
