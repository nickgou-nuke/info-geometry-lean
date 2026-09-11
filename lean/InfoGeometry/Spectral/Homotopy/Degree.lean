import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Arithmetic lemmas for degree arguments

The old degree module mixes elementary integer arithmetic with an unfinished
topological sphere-degree construction. This file ports the elementary facts
that are reusable independently of that missing topological layer.
-/

namespace InfoGeometry.Spectral.Homotopy.Degree

theorem nat_eq_one_of_mul_eq_one {n m : ℕ} (h : n * m = 1) : n = 1 := by
  exact Nat.dvd_one.mp ⟨m, h.symm⟩

theorem int_eq_one_or_neg_one_of_mul_eq_one {n m : ℤ} (h : n * m = 1) :
    n = 1 ∨ n = -1 := by
  have hn : n.natAbs * m.natAbs = 1 := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs h
  have habs : Int.natAbs n = 1 := by
    exact nat_eq_one_of_mul_eq_one hn
  cases n with
  | ofNat n =>
      left
      simp at habs ⊢
      omega
  | negSucc n =>
      right
      simp at habs ⊢
      omega

/-- Every integer with prescribed absolute value has one of the two signs. -/
theorem int_eq_natCast_or_neg_of_natAbs_eq {z : ℤ} (n : ℕ)
    (h : z.natAbs = n) : z = n ∨ z = -(n : ℤ) := by
  cases z with
  | ofNat k =>
      left
      simp at h ⊢
      omega
  | negSucc k =>
      right
      simp at h ⊢
      omega

/-- An additive endomorphism of `ℤ` is multiplication by its value at `1`.

This is the algebraic core of the degree-composition argument in the old
HoTT source; the sphere-specific degree construction is deliberately kept
separate.
-/
theorem addMonoidHom_int_apply (f : ℤ →+ ℤ) (n : ℤ) :
    f n = f 1 * n := by
  rw [show n = n • (1 : ℤ) by simp]
  rw [map_zsmul]
  simp [smul_eq_mul, mul_comm]

end InfoGeometry.Spectral.Homotopy.Degree
