/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Quantum.QBinomial

/-!
# Cubic cancellation for an ordered braided family

The existing quantum-binomial owner supplies the expansion in a genuinely
noncommutative algebra. Here the scalar equation `1 + q + q^2 = 0` cancels
its two intermediate cubic coefficients. Nilpotence of the summands remains
an explicit additional hypothesis.

The finite-family theorem uses the order on `Fin n`: the hypothesis is
`a i * a j = q * (a j * a i)` only when `i < j`. In particular, it does not
replace the product with a commutative one or assume the opposite order has
the same phase. The result applies to native endomorphism algebras, so it
also gives a cube-zero sum of linear operators once their ordered relations
and individual cube-zero laws have been established. It does not supply a
graded Leibniz rule or imply that the square of that sum is nonzero.
-/

namespace InfoGeometry.Algebra.Quantum

open scoped BigOperators

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The cyclotomic scalar relation cancels the mixed cubic terms. Centrality
of the phase is supplied by the native algebra map. -/
theorem q_comm_cube_of_cyclotomic
    (q : k) (hq : 1 + q + q ^ 2 = 0) (a b : A)
    (hab : a * b = algebraMap k A q * (b * a)) :
    (a + b) ^ 3 = a ^ 3 + b ^ 3 := by
  have h31 : qBinomial q 3 1 = 0 := by
    calc
      qBinomial q 3 1 = 1 + q + q ^ 2 := by
        norm_num [qBinomial]; ring
      _ = 0 := hq
  have h32 : qBinomial q 3 2 = 0 := by
    calc
      qBinomial q 3 2 = 1 + q + q ^ 2 := by
        norm_num [qBinomial]; ring
      _ = 0 := hq
  simpa [Finset.sum_range_succ, h31, h32, qBinomial_self, add_comm] using
    (q_binomial_expansion q b a hab 3)

/-- Cube-zero summands with the stated ordered braiding have cube-zero sum. -/
theorem q_comm_add_cube_zero
    (q : k) (hq : 1 + q + q ^ 2 = 0) (a b : A)
    (hab : a * b = algebraMap k A q * (b * a))
    (ha : a ^ 3 = 0) (hb : b ^ 3 = 0) :
    (a + b) ^ 3 = 0 := by
  rw [q_comm_cube_of_cyclotomic q hq a b hab, ha, hb, add_zero]

/-- The ordered pairwise phase relations extend cubic cancellation to every
finite family. No nilpotency assumption is needed for this identity. -/
theorem q_comm_finSum_cube (q : k) (hq : 1 + q + q ^ 2 = 0) :
    ∀ (n : ℕ) (a : Fin n → A),
      (∀ i j : Fin n, i < j →
        a i * a j = algebraMap k A q * (a j * a i)) →
      (∑ i : Fin n, a i) ^ 3 = ∑ i : Fin n, (a i) ^ 3 := by
  intro n
  induction n with
  | zero =>
      intro a _
      simp
  | succ n ih =>
      intro a hcomm
      have hhead : a 0 * (∑ i : Fin n, a i.succ) =
          algebraMap k A q * ((∑ i : Fin n, a i.succ) * a 0) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact hcomm 0 i.succ (Fin.succ_pos i)
      have htail : ∀ i j : Fin n, i < j →
          a i.succ * a j.succ = algebraMap k A q * (a j.succ * a i.succ) := by
        intro i j hij
        exact hcomm i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
      calc
        (∑ i : Fin (n + 1), a i) ^ 3 =
            (a 0 + ∑ i : Fin n, a i.succ) ^ 3 := by
              rw [Fin.sum_univ_succ]
        _ = (a 0) ^ 3 + (∑ i : Fin n, a i.succ) ^ 3 :=
              q_comm_cube_of_cyclotomic q hq (a 0) _ hhead
        _ = (a 0) ^ 3 + ∑ i : Fin n, (a i.succ) ^ 3 := by
              rw [ih (fun i : Fin n => a i.succ) htail]
        _ = ∑ i : Fin (n + 1), (a i) ^ 3 :=
              (Fin.sum_univ_succ (fun i : Fin (n + 1) => (a i) ^ 3)).symm

/-- An ordered finite sum is cube-zero when every summand is cube-zero. This
is the applicable nilpotency theorem for a finite sum of braided operators. -/
theorem q_comm_finSum_cube_zero
    (q : k) (hq : 1 + q + q ^ 2 = 0) (n : ℕ) (a : Fin n → A)
    (hcomm : ∀ i j : Fin n, i < j →
      a i * a j = algebraMap k A q * (a j * a i))
    (hcube : ∀ i : Fin n, (a i) ^ 3 = 0) :
    (∑ i : Fin n, a i) ^ 3 = 0 := by
  rw [q_comm_finSum_cube q hq n a hcomm]
  exact Finset.sum_eq_zero (fun i _ => hcube i)

end InfoGeometry.Algebra.Quantum
