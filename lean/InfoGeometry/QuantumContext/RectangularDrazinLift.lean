/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.RectangularRetract
import InfoGeometry.QuantumContext.DrazinSpectralKernel
import Lean.Elab.Tactic.Omega

/-!
# Drazin transport through a rectangular retract

The complementary operator is explicitly nilpotent. The ambient operator is
`K * A * Q + N`, with `Q * N = 0` and `N * K = 0`. No simultaneous
diagonalization or ambient commutativity is assumed. The index constructed
below is an upper bound, not a minimality assertion.
-/

namespace InfoGeometry.QuantumContext.RectangularDrazinLift

open Matrix InfoGeometry.Algebra.RectangularRetract
open InfoGeometry.QuantumContext.Drazin

variable {R m n : Type*} [Ring R]
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {K : Matrix n m R} {Q : Matrix m n R} {N : Matrix n n R}

omit [DecidableEq n] in
theorem lift_mul_complement (h : Q * K = 1) (hQN : Q * N = 0) (A : Matrix m m R) :
    cornerHom K Q h A * N = 0 := by
  simp only [cornerHom_apply, Matrix.mul_assoc, hQN, Matrix.mul_zero]

omit [DecidableEq n] in
theorem complement_mul_lift (h : Q * K = 1) (hNK : N * K = 0) (A : Matrix m m R) :
    N * cornerHom K Q h A = 0 := by
  simp only [cornerHom_apply, ← Matrix.mul_assoc, hNK, Matrix.zero_mul]

/-- Exact positive-power expansion in the ambient noncommutative algebra. -/
theorem lift_add_complement_pow_succ (h : Q * K = 1)
    (hQN : Q * N = 0) (hNK : N * K = 0) (A : Matrix m m R) (s : ℕ) :
    (cornerHom K Q h A + N) ^ (s + 1) =
      cornerHom K Q h (A ^ (s + 1)) + N ^ (s + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hNKpow : N ^ (s + 1) * K = 0 := by
        rw [pow_succ, Matrix.mul_assoc, hNK, Matrix.mul_zero]
      calc
        _ = (cornerHom K Q h (A ^ (s + 1)) + N ^ (s + 1)) *
            (cornerHom K Q h A + N) := by rw [pow_succ, ih]
        _ = cornerHom K Q h (A ^ (s + 1)) * cornerHom K Q h A +
            cornerHom K Q h (A ^ (s + 1)) * N +
            (N ^ (s + 1) * cornerHom K Q h A + N ^ (s + 1) * N) := by
              rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        _ = cornerHom K Q h (A ^ (s + 1 + 1)) + N ^ (s + 1 + 1) := by
              rw [lift_mul_complement h hQN, complement_mul_lift h hNKpow,
                add_zero, zero_add, ← map_mul, ← pow_succ, ← pow_succ]

/-- Any later exponent still satisfies the owner's Drazin power law. -/
theorem index_eq_of_le {A D : Matrix m m R} {k s : ℕ}
    (hD : IsDrazinInverse A D k) (hks : k ≤ s) : A ^ (s + 1) * D = A ^ s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hks
  calc
    A ^ (k + t + 1) * D = A ^ t * (A ^ (k + 1) * D) := by
      rw [← Matrix.mul_assoc, ← pow_add]
      congr 2 <;> omega
    _ = A ^ t * A ^ k := by rw [hD.index_eq]
    _ = A ^ (k + t) := by rw [← pow_add, Nat.add_comm]

/-- A Drazin inverse on the retract lifts across an explicitly nilpotent complement. -/
theorem isDrazinInverse_lift (h : Q * K = 1)
    (hQN : Q * N = 0) (hNK : N * K = 0)
    {A D : Matrix m m R} {k r : ℕ}
    (hD : IsDrazinInverse A D k) (hN : N ^ r = 0) :
    IsDrazinInverse (cornerHom K Q h A + N) (cornerHom K Q h D) (k + r + 1) := by
  have hleft (X : Matrix m m R) := lift_mul_complement h hQN X
  have hright (X : Matrix m m R) := complement_mul_lift h hNK X
  have hpow (s : ℕ) (hrs : r ≤ s + 1) :
      (cornerHom K Q h A + N) ^ (s + 1) = cornerHom K Q h (A ^ (s + 1)) := by
    rw [lift_add_complement_pow_succ h hQN hNK,
      pow_eq_zero_of_le hrs hN, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_add, hleft D, add_zero, ← map_mul, ← map_mul, hD.drazin_one]
  · rw [Matrix.add_mul, Matrix.mul_add, hright D, hleft D, add_zero, add_zero,
      ← map_mul, ← map_mul, hD.comm]
  · rw [hpow (k + r + 1) (by omega), hpow (k + r) (by omega), ← map_mul,
      index_eq_of_le hD (by omega)]

omit [DecidableEq n] in
/-- The lifted spectral projector transports the inner spectral projector.
It need not equal the support `K * Q`. -/
theorem lifted_spectralProj (h : Q * K = 1) (hNK : N * K = 0)
    (A D : Matrix m m R) :
    spectralProj (cornerHom K Q h A + N) (cornerHom K Q h D) =
      cornerHom K Q h (spectralProj A D) := by
  simp only [spectralProj, Matrix.add_mul, complement_mul_lift h hNK,
    add_zero, map_mul]

/-- A nontrivial ambient matrix algebra cannot satisfy a zero-exponent nilpotence premise. -/
theorem nilpotence_exponent_pos [Nontrivial R] [Nonempty n]
    {r : ℕ} (hN : N ^ r = 0) : 0 < r := by
  cases r with
  | zero => simp at hN
  | succ r => exact Nat.succ_pos r

end InfoGeometry.QuantumContext.RectangularDrazinLift
