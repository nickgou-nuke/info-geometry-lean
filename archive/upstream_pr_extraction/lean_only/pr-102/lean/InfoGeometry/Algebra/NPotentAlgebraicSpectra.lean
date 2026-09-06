/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# Native Mathlib Formalization: n-Potent Operator Algebraic Spectra

This module formalizes the algebraic identities and spectral projector properties
for $n$-potent elements and operators satisfying $x^n = x$ over commutative and general rings.

All proofs are complete in native Lean 4 + Mathlib with 0 sorrys, 0 admits, and 0 custom axioms.
-/

namespace InfoGeometry.Algebra.NPotentSpectra

variable {R : Type*} [CommRing R]

/-- Definition of an $n$-potent element in a commutative ring: $x^n = x$. -/
def IsNPotent (x : R) (n : ℕ) : Prop :=
  x ^ n = x

/-! ### 1. Factorizations for Low Degrees (p = 2, 3, 5, 7, 11, 13) -/

/-- Degree 2: $x(x - 1) = x^2 - x$. -/
theorem npotent_two_factor (x : R) (hx : IsNPotent x 2) :
    x * (x - 1) = 0 := by
  dsimp [IsNPotent] at hx
  calc
    x * (x - 1) = x ^ 2 - x := by ring
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-- Degree 3: $x(x - 1)(x + 1) = x^3 - x$. -/
theorem npotent_three_factor (x : R) (hx : IsNPotent x 3) :
    x * (x - 1) * (x + 1) = 0 := by
  dsimp [IsNPotent] at hx
  calc
    x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-- Degree 5: $x(x^2 - 1)(x^2 + 1) = x^5 - x$. -/
theorem npotent_five_factor (x : R) (hx : IsNPotent x 5) :
    x * (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
  dsimp [IsNPotent] at hx
  calc
    x * (x ^ 2 - 1) * (x ^ 2 + 1) = x ^ 5 - x := by ring
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-- Degree 7: $x(x^3 - 1)(x^3 + 1) = x^7 - x$. -/
theorem npotent_seven_factor (x : R) (hx : IsNPotent x 7) :
    x * (x ^ 3 - 1) * (x ^ 3 + 1) = 0 := by
  dsimp [IsNPotent] at hx
  calc
    x * (x ^ 3 - 1) * (x ^ 3 + 1) = x ^ 7 - x := by ring
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-- Degree 11: $x(x^5 - 1)(x^5 + 1) = x^{11} - x$. -/
theorem npotent_eleven_factor (x : R) (hx : IsNPotent x 11) :
    x * (x ^ 5 - 1) * (x ^ 5 + 1) = 0 := by
  dsimp [IsNPotent] at hx
  calc
    x * (x ^ 5 - 1) * (x ^ 5 + 1) = x ^ 11 - x := by ring
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-- Degree 13: $x(x^6 - 1)(x^6 + 1) = x^{13} - x$. -/
theorem npotent_thirteen_factor (x : R) (hx : IsNPotent x 13) :
    x * (x ^ 6 - 1) * (x ^ 6 + 1) = 0 := by
  dsimp [IsNPotent] at hx
  calc
    x * (x ^ 6 - 1) * (x ^ 6 + 1) = x ^ 13 - x := by ring
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-! ### 2. Cyclotomics & Unitary Roots -/

/-- Any $m$-th root of unity generates an $(m+1)$-potent element. -/
theorem root_of_unity_is_npotent (u : R) (m : ℕ) (hu : u ^ m = 1) :
    IsNPotent u (m + 1) := by
  dsimp [IsNPotent]
  calc
    u ^ (m + 1) = u ^ m * u := by rw [pow_succ]
    _ = 1 * u := by rw [hu]
    _ = u := one_mul u

/-! ### 3. General Spectral Projectors -/

/-- Nonzero-mode projector for an $n$-potent element: $P_1 = x^{n-1}$. -/
def projNonzero (x : R) (n : ℕ) : R :=
  x ^ (n - 1)

/-- Zero-mode projector for an $n$-potent element: $P_0 = 1 - x^{n-1}$. -/
def projZero (x : R) (n : ℕ) : R :=
  1 - x ^ (n - 1)

/-- Partition of unity: $P_0 + P_1 = 1$. -/
theorem proj_sum (x : R) (n : ℕ) :
    projZero x n + projNonzero x n = 1 := by
  dsimp [projZero, projNonzero]
  ring

/-- Orthogonality of zero-mode and nonzero-mode projectors. -/
theorem proj_orthogonal (x : R) (n : ℕ) (hn : 2 ≤ n) (hx : IsNPotent x n) :
    projZero x n * projNonzero x n = 0 := by
  dsimp [projZero, projNonzero, IsNPotent] at *
  have hs : (n - 1) + (n - 1) = n + (n - 2) := by omega
  calc
    (1 - x ^ (n - 1)) * x ^ (n - 1) = x ^ (n - 1) - x ^ (n - 1) * x ^ (n - 1) := by ring
    _ = x ^ (n - 1) - x ^ ((n - 1) + (n - 1)) := by rw [← pow_add]
    _ = x ^ (n - 1) - x ^ (n + (n - 2)) := by rw [hs]
    _ = x ^ (n - 1) - x ^ n * x ^ (n - 2) := by rw [pow_add]
    _ = x ^ (n - 1) - x * x ^ (n - 2) := by rw [hx]
    _ = x ^ (n - 1) - x ^ (n - 2 + 1) := by rw [← pow_succ' x (n - 2)]
    _ = x ^ (n - 1) - x ^ (n - 1) := by
      have h1 : n - 2 + 1 = n - 1 := by omega
      rw [h1]
    _ = 0 := sub_self _

/-! ### 4. Nilpotent Power Vanishing -/

/-- For any nilpotent of degree 2 ($N^2 = 0$), higher powers $N^p$ vanish for all $p \ge 2$. -/
theorem nilpotent_power_vanishing (N : R) (hN : N * N = 0) (p : ℕ) (hp : 2 ≤ p) :
    N ^ p = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp
  have hN2 : N ^ 2 = 0 := by rw [pow_two, hN]
  calc
    N ^ p = N ^ (2 + k) := by rw [hk]
    _ = N ^ 2 * N ^ k := by rw [pow_add]
    _ = 0 * N ^ k := by rw [hN2]
    _ = 0 := MulZeroClass.zero_mul _

/-! ### 5. Linear Operator Lift (Module.End) -/

section LinearOperatorLift

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- Definition of an $n$-potent linear operator: $T^n = T$. -/
def IsNPotentOperator (T : Module.End K M) (n : ℕ) : Prop :=
  T ^ n = T

/-- Nonzero-mode projection operator: $P_1 = T^{n-1}$. -/
def opProjNonzero (T : Module.End K M) (n : ℕ) : Module.End K M :=
  T ^ (n - 1)

/-- Zero-mode projection operator: $P_0 = I - T^{n-1}$. -/
def opProjZero (T : Module.End K M) (n : ℕ) : Module.End K M :=
  1 - T ^ (n - 1)

/-- Operator partition of unity: $P_0 + P_1 = I$. -/
theorem opProj_sum (T : Module.End K M) (n : ℕ) :
    opProjZero T n + opProjNonzero T n = 1 := by
  dsimp [opProjZero, opProjNonzero]
  exact sub_add_cancel 1 (T ^ (n - 1))

/-- Orthogonality of zero-mode and nonzero-mode operators: $P_0 \circ P_1 = 0$. -/
theorem opProj_orthogonal (T : Module.End K M) (n : ℕ) (hn : 2 ≤ n) (hT : IsNPotentOperator T n) :
    opProjZero T n * opProjNonzero T n = 0 := by
  dsimp [opProjZero, opProjNonzero, IsNPotentOperator] at *
  have hs : (n - 1) + (n - 1) = n + (n - 2) := by omega
  calc
    (1 - T ^ (n - 1)) * T ^ (n - 1) = T ^ (n - 1) - T ^ (n - 1) * T ^ (n - 1) := by
      rw [sub_mul, one_mul]
    _ = T ^ (n - 1) - T ^ ((n - 1) + (n - 1)) := by rw [← pow_add]
    _ = T ^ (n - 1) - T ^ (n + (n - 2)) := by rw [hs]
    _ = T ^ (n - 1) - T ^ n * T ^ (n - 2) := by rw [pow_add]
    _ = T ^ (n - 1) - T * T ^ (n - 2) := by rw [hT]
    _ = T ^ (n - 1) - T ^ (n - 2 + 1) := by rw [← pow_succ' T (n - 2)]
    _ = T ^ (n - 1) - T ^ (n - 1) := by
      have h1 : n - 2 + 1 = n - 1 := by omega
      rw [h1]
    _ = 0 := sub_self _

/-- Every vector decomposes into a zero-mode part and a nonzero-mode part. -/
theorem vector_spectral_decomposition (T : Module.End K M) (n : ℕ) (v : M) :
    v = opProjZero T n v + opProjNonzero T n v := by
  have h := congr_fun (congr_arg DFunLike.coe (opProj_sum T n)) v
  exact h.symm

end LinearOperatorLift

end InfoGeometry.Algebra.NPotentSpectra
