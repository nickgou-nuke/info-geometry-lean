/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.QuantumAlgebra.RankTwoCyclotomicArtinBridge

open Matrix

set_option linter.unnecessarySeqFocus false

/-!
# Universal Rank-Two Dihedral Cyclotomic Artin Bridge ($I_2(5) \rightsquigarrow \phi$ vs $I_2(6) \rightsquigarrow \sqrt{3}$)

This module formalizes the exact algebraic unification of the rank-2 dihedral Coxeter family $I_2(m)$
governed by the quantum integer $[2]_q = q + q^{-1} = 2\cos(\pi/m)$ at primitive roots of unity:

1. **$m = 5$ ($I_2(5)$, Pentagonal / Fibonacci anyons / $\operatorname{SU}(2)_3$)**:
   $$\Phi_{10}(\zeta) = 0 \implies d_5 = \zeta + \zeta^{-1} \implies d_5^2 = d_5 + 1 \quad (\phi^2 = \phi + 1)$$
   $$\operatorname{tr}(C_5) = \phi^2 - 2 = \phi - 1 = \phi^{-1} = 2\cos(2\pi/5), \quad (B_1 B_2)^5 = I_2$$

2. **$m = 6$ ($I_2(6)$, Hexagonal / $G_2$ Cartan plane / $\operatorname{SU}(2)_4$)**:
   $$\Phi_{12}(\zeta) = 0 \implies d_6 = \zeta + \zeta^{-1} \implies d_6^2 = 3 \quad ((\sqrt{3})^2 = 3)$$
   $$\operatorname{tr}(C_6) = 3 - 2 = 1 = 2\cos(2\pi/6), \quad (B_1 B_2)^3 = -I_2, \quad (B_1 B_2)^6 = I_2$$

3. **Semilinear Galois Transport & Commuting Square**:
   Every ring endomorphism $\sigma : R \to+* R$ acts coefficientwise on matrices $\operatorname{End}(V)$
   preserving matrix multiplication, powers, nilpotency, and Artin braid equalities.
-/

variable {R : Type*} [CommRing R]

/-- The 10th cyclotomic polynomial $\Phi_{10}(X) = X^4 - X^3 + X^2 - X + 1$. -/
def cyclotomic10 (zeta : R) : R := zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1

/-- The 12th cyclotomic polynomial $\Phi_{12}(X) = X^4 - X^2 + 1$. -/
def cyclotomic12 (zeta : R) : R := zeta ^ 4 - zeta ^ 2 + 1

/-- Universal quantum two generator $d_m = [2]_q = \zeta + \zeta^{-1}$. -/
def quantumTwo (zeta zeta_inv : R) : R := zeta + zeta_inv

/-! ### Sector 1: $m = 5$ (Fibonacci / Golden Ratio $\phi$) -/

/-- 🏆 THEOREM 1: For roots of $\Phi_{10}(\zeta) = 0$, the quantum integer $d_5 = \zeta + \zeta^{-1}$ satisfies
    the exact Golden Ratio polynomial identity $d_5^2 = d_5 + 1$. -/
theorem I2Five_quantumDimension_golden (zeta zeta_inv : R)
    (h_inv : zeta * zeta_inv = 1)
    (h_phi10 : cyclotomic10 zeta = 0) :
    (quantumTwo zeta zeta_inv) ^ 2 = quantumTwo zeta zeta_inv + 1 := by
  dsimp [quantumTwo, cyclotomic10] at *
  have h_exp : (zeta + zeta_inv) ^ 2 - (zeta + zeta_inv) - 1 =
      (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1) := by
    have h1 : (zeta + zeta_inv) ^ 2 - (zeta + zeta_inv) - 1 =
        zeta ^ 2 + zeta_inv ^ 2 + 2 * (zeta * zeta_inv) - zeta - zeta_inv - 1 := by ring
    have h2 : (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1) =
        (zeta * zeta_inv) ^ 2 * zeta ^ 2 - (zeta * zeta_inv) ^ 2 * zeta +
        (zeta * zeta_inv) ^ 2 - (zeta * zeta_inv) * zeta_inv + zeta_inv ^ 2 := by ring
    rw [h1, h2, h_inv]
    ring
  have h_zero : (zeta + zeta_inv) ^ 2 - (zeta + zeta_inv) - 1 = 0 := by
    rw [h_exp, h_phi10, mul_zero]
  linear_combination h_zero

/-! ### Sector 2: $m = 6$ ($G_2$ Root Length Ratio $\sqrt{3}$) -/

/-- 🏆 THEOREM 2: For roots of $\Phi_{12}(\zeta) = 0$, the quantum integer $d_6 = \zeta + \zeta^{-1}$ satisfies
    the exact root-three identity $d_6^2 = 3$. -/
theorem I2Six_quantumDimension_sq_three (zeta zeta_inv : R)
    (h_inv : zeta * zeta_inv = 1)
    (h_phi12 : cyclotomic12 zeta = 0) :
    (quantumTwo zeta zeta_inv) ^ 2 = 3 := by
  dsimp [quantumTwo, cyclotomic12] at *
  have h_exp : (zeta + zeta_inv) ^ 2 - 3 =
      (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 2 + 1) := by
    have h1 : (zeta + zeta_inv) ^ 2 - 3 =
        zeta ^ 2 + zeta_inv ^ 2 + 2 * (zeta * zeta_inv) - 3 := by ring
    have h2 : (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 2 + 1) =
        (zeta * zeta_inv) ^ 2 * zeta ^ 2 - (zeta * zeta_inv) ^ 2 + zeta_inv ^ 2 := by ring
    rw [h1, h2, h_inv]
    ring
  have h_zero : (zeta + zeta_inv) ^ 2 - 3 = 0 := by
    rw [h_exp, h_phi12, mul_zero]
  linear_combination h_zero

/-! ### Generic 2D Cartan Artin Reflection Representation -/

/-- Generic 2D Cartan reflection $B_1(d)$. -/
def B1Cartan (d : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![-1, d],
    ![ 0, 1]]

/-- Generic 2D Cartan reflection $B_2(d)$. -/
def B2Cartan (d : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![ 1,  0],
    ![ d, -1]]

/-- Product of Cartan reflections $C(d) = B_1(d) B_2(d)$. -/
def CCartan (d : R) : Matrix (Fin 2) (Fin 2) R :=
  B1Cartan d * B2Cartan d

private theorem fin2_mul_eq (A B C : Matrix (Fin 2) (Fin 2) R)
    (h00 : (A * B) 0 0 = C 0 0)
    (h01 : (A * B) 0 1 = C 0 1)
    (h10 : (A * B) 1 0 = C 1 0)
    (h11 : (A * B) 1 1 = C 1 1) :
    A * B = C := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

private theorem CCartan_eq_explicit (d : R) :
    CCartan d = ![![d ^ 2 - 1, -d], ![d, -1]] := by
  have h := Matrix.two_mul_expl (B1Cartan d) (B2Cartan d)
  apply fin2_mul_eq
  · convert h.1 using 1 <;> simp [B1Cartan, B2Cartan, pow_two] <;> ring
  · convert h.2.1 using 1 <;> simp [B1Cartan, B2Cartan, pow_two] <;> ring
  · convert h.2.2.1 using 1 <;> simp [B1Cartan, B2Cartan, pow_two] <;> ring
  · convert h.2.2.2 using 1 <;> simp [B1Cartan, B2Cartan, pow_two] <;> ring

/-- 🏆 THEOREM 3: The Coxeter product trace is $\operatorname{tr}(C(d)) = d^2 - 2$. -/
theorem CCartan_trace (d : R) :
    Matrix.trace (CCartan d) = d ^ 2 - 2 := by
  rw [CCartan_eq_explicit]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  ring

/-- 🏆 THEOREM 4: For $m=6$ ($d^2 = 3$), $C^3 = -I$ and $C^6 = I$. -/
theorem CCartan_six_order (d : R) (hd : d ^ 2 = 3) :
    (CCartan d) ^ 3 = -1 ∧ (CCartan d) ^ 6 = 1 := by
  have hC := CCartan_eq_explicit d
  let M : Matrix (Fin 2) (Fin 2) R := ![![d ^ 2 - 1, -d], ![d, -1]]
  have hM2 : M ^ 2 = M - 1 := by
    rw [pow_two]
    have h := Matrix.two_mul_expl M M
    apply fin2_mul_eq
    · calc
        (M * M) 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 := h.1
        _ = M 0 0 - 1 := by
          simp [M, pow_two]
          linear_combination (d ^ 2 - 1) * hd
        _ = (M - 1) 0 0 := by simp [Matrix.sub_apply, Matrix.one_apply]
    · calc
        (M * M) 0 1 = M 0 0 * M 0 1 + M 0 1 * M 1 1 := h.2.1
        _ = M 0 1 := by
          simp [M]
          linear_combination (-d) * hd
        _ = (M - 1) 0 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
    · calc
        (M * M) 1 0 = M 1 0 * M 0 0 + M 1 1 * M 1 0 := h.2.2.1
        _ = M 1 0 := by
          simp [M]
          linear_combination d * hd
        _ = (M - 1) 1 0 := by simp [Matrix.sub_apply, Matrix.one_apply]
    · calc
        (M * M) 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 := h.2.2.2
        _ = M 1 1 - 1 := by
          simp [M]
          linear_combination -hd
        _ = (M - 1) 1 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have hM3 : M ^ 3 = -1 := by
    calc
      M ^ 3 = M ^ 2 * M := by rw [pow_succ]
      _ = (M - 1) * M := by rw [hM2]
      _ = M * M - 1 * M := by rw [Matrix.sub_mul]
      _ = M ^ 2 - M := by rw [one_mul, pow_two]
      _ = (M - 1) - M := by rw [hM2]
      _ = -1 := by ext i j; fin_cases i <;> fin_cases j <;> simp
  have h3 : (CCartan d) ^ 3 = -1 := by
    rw [hC]
    exact hM3
  constructor
  · exact h3
  · have h6 : (CCartan d) ^ 6 = ((CCartan d) ^ 3) ^ 2 := by
      have : (3 : ℕ) * 2 = 6 := rfl
      rw [← pow_mul, this]
    rw [h6, h3]
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 5: For $m=5$ ($d^2 = d + 1$), the Coxeter product has order 5: $(B_1 B_2)^5 = I$. -/
theorem CCartan_five_order (d : R) (hd : d ^ 2 = d + 1) :
    (CCartan d) ^ 5 = 1 := by
  have hC := CCartan_eq_explicit d
  let M : Matrix (Fin 2) (Fin 2) R := ![![d ^ 2 - 1, -d], ![d, -1]]
  have hd3 : d ^ 3 = 2 * d + 1 := by
    calc
      d ^ 3 = d ^ 2 * d := by rw [pow_succ]
      _ = (d + 1) * d := by rw [hd]
      _ = d ^ 2 + d := by ring
      _ = (d + 1) + d := by rw [hd]
      _ = 2 * d + 1 := by ring
  have hd4 : d ^ 4 = 3 * d + 2 := by
    calc
      d ^ 4 = d ^ 3 * d := by rw [pow_succ]
      _ = (2 * d + 1) * d := by rw [hd3]
      _ = 2 * d ^ 2 + d := by ring
      _ = 2 * (d + 1) + d := by rw [hd]
      _ = 3 * d + 2 := by ring
  have hd_sub : d ^ 2 - d = 1 := by rw [hd]; ring
  have hd_flip : d - d ^ 2 = -1 := by
    calc
      d - d ^ 2 = -(d ^ 2 - d) := by ring
      _ = -1 := by rw [hd_sub]
  have hd_sq_sub_one : d ^ 2 - 1 = d := by rw [hd]; ring
  have hd_mul_sub : d * d - d = 1 := by simpa only [pow_two] using hd_sub
  have hd_sub_mul : d - d * d = -1 := by simpa only [pow_two] using hd_flip
  have hd_mul_sq_sub_one : d * d - 1 = d := by
    simpa only [pow_two] using hd_sq_sub_one
  have hd_cube_reduce : -d ^ 3 + 2 * d ^ 2 = 1 := by
    rw [hd3, hd]
    ring
  let M2 : Matrix (Fin 2) (Fin 2) R := ![![0, -1], ![1, -d]]
  let M3 : Matrix (Fin 2) (Fin 2) R := ![![-d, 1], ![-1, 0]]
  let M4 : Matrix (Fin 2) (Fin 2) R := ![![-1, d], ![-d, d]]
  have hM2 : M ^ 2 = M2 := by
    rw [pow_two]
    have h := Matrix.two_mul_expl M M
    apply fin2_mul_eq
    · calc
        (M * M) 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 := h.1
        _ = 0 := by simp [M, hd_sq_sub_one]
        _ = M2 0 0 := by simp [M2]
    · calc
        (M * M) 0 1 = M 0 0 * M 0 1 + M 0 1 * M 1 1 := h.2.1
        _ = -1 := by
          simp [M, hd_sq_sub_one]
          calc
            -(d * d) + d = d - d ^ 2 := by rw [pow_two]; ring
            _ = -1 := hd_flip
        _ = M2 0 1 := by simp [M2]
    · calc
        (M * M) 1 0 = M 1 0 * M 0 0 + M 1 1 * M 1 0 := h.2.2.1
        _ = 1 := by
          simp [M, hd_sq_sub_one]
          calc
            d * d + -d = d ^ 2 - d := by rw [pow_two]; ring
            _ = 1 := hd_sub
        _ = M2 1 0 := by simp [M2]
    · calc
        (M * M) 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 := h.2.2.2
        _ = -d := by
          simp [M]
          calc
            -(d * d) + 1 = -(d ^ 2) + 1 := by rw [pow_two]
            _ = -d := by rw [hd]; ring
        _ = M2 1 1 := by simp [M2]
  have hM3 : M2 * M = M3 := by
    have h := Matrix.two_mul_expl M2 M
    apply fin2_mul_eq
    · calc
        (M2 * M) 0 0 = M2 0 0 * M 0 0 + M2 0 1 * M 1 0 := h.1
        _ = -d := by simp [M, M2]
        _ = M3 0 0 := by simp [M3]
    · calc
        (M2 * M) 0 1 = M2 0 0 * M 0 1 + M2 0 1 * M 1 1 := h.2.1
        _ = 1 := by simp [M, M2]
        _ = M3 0 1 := by simp [M3]
    · calc
        (M2 * M) 1 0 = M2 1 0 * M 0 0 + M2 1 1 * M 1 0 := h.2.2.1
        _ = -1 := by
          simp [M, M2]
          rw [hd_sq_sub_one]
          simpa [sub_eq_add_neg] using hd_sub_mul
        _ = M3 1 0 := by simp [M3]
    · calc
        (M2 * M) 1 1 = M2 1 0 * M 0 1 + M2 1 1 * M 1 1 := h.2.2.2
        _ = 0 := by simp [M, M2]
        _ = M3 1 1 := by simp [M3]
  have hM4 : M3 * M = M4 := by
    have h := Matrix.two_mul_expl M3 M
    apply fin2_mul_eq
    · calc
        (M3 * M) 0 0 = M3 0 0 * M 0 0 + M3 0 1 * M 1 0 := h.1
        _ = -1 := by
          simp [M, M3]
          rw [hd_sq_sub_one]
          calc
            -(d * d) + d = d - d * d := by ring
            _ = -1 := hd_sub_mul
        _ = M4 0 0 := by simp [M4]
    · calc
        (M3 * M) 0 1 = M3 0 0 * M 0 1 + M3 0 1 * M 1 1 := h.2.1
        _ = d := by
          simp [M, M3]
          simpa [sub_eq_add_neg] using hd_mul_sq_sub_one
        _ = M4 0 1 := by simp [M4]
    · calc
        (M3 * M) 1 0 = M3 1 0 * M 0 0 + M3 1 1 * M 1 0 := h.2.2.1
        _ = -d := by simp [M, M3, hd_sq_sub_one]
        _ = M4 1 0 := by simp [M4]
    · calc
        (M3 * M) 1 1 = M3 1 0 * M 0 1 + M3 1 1 * M 1 1 := h.2.2.2
        _ = d := by simp [M, M3]
        _ = M4 1 1 := by simp [M4]
  have hM5 : M4 * M = 1 := by
    have h := Matrix.two_mul_expl M4 M
    apply fin2_mul_eq
    · calc
        (M4 * M) 0 0 = M4 0 0 * M 0 0 + M4 0 1 * M 1 0 := h.1
        _ = 1 := by
          simp [M, M4]
          calc
            1 - d ^ 2 + d * d = 1 - d ^ 2 + d ^ 2 := by rw [pow_two]
            _ = 1 := by ring
        _ = (1 : Matrix (Fin 2) (Fin 2) R) 0 0 := by simp
    · calc
        (M4 * M) 0 1 = M4 0 0 * M 0 1 + M4 0 1 * M 1 1 := h.2.1
        _ = 0 := by simp [M, M4]
        _ = (1 : Matrix (Fin 2) (Fin 2) R) 0 1 := by simp
    · calc
        (M4 * M) 1 0 = M4 1 0 * M 0 0 + M4 1 1 * M 1 0 := h.2.2.1
        _ = 0 := by simp [M, M4, hd_sq_sub_one]
        _ = (1 : Matrix (Fin 2) (Fin 2) R) 1 0 := by simp
    · calc
        (M4 * M) 1 1 = M4 1 0 * M 0 1 + M4 1 1 * M 1 1 := h.2.2.2
        _ = 1 := by
          simp [M, M4]
          calc
            d * d + -d = d ^ 2 - d := by rw [pow_two]; ring
            _ = 1 := hd_sub
        _ = (1 : Matrix (Fin 2) (Fin 2) R) 1 1 := by simp
  have hM3pow : M ^ 3 = M3 := by
    rw [pow_succ, hM2]
    exact hM3
  have hM4pow : M ^ 4 = M4 := by
    rw [pow_succ, hM3pow]
    exact hM4
  have hM5pow : M ^ 5 = 1 := by
    rw [pow_succ, hM4pow]
    exact hM5
  rw [hC]
  change M ^ 5 = 1
  exact hM5pow

/-! ### Semilinear Galois Transport on the Operator Carrier -/

/-- Coefficientwise Galois mapping on matrix operators. -/
def matrixGaloisMap (σ : R →+* R) (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.map M σ

/-- 🏆 THEOREM 6 (Multiplicativity of Semilinear Matrix Transport):
    $$\sigma(M_1 M_2) = \sigma(M_1) \sigma(M_2)$$ -/
theorem matrixGaloisMap_mul (σ : R →+* R) (M1 M2 : Matrix (Fin 2) (Fin 2) R) :
    matrixGaloisMap σ (M1 * M2) = matrixGaloisMap σ M1 * matrixGaloisMap σ M2 := by
  ext i j
  dsimp [matrixGaloisMap]
  simp [Matrix.mul_apply, map_mul]

theorem matrixGaloisMap_commutator
    (σ : R →+* R) (M1 M2 : Matrix (Fin 2) (Fin 2) R) :
    matrixGaloisMap σ (M1 * M2 - M2 * M1) =
      matrixGaloisMap σ M1 * matrixGaloisMap σ M2 -
        matrixGaloisMap σ M2 * matrixGaloisMap σ M1 := by
  ext i j
  simp [matrixGaloisMap, Matrix.mul_apply, map_sub, map_mul]

theorem matrixGaloisMap_anticommutator
    (σ : R →+* R) (M1 M2 : Matrix (Fin 2) (Fin 2) R) :
    matrixGaloisMap σ (M1 * M2 + M2 * M1) =
      matrixGaloisMap σ M1 * matrixGaloisMap σ M2 +
        matrixGaloisMap σ M2 * matrixGaloisMap σ M1 := by
  ext i j
  simp [matrixGaloisMap, Matrix.mul_apply, map_add, map_mul]

/-- 🏆 THEOREM 7 (Identity Preservation):
    $$\sigma(I) = I$$ -/
theorem matrixGaloisMap_one (σ : R →+* R) :
    matrixGaloisMap σ (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  dsimp [matrixGaloisMap]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- 🏆 THEOREM 8 (Power Preservation):
    $$\sigma(M^n) = (\sigma(M))^n$$ -/
theorem matrixGaloisMap_pow (σ : R →+* R) (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    matrixGaloisMap σ (M ^ n) = (matrixGaloisMap σ M) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, matrixGaloisMap_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, matrixGaloisMap_mul, ih]

/-- 🏆 THEOREM 9 (Semilinear Scalar Action):
    $$\sigma(c \cdot M) = \sigma(c) \cdot \sigma(M)$$ -/
theorem matrixGaloisMap_smul (σ : R →+* R) (c : R) (M : Matrix (Fin 2) (Fin 2) R) :
    matrixGaloisMap σ (c • M) = σ c • matrixGaloisMap σ M := by
  ext i j
  dsimp [matrixGaloisMap]
  simp

/-- 🏆 THEOREM 10 (Artin-Galois Commuting Square for Braid Relation):
    If $B_1, B_2$ satisfy the braid relation $(B_1 B_2)^m = (B_2 B_1)^m$,
    then so do their semilinear Galois transports $\sigma(B_1), \sigma(B_2)$:
    $$(\sigma(B_1) \sigma(B_2))^m = (\sigma(B_2) \sigma(B_1))^m$$ -/
theorem matrixGaloisMap_artin_braid (σ : R →+* R) (B1 B2 : Matrix (Fin 2) (Fin 2) R) (m : ℕ)
    (h_artin : (B1 * B2) ^ m = (B2 * B1) ^ m) :
    (matrixGaloisMap σ B1 * matrixGaloisMap σ B2) ^ m =
      (matrixGaloisMap σ B2 * matrixGaloisMap σ B1) ^ m := by
  rw [← matrixGaloisMap_mul, ← matrixGaloisMap_mul, ← matrixGaloisMap_pow, ← matrixGaloisMap_pow, h_artin]

end InfoGeometry.QuantumAlgebra.RankTwoCyclotomicArtinBridge
