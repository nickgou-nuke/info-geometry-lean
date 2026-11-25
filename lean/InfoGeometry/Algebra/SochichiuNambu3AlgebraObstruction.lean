/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Nambu–Lie 3-Algebra Matrix Obstructions (Sochichiu `arXiv:0806.3520v2`)

Formalizes the matrix Nambu–Lie 3-commutator `[A, B, C]_N`, its reduction on a constant
eigenspace of `T_D` and via the deformed Lie bracket (Sochichiu §2.2 & §2.4),
the 3-algebra Schur's Lemma (Lemma 1: zero central/Casimir elements in any non-abelian
representation), the constant-`T₄` quartic obstruction `t₄⁴ = -c₂` for Euclidean `A₄`,
the universal all-dimension `n × n` Hermitian no-go theorem proving every finite-dimensional
Hermitian representation of Euclidean `A₄` is identically zero, and an explicit nonzero
`2 × 2` Hermitian Pauli representation of Lorentzian `A_{3,1}` showing sharpness.
-/

set_option autoImplicit false

noncomputable section

open Matrix Complex

namespace InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction

/-- Associator-induced matrix Lie commutator `[A, B] = A * B - B * A`. -/
def lieComm {R : Type*} [Ring R] (A B : R) : R :=
  A * B - B * A

/-- Associative Nambu–Lie 3-commutator
`[A, B, C]_N = A B C - A C B + B C A - B A C + C A B - C B A`. -/
def nambu3 {R : Type*} [Ring R] (A B C : R) : R :=
  A * B * C - A * C * B + B * C * A - B * A * C + C * A * B - C * B * A

/-- Cyclic decomposition `[A, B, C]_N = A [B, C] + B [C, A] + C [A, B]`. -/
theorem nambu3_eq_sum_comm {R : Type*} [Ring R] (A B C : R) :
    nambu3 A B C = A * lieComm B C + B * lieComm C A + C * lieComm A B := by
  unfold nambu3 lieComm
  noncomm_ring

/-- Antisymmetry in the first two arguments: `[A, B, C]_N = -[B, A, C]_N`. -/
theorem nambu3_antisymm_12 {R : Type*} [Ring R] (A B C : R) :
    nambu3 A B C = -nambu3 B A C := by
  unfold nambu3
  noncomm_ring

/-- Antisymmetry in the last two arguments: `[A, B, C]_N = -[A, C, B]_N`. -/
theorem nambu3_antisymm_23 {R : Type*} [Ring R] (A B C : R) :
    nambu3 A B C = -nambu3 A C B := by
  unfold nambu3
  noncomm_ring

/-- Cyclic invariance: `[A, B, C]_N = [B, C, A]_N`. -/
theorem nambu3_cyclic {R : Type*} [Ring R] (A B C : R) :
    nambu3 A B C = nambu3 B C A := by
  unfold nambu3
  noncomm_ring

/-- Sochichiu Eq. (2.7): on a scalar subspace `T_D = t • 1`, `[t • 1, X, Y]_N = t • [X, Y]`. -/
theorem nambu3_smul_one_left {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (t : R) (X Y : A) :
    nambu3 (t • (1 : A)) X Y = t • lieComm X Y := by
  unfold nambu3 lieComm
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [Algebra.smul_def t (X * Y - Y * X), Algebra.smul_def t (X * Y),
    Algebra.smul_def t (Y * X)]
  noncomm_ring

/-- Sochichiu Eq. (2.21): nonconstant `T` reduction via the deformed bracket
`[T, X, Y]_N = T [X, Y] + [X, Y] T - X T Y + Y T X`. -/
theorem nambu3_eq_deformed_bracket {R : Type*} [Ring R] (T X Y : R) :
    nambu3 T X Y = T * lieComm X Y + lieComm X Y * T - X * T * Y + Y * T * X := by
  unfold nambu3 lieComm
  noncomm_ring

/-- Commuting reduction: if `T` commutes with `X` and `Y`, then `[T, X, Y]_N = T [X, Y]`. -/
theorem nambu3_of_comm_left {R : Type*} [Ring R] (T X Y : R)
    (hTX : T * X = X * T) (hTY : T * Y = Y * T) :
    nambu3 T X Y = T * lieComm X Y := by
  unfold nambu3 lieComm
  have hXYT : X * Y * T = T * X * Y := by
    calc
      X * Y * T = X * (Y * T) := mul_assoc _ _ _
      _ = X * (T * Y) := by rw [← hTY]
      _ = (X * T) * Y := (mul_assoc _ _ _).symm
      _ = T * X * Y := by rw [← hTX]
  have hXTY : X * T * Y = T * X * Y := by rw [← hTX]
  have hYTX : Y * T * X = T * Y * X := by rw [← hTY]
  have hYXT : Y * X * T = T * Y * X := by
    calc
      Y * X * T = Y * (X * T) := mul_assoc _ _ _
      _ = Y * (T * X) := by rw [← hTX]
      _ = (Y * T) * X := (mul_assoc _ _ _).symm
      _ = T * Y * X := by rw [← hTY]
  rw [hXYT, hXTY, hYTX, hYXT]
  noncomm_ring

/-- Sochichiu Lemma 1 (central form): if `X` commutes with `A` and `B`,
then `[A, B, X]_N = [A, B] * X`. -/
theorem sochichiu_lemma1_central_mul {R : Type*} [Ring R] (A B X : R)
    (hXA : X * A = A * X) (hXB : X * B = B * X) :
    nambu3 A B X = lieComm A B * X := by
  rw [nambu3_cyclic A B X, nambu3_cyclic B X A]
  rw [nambu3_of_comm_left X A B hXA hXB]
  unfold lieComm
  calc
    X * (A * B - B * A) = (X * A) * B - (X * B) * A := by noncomm_ring
    _ = (A * X) * B - (B * X) * A := by rw [hXA, hXB]
    _ = A * (X * B) - B * (X * A) := by simp only [mul_assoc]
    _ = A * (B * X) - B * (A * X) := by rw [hXB, hXA]
    _ = (A * B - B * A) * X := by noncomm_ring

/-- **Sochichiu Lemma 1 (3-Algebra Schur's Lemma)**:
In any nontrivial algebra over a field `K`, any scalar central element `X = c • 1` that
Nambu-commutes with a non-commuting pair `[A, B] ≠ 0` must vanish (`c = 0`). -/
theorem sochichiu_lemma1_scalar_zero {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (c : K) (A₁ A₂ : A) (hNonAbelian : lieComm A₁ A₂ ≠ 0)
    (hCent : nambu3 A₁ A₂ (c • (1 : A)) = 0) :
    c = 0 := by
  have h1 : nambu3 A₁ A₂ (c • (1 : A)) = c • lieComm A₁ A₂ := by
    rw [nambu3_cyclic A₁ A₂ (c • 1), nambu3_cyclic A₂ (c • 1) A₁]
    exact nambu3_smul_one_left c A₁ A₂
  rw [h1, smul_eq_zero] at hCent
  rcases hCent with hc | h0
  · exact hc
  · exact absurd h0 hNonAbelian

/-- **Sochichiu §2.3 Euclidean `A₄` Constant-`T₄` Quartic Constraint (Eq. 2.20)**:
If `T₄ = t₄ • 1` (`t₄ ≠ 0`), `[Tᵢ, Tⱼ] = (-I / t₄) • T_k`, Casimir
`(t₄ • T₁)² + (t₄ • T₂)² + (t₄ • T₃)² = (c₂ : ℂ) • 1`, and `[T₁, T₂, T₃]_N = I • T₄`,
then `t₄ ^ 4 = -(c₂ : ℂ)`. -/
theorem sochichiu_A4_quartic_constraint {A : Type*} [Ring A] [Algebra ℂ A] [Nontrivial A]
    (T₁ T₂ T₃ : A) (t₄ : ℂ) (c₂ : ℝ) (ht₄ : t₄ ≠ 0)
    (h12 : lieComm T₁ T₂ = (-I / t₄) • T₃)
    (h23 : lieComm T₂ T₃ = (-I / t₄) • T₁)
    (h31 : lieComm T₃ T₁ = (-I / t₄) • T₂)
    (hCas : (t₄ • T₁) * (t₄ • T₁) + (t₄ • T₂) * (t₄ • T₂) + (t₄ • T₃) * (t₄ • T₃) =
      (c₂ : ℂ) • (1 : A))
    (hNambu : nambu3 T₁ T₂ T₃ = I • (t₄ • (1 : A))) :
    t₄ ^ 4 = -(c₂ : ℂ) := by
  have hSumSq : (t₄ ^ 2) • (T₁ * T₁ + T₂ * T₂ + T₃ * T₃) = (c₂ : ℂ) • (1 : A) := by
    have hEq : (t₄ • T₁) * (t₄ • T₁) + (t₄ • T₂) * (t₄ • T₂) + (t₄ • T₃) * (t₄ • T₃) =
        (t₄ ^ 2) • (T₁ * T₁ + T₂ * T₂ + T₃ * T₃) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_add, sq]
    rwa [hEq] at hCas
  have hLHS : nambu3 T₁ T₂ T₃ = (-I / t₄) • (T₁ * T₁ + T₂ * T₂ + T₃ * T₃) := by
    rw [nambu3_eq_sum_comm, h23, h31, h12]
    simp only [mul_smul_comm, ← smul_add]
  rw [hLHS] at hNambu
  have hScaled := congrArg (fun x : A => (t₄ ^ 3) • x) hNambu
  have hL : (t₄ ^ 3) • ((-I / t₄) • (T₁ * T₁ + T₂ * T₂ + T₃ * T₃)) =
      (-I) • ((t₄ ^ 2) • (T₁ * T₁ + T₂ * T₂ + T₃ * T₃)) := by
    rw [smul_smul, smul_smul]
    congr 1
    field_simp [ht₄]
  have hR : (t₄ ^ 3) • (I • (t₄ • (1 : A))) = (I * t₄ ^ 4) • (1 : A) := by
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [hL, hR, hSumSq, smul_smul] at hScaled
  have hDiff : (I * (t₄ ^ 4 + (c₂ : ℂ))) • (1 : A) = 0 := by
    have h0 := sub_eq_zero.mpr hScaled
    rw [← sub_smul] at h0
    have hEqCoeff : -I * (c₂ : ℂ) - I * t₄ ^ 4 = -(I * (t₄ ^ 4 + (c₂ : ℂ))) := by ring
    rw [hEqCoeff, neg_smul, neg_eq_zero] at h0
    exact h0
  rw [Algebra.smul_def, mul_one] at hDiff
  have hZero : I * (t₄ ^ 4 + (c₂ : ℂ)) = 0 :=
    (injective_iff_map_eq_zero (algebraMap ℂ A)).mp (RingHom.injective (algebraMap ℂ A)) _ hDiff
  have hFac : t₄ ^ 4 + (c₂ : ℂ) = 0 := by
    rcases mul_eq_zero.mp hZero with hI | hRest
    · exact absurd hI I_ne_zero
    · exact hRest
  exact eq_neg_of_add_eq_zero_left hFac

/-- When the spin Casimir `c₂ > 0`, no real eigenvalue `t₄ ∈ ℝ` satisfies `t₄ ^ 4 = -c₂`. -/
theorem sochichiu_A4_no_real_eigenvalue (t₄ : ℂ) (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hq : t₄ ^ 4 = -(c₂ : ℂ)) :
    ¬ ∃ r : ℝ, t₄ = (r : ℂ) := by
  rintro ⟨r, rfl⟩
  have hre := congrArg Complex.re hq
  have hpow : ((r : ℂ) ^ 4).re = r ^ 4 := by
    norm_cast
  rw [hpow] at hre
  have hcneg : (-(c₂ : ℂ)).re = -c₂ := by simp
  rw [hcneg] at hre
  have hr4 : 0 ≤ r ^ 4 := by
    have : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [this]
    exact sq_nonneg (r ^ 2)
  linarith [hr4, hc₂, hre]

/-- **Universal Matrix Trace Identity for Alternating Nambu Brackets**:
For arbitrary matrices `T₁, T₂, T₃, T₄` of any finite dimension `n`,
`Tr(T₄ [T₁,T₂,T₃]_N) - Tr(T₁ [T₂,T₃,T₄]_N) + Tr(T₂ [T₃,T₄,T₁]_N) - Tr(T₃ [T₄,T₁,T₂]_N) = 0`. -/
theorem trace_alternating_nambu3_eq_zero {R : Type*} [CommRing R] {n : ℕ}
    (T₁ T₂ T₃ T₄ : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (T₄ * nambu3 T₁ T₂ T₃) - Matrix.trace (T₁ * nambu3 T₂ T₃ T₄) +
      Matrix.trace (T₂ * nambu3 T₃ T₄ T₁) - Matrix.trace (T₃ * nambu3 T₄ T₁ T₂) = 0 := by
  unfold nambu3
  simp only [mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub, ← Matrix.mul_assoc]
  -- Canonicalize all 24 traces so `T₁` sits at the front via `Matrix.trace_mul_comm`.
  have cyc3 : ∀ A B C D : Matrix (Fin n) (Fin n) R,
      Matrix.trace (A * B * C * D) = Matrix.trace (D * A * B * C) := fun A B C D => by
    rw [Matrix.trace_mul_comm (A * B * C) D]
    simp only [Matrix.mul_assoc]
  -- Move `T₁` to leading position in every term of the 4 cyclic blocks.
  have c_4123 : Matrix.trace (T₄ * T₁ * T₂ * T₃) = Matrix.trace (T₁ * T₂ * T₃ * T₄) := by
    simpa [Matrix.mul_assoc] using (cyc3 T₁ T₂ T₃ T₄).symm
  have c_4132 : Matrix.trace (T₄ * T₁ * T₃ * T₂) = Matrix.trace (T₁ * T₃ * T₂ * T₄) := by
    simpa [Matrix.mul_assoc] using (cyc3 T₁ T₃ T₂ T₄).symm
  have c_4231 : Matrix.trace (T₄ * T₂ * T₃ * T₁) = Matrix.trace (T₁ * T₄ * T₂ * T₃) := by
    simpa [Matrix.mul_assoc] using cyc3 T₄ T₂ T₃ T₁
  have c_4213 : Matrix.trace (T₄ * T₂ * T₁ * T₃) = Matrix.trace (T₁ * T₃ * T₄ * T₂) := by
    calc
      Matrix.trace (T₄ * T₂ * T₁ * T₃) = Matrix.trace (T₃ * T₄ * T₂ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₃ * T₄ * T₂) := cyc3 _ _ _ _
  have c_4312 : Matrix.trace (T₄ * T₃ * T₁ * T₂) = Matrix.trace (T₁ * T₂ * T₄ * T₃) := by
    calc
      Matrix.trace (T₄ * T₃ * T₁ * T₂) = Matrix.trace (T₂ * T₄ * T₃ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₂ * T₄ * T₃) := cyc3 _ _ _ _
  have c_4321 : Matrix.trace (T₄ * T₃ * T₂ * T₁) = Matrix.trace (T₁ * T₄ * T₃ * T₂) := by
    simpa [Matrix.mul_assoc] using cyc3 T₄ T₃ T₂ T₁
  have c_2341 : Matrix.trace (T₂ * T₃ * T₄ * T₁) = Matrix.trace (T₁ * T₂ * T₃ * T₄) := by
    simpa [Matrix.mul_assoc] using cyc3 T₂ T₃ T₄ T₁
  have c_2314 : Matrix.trace (T₂ * T₃ * T₁ * T₄) = Matrix.trace (T₁ * T₄ * T₂ * T₃) := by
    calc
      Matrix.trace (T₂ * T₃ * T₁ * T₄) = Matrix.trace (T₄ * T₂ * T₃ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₄ * T₂ * T₃) := cyc3 _ _ _ _
  have c_2413 : Matrix.trace (T₂ * T₄ * T₁ * T₃) = Matrix.trace (T₁ * T₃ * T₂ * T₄) := by
    calc
      Matrix.trace (T₂ * T₄ * T₁ * T₃) = Matrix.trace (T₃ * T₂ * T₄ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₃ * T₂ * T₄) := cyc3 _ _ _ _
  have c_2431 : Matrix.trace (T₂ * T₄ * T₃ * T₁) = Matrix.trace (T₁ * T₂ * T₄ * T₃) := by
    simpa [Matrix.mul_assoc] using cyc3 T₂ T₄ T₃ T₁
  have c_2134 : Matrix.trace (T₂ * T₁ * T₃ * T₄) = Matrix.trace (T₁ * T₃ * T₄ * T₂) := by
    calc
      Matrix.trace (T₂ * T₁ * T₃ * T₄) = Matrix.trace (T₄ * T₂ * T₁ * T₃) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₃ * T₄ * T₂) := c_4213
  have c_2143 : Matrix.trace (T₂ * T₁ * T₄ * T₃) = Matrix.trace (T₁ * T₄ * T₃ * T₂) := by
    calc
      Matrix.trace (T₂ * T₁ * T₄ * T₃) = Matrix.trace (T₃ * T₂ * T₁ * T₄) := cyc3 _ _ _ _
      _ = Matrix.trace (T₄ * T₃ * T₂ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₄ * T₃ * T₂) := c_4321
  have c_3412 : Matrix.trace (T₃ * T₄ * T₁ * T₂) = Matrix.trace (T₁ * T₂ * T₃ * T₄) := by
    calc
      Matrix.trace (T₃ * T₄ * T₁ * T₂) = Matrix.trace (T₂ * T₃ * T₄ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₂ * T₃ * T₄) := c_2341
  have c_3421 : Matrix.trace (T₃ * T₄ * T₂ * T₁) = Matrix.trace (T₁ * T₃ * T₄ * T₂) := by
    simpa [Matrix.mul_assoc] using cyc3 T₃ T₄ T₂ T₁
  have c_3124 : Matrix.trace (T₃ * T₁ * T₂ * T₄) = Matrix.trace (T₁ * T₂ * T₄ * T₃) := by
    calc
      Matrix.trace (T₃ * T₁ * T₂ * T₄) = Matrix.trace (T₄ * T₃ * T₁ * T₂) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₂ * T₄ * T₃) := c_4312
  have c_3142 : Matrix.trace (T₃ * T₁ * T₄ * T₂) = Matrix.trace (T₁ * T₄ * T₂ * T₃) := by
    calc
      Matrix.trace (T₃ * T₁ * T₄ * T₂) = Matrix.trace (T₂ * T₃ * T₁ * T₄) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₄ * T₂ * T₃) := c_2314
  have c_3241 : Matrix.trace (T₃ * T₂ * T₄ * T₁) = Matrix.trace (T₁ * T₃ * T₂ * T₄) := by
    simpa [Matrix.mul_assoc] using cyc3 T₃ T₂ T₄ T₁
  have c_3214 : Matrix.trace (T₃ * T₂ * T₁ * T₄) = Matrix.trace (T₁ * T₄ * T₃ * T₂) := by
    calc
      Matrix.trace (T₃ * T₂ * T₁ * T₄) = Matrix.trace (T₄ * T₃ * T₂ * T₁) := cyc3 _ _ _ _
      _ = Matrix.trace (T₁ * T₄ * T₃ * T₂) := c_4321
  rw [c_4123, c_4132, c_4231, c_4213, c_4312, c_4321,
    c_2341, c_2314, c_2413, c_2431, c_2134, c_2143,
    c_3412, c_3421, c_3124, c_3142, c_3241, c_3214]
  ring

private lemma trace_mul_self_re_of_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    (Matrix.trace (A * A)).re = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) := by
  have htr : Matrix.trace (A * A) = ∑ i : Fin n, ∑ j : Fin n, ((Complex.normSq (A i j) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hji : A j i = star (A i j) := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j i) hA.eq
      simpa using h.symm
    rw [hji, RCLike.star_def, Complex.mul_conj]
  rw [htr]
  simp

/-- **Universal All-Dimension Finite Hermitian No-Go Theorem for Euclidean `A₄`**:
For EVERY finite dimension `n : ℕ`, any four `n × n` Hermitian matrices satisfying the Euclidean
`A₄` Nambu 3-algebra relations must ALL be identically zero. -/
theorem euclidean_A4_hermitian_matrix_rep_trivial {n : ℕ}
    (T₁ T₂ T₃ T₄ : Matrix (Fin n) (Fin n) ℂ)
    (hH₁ : T₁.IsHermitian) (hH₂ : T₂.IsHermitian) (hH₃ : T₃.IsHermitian) (hH₄ : T₄.IsHermitian)
    (h123 : nambu3 T₁ T₂ T₃ = I • T₄)
    (h234 : nambu3 T₂ T₃ T₄ = (-I) • T₁)
    (h341 : nambu3 T₃ T₄ T₁ = I • T₂)
    (h412 : nambu3 T₄ T₁ T₂ = (-I) • T₃) :
    T₁ = 0 ∧ T₂ = 0 ∧ T₃ = 0 ∧ T₄ = 0 := by
  have hZero := trace_alternating_nambu3_eq_zero T₁ T₂ T₃ T₄
  rw [h123, h234, h341, h412] at hZero
  simp only [mul_smul_comm, Matrix.trace_smul, smul_eq_mul] at hZero
  have hFac : I * (Matrix.trace (T₄ * T₄) + Matrix.trace (T₁ * T₁) +
      Matrix.trace (T₂ * T₂) + Matrix.trace (T₃ * T₃)) = 0 := by
    linear_combination hZero
  have hSumZero : Matrix.trace (T₄ * T₄) + Matrix.trace (T₁ * T₁) +
      Matrix.trace (T₂ * T₂) + Matrix.trace (T₃ * T₃) = 0 := by
    rcases mul_eq_zero.mp hFac with hI | hS
    · exact absurd hI I_ne_zero
    · exact hS
  have hReZero := congrArg Complex.re hSumZero
  simp only [Complex.add_re, Complex.zero_re,
    trace_mul_self_re_of_isHermitian _ hH₁,
    trace_mul_self_re_of_isHermitian _ hH₂,
    trace_mul_self_re_of_isHermitian _ hH₃,
    trace_mul_self_re_of_isHermitian _ hH₄] at hReZero
  have hnn1 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (T₁ i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hnn2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (T₂ i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hnn3 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (T₃ i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hnn4 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (T₄ i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have killHerm : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) = 0) → A = 0 := by
    intro A hA
    ext i j
    have hi : ∑ j' : Fin n, Complex.normSq (A i j') = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => Complex.normSq_nonneg (A a b)).mp hA i (Finset.mem_univ i)
    have hij : Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => Complex.normSq_nonneg (A i b)).mp hi j
        (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp hij
  refine ⟨killHerm T₁ (by linarith [hnn1, hnn2, hnn3, hnn4, hReZero]),
    killHerm T₂ (by linarith [hnn1, hnn2, hnn3, hnn4, hReZero]),
    killHerm T₃ (by linarith [hnn1, hnn2, hnn3, hnn4, hReZero]),
    killHerm T₄ (by linarith [hnn1, hnn2, hnn3, hnn4, hReZero])⟩

/-! ### Part 3: Explicit `2 × 2` Hermitian Lorentzian `A_{3,1}` Positive Witness -/

/-- Rescaling factor `c = (1 / 12)^(1/4)` satisfying `12 * c^4 = 1`. -/
def lorScale : ℝ := Real.sqrt (Real.sqrt (1 / 12 : ℝ))

private lemma lorScale_pos : 0 < lorScale := by
  unfold lorScale
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

private lemma lorScale_pow4 : 12 * lorScale ^ 4 = 1 := by
  have h0 : 0 ≤ (1 / 12 : ℝ) := by norm_num
  have h1 : Real.sqrt (1 / 12 : ℝ) ^ 2 = 1 / 12 := Real.sq_sqrt h0
  have h2 : lorScale ^ 2 = Real.sqrt (1 / 12 : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : lorScale ^ 4 = 1 / 12 := by
    calc
      lorScale ^ 4 = (lorScale ^ 2) ^ 2 := by ring
      _ = Real.sqrt (1 / 12 : ℝ) ^ 2 := by rw [h2]
      _ = 1 / 12 := h1
  linarith

/-- Explicit `2 × 2` Pauli matrices and Lorentzian `A_{3,1}` Hermitian generators. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def lorT1 : Matrix (Fin 2) (Fin 2) ℂ := (lorScale : ℂ) • pauli1
def lorT2 : Matrix (Fin 2) (Fin 2) ℂ := (lorScale : ℂ) • pauli2
def lorT3 : Matrix (Fin 2) (Fin 2) ℂ := (lorScale : ℂ) • pauli3
def lorT4 : Matrix (Fin 2) (Fin 2) ℂ := ((6 * lorScale ^ 3 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Non-commutativity witness for the `2 × 2` Pauli algebra carrier (`σ₁ σ₂ ≠ σ₂ σ₁`). -/
theorem pauli1_mul_pauli2_ne_comm : pauli1 * pauli2 ≠ pauli2 * pauli1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp [pauli1, pauli2, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hre := congrArg Complex.im h00
  norm_num at hre

private lemma nambu3_smul_three {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (a b c : R) (X Y Z : A) :
    nambu3 (a • X) (b • Y) (c • Z) = (a * b * c) • nambu3 X Y Z := by
  unfold nambu3
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h1 : c * (b * a) = a * b * c := by
    rw [← mul_assoc, mul_comm c b, mul_comm (b * c) a, ← mul_assoc]
  have h2 : b * (c * a) = a * b * c := by rw [mul_comm c a, ← mul_assoc, mul_comm b a]
  have h3 : a * (c * b) = a * b * c := by rw [mul_comm c b, ← mul_assoc]
  have h4 : c * (a * b) = a * b * c := mul_comm c (a * b)
  have h5 : b * (a * c) = a * b * c := by rw [← mul_assoc, mul_comm b a, mul_assoc]
  have h6 : a * (b * c) = a * b * c := (mul_assoc a b c).symm
  rw [h1, h2, h3, h4, h5, h6, ← smul_sub, ← smul_add, ← smul_sub, ← smul_add, ← smul_sub]

private lemma lieComm_smul_two {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (a b : R) (X Y : A) :
    lieComm (a • X) (b • Y) = (a * b) • lieComm X Y := by
  unfold lieComm
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm b a, ← smul_sub]

/-- **Lorentzian `A_{3,1}` Non-Trivial Hermitian Witness (Sharpness Contrast)**:
All four `lorTᵢ` are Hermitian, nonzero, and satisfy the indefinite-signature `A_{3,1}`
Nambu 3-algebra relations (`[T₁,T₂,T₃]_N = +I T₄` and `[T₄,T_i,T_j]_N = +I ε_{ijk} T_k`). -/
theorem lorentzian_A31_hermitian_nontrivial_witness :
    lorT1.IsHermitian ∧ lorT2.IsHermitian ∧ lorT3.IsHermitian ∧ lorT4.IsHermitian ∧
    lorT1 ≠ 0 ∧ lorT2 ≠ 0 ∧ lorT3 ≠ 0 ∧ lorT4 ≠ 0 ∧
    nambu3 lorT1 lorT2 lorT3 = I • lorT4 ∧
    nambu3 lorT4 lorT1 lorT2 = I • lorT3 ∧
    nambu3 lorT4 lorT2 lorT3 = I • lorT1 ∧
    nambu3 lorT4 lorT3 lorT1 = I • lorT2 := by
  have hc4 : (lorScale : ℂ) ^ 4 = (1 / 12 : ℂ) := by
    have hR : lorScale ^ 4 = 1 / 12 := by linarith [lorScale_pow4]
    have hC := congrArg (fun x : ℝ => (x : ℂ)) hR
    push_cast at hC
    exact hC
  have hpHerm1 : pauli1.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli1]
  have hpHerm2 : pauli2.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli2]
  have hpHerm3 : pauli3.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli3]
  have hp123 : nambu3 pauli1 pauli2 pauli3 = (6 * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nambu3, pauli1, pauli2, pauli3, Complex.ext_iff] <;> norm_num
  have hComm12 : lieComm pauli1 pauli2 = (2 * I) • pauli3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lieComm, pauli1, pauli2, pauli3, Complex.ext_iff] <;> norm_num
  have hComm23 : lieComm pauli2 pauli3 = (2 * I) • pauli1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lieComm, pauli1, pauli2, pauli3, Complex.ext_iff] <;> norm_num
  have hComm31 : lieComm pauli3 pauli1 = (2 * I) • pauli2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lieComm, pauli1, pauli2, pauli3, Complex.ext_iff] <;> norm_num
  have scaleHerm : ∀ {r : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ},
      M.IsHermitian → ((r : ℂ) • M).IsHermitian := by
    intro r M hM
    rw [Matrix.IsHermitian]
    ext i j
    have hij := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) hM.eq
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_smul, RCLike.star_def,
      Complex.conj_ofReal] at hij ⊢
    rw [← hij]
  refine ⟨scaleHerm hpHerm1, scaleHerm hpHerm2, scaleHerm hpHerm3,
    scaleHerm Matrix.isHermitian_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simp [lorT1, pauli1] at h01
    exact lorScale_pos.ne' h01
  · intro h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
    simp [lorT2, pauli2] at h10
    exact lorScale_pos.ne' h10
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp [lorT3, pauli3] at h00
    exact lorScale_pos.ne' h00
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp [lorT4] at h00
    exact lorScale_pos.ne' h00
  · unfold lorT1 lorT2 lorT3 lorT4
    rw [nambu3_smul_three, hp123, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · unfold lorT4 lorT1 lorT2 lorT3
    rw [nambu3_smul_one_left, lieComm_smul_two, hComm12, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    calc
      6 * (lorScale : ℂ) ^ 3 * ((lorScale : ℂ) * (lorScale : ℂ)) * (2 * I)
          = 12 * (lorScale : ℂ) ^ 4 * (I * (lorScale : ℂ)) := by ring
      _ = 12 * (1 / 12 : ℂ) * (I * (lorScale : ℂ)) := by rw [hc4]
      _ = I * (lorScale : ℂ) := by ring
  · unfold lorT4 lorT2 lorT3 lorT1
    rw [nambu3_smul_one_left, lieComm_smul_two, hComm23, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    calc
      6 * (lorScale : ℂ) ^ 3 * ((lorScale : ℂ) * (lorScale : ℂ)) * (2 * I)
          = 12 * (lorScale : ℂ) ^ 4 * (I * (lorScale : ℂ)) := by ring
      _ = 12 * (1 / 12 : ℂ) * (I * (lorScale : ℂ)) := by rw [hc4]
      _ = I * (lorScale : ℂ) := by ring
  · unfold lorT4 lorT3 lorT1 lorT2
    rw [nambu3_smul_one_left, lieComm_smul_two, hComm31, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    calc
      6 * (lorScale : ℂ) ^ 3 * ((lorScale : ℂ) * (lorScale : ℂ)) * (2 * I)
          = 12 * (lorScale : ℂ) ^ 4 * (I * (lorScale : ℂ)) := by ring
      _ = 12 * (1 / 12 : ℂ) * (I * (lorScale : ℂ)) := by rw [hc4]
      _ = I * (lorScale : ℂ) := by ring

end InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
