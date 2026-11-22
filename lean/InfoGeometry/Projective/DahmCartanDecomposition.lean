/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Tactic
import InfoGeometry.Projective.DahmKleinLieIsomorphism

/-!
# Cartan decomposition `15 = 5 ⊕ 10 = 5 ⊕ 6 ⊕ 3 ⊕ 1` (Dahm, Sec. II)

CAS-confirmed (`stage2_cartan.py`), proved here in the owner basis order.

* `Ω` pairs the basis vectors `(0,1)` and `(2,3)`; `θ X = Ω Xᵀ Ω` is an involutive
  Lie algebra automorphism of `gl₄` (`theta_theta`, `theta_lie`).
* `k := so(Ω)` (Mathlib `skewAdjointMatricesLieSubalgebra Ω`, i.e. `sp₄`) is exactly
  the fixed algebra of `θ` (`mem_k_iff`), and exactly the stabilizer of the
  non-null Plücker vector `w = e₀₁ + e₂₃` under `Λ²` (`mem_k_iff_lam2_w`,
  `kleinGram`-norm `2`).  This is Dahm's `usp(4) ≅ so(5)` as a stabilizer.
* `p := {X | θX = -X, tr X = 0}`; `sl₄ = k ⊕ p` (`sl_decomposition`, `k_inf_p`),
  `[k,p] ⊆ p`, `[p,p] ⊆ k` (`lie_k_p`, `lie_p_p`); `p → w^⊥` is injective.
* `H = diag(1,-1,1,-1) ∈ k` grades `k = m₋ ⊕ l ⊕ m₊` by `ad H ∈ {-2, 0, 2}`, with
  `[l,m±] ⊆ m±`, `[m₊,m₋] ⊆ l`, `[m±,m±] = 0` (`lie_graded`, `ad_H_four`).
  CAS dimensions: `m± = 3`, `l = 4 = 3 (sl₂) + 1 (centre ∋ H)`, so `10 = 6 + 3 + 1`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The involution, stabilizer, direct-sum, and grading statements are proved for
the displayed finite matrix representation.

#### BUCKET 2: CONDITIONAL THEOREMS
The Lie-algebra decomposition uses the stated field and characteristic-zero
hypotheses; the result is about these matrix subspaces.

#### BUCKET 3: OPEN CLOSURE DEBT
This module does not by itself construct a group-level Cartan decomposition or
identify other real forms.
-/

namespace InfoGeometry.Projective.DahmCartanDecomposition

open Matrix LieAlgebra
open InfoGeometry.Projective.DahmKleinLieIsomorphism

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type*} [CommRing R]

/-- Symplectic form pairing `(0,1)` and `(2,3)`. -/
def omega : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

/-- The chosen symplectic matrix squares to `-I`. -/
theorem omega_mul_omega : (omega : Matrix (Fin 4) (Fin 4) R) * omega = -1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [omega, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The chosen symplectic matrix is skew-symmetric. -/
theorem omega_transpose : (omega : Matrix (Fin 4) (Fin 4) R)ᵀ = -omega := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [omega]

/-- Cartan involution `θ X = Ω Xᵀ Ω` (`= -Ω⁻¹ Xᵀ Ω`). -/
def theta (X : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R := omega * Xᵀ * omega

/-- The Cartan map is an involution. -/
theorem theta_theta (X : Matrix (Fin 4) (Fin 4) R) : theta (theta X) = X := by
  calc theta (theta X) = omega * (omega * Xᵀ * omega)ᵀ * omega := rfl
    _ = omega * omegaᵀ * X * omegaᵀ * omega := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (omega * omega) * X * (omega * omega) := by
        rw [omega_transpose]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    _ = X := by rw [omega_mul_omega]; simp

/-- The Cartan map reverses products with the symplectic sign. -/
theorem theta_mul (X Y : Matrix (Fin 4) (Fin 4) R) : theta (X * Y) = -(theta Y * theta X) := by
  unfold theta
  rw [Matrix.transpose_mul]
  have h : omega * Yᵀ * omega * (omega * Xᵀ * omega) = -(omega * Yᵀ * Xᵀ * omega) := by
    rw [show omega * Yᵀ * omega * (omega * Xᵀ * omega) =
        omega * Yᵀ * (omega * omega) * Xᵀ * omega by simp only [Matrix.mul_assoc]]
    rw [omega_mul_omega]; simp [Matrix.mul_assoc]
  rw [h, neg_neg, Matrix.mul_assoc omega Yᵀ Xᵀ]

/-- `θ` is a Lie algebra automorphism of `gl₄`. -/
theorem theta_lie (X Y : Matrix (Fin 4) (Fin 4) R) :
    theta (X * Y - Y * X) = theta X * theta Y - theta Y * theta X := by
  have hsub : theta (X * Y - Y * X) = theta (X * Y) - theta (Y * X) := by
    unfold theta; rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub, theta_mul, theta_mul]; abel

/-- Additivity of the Cartan map. -/
theorem theta_add (X Y : Matrix (Fin 4) (Fin 4) R) : theta (X + Y) = theta X + theta Y := by
  unfold theta; rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

/-- Compatibility of the Cartan map with negation. -/
theorem theta_neg (X : Matrix (Fin 4) (Fin 4) R) : theta (-X) = -theta X := by
  unfold theta; rw [Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]

/-- Linearity of the Cartan map over the commutative coefficient ring. -/
theorem theta_smul (c : R) (X : Matrix (Fin 4) (Fin 4) R) : theta (c • X) = c • theta X := by
  unfold theta; rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The Cartan map negates the matrix trace. -/
theorem trace_theta (X : Matrix (Fin 4) (Fin 4) R) : (theta X).trace = -X.trace := by
  simp [theta, omega, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul,
    dotProduct, Matrix.transpose_apply]; ring

/-- `k = so(Ω)` (Mathlib's skew-adjoint Lie subalgebra for the symplectic form). -/
abbrev kAlg : LieSubalgebra R (Matrix (Fin 4) (Fin 4) R) := skewAdjointMatricesLieSubalgebra omega

/-- **`k` is the fixed algebra of `θ`.** -/
theorem mem_k_iff (X : Matrix (Fin 4) (Fin 4) R) : X ∈ kAlg ↔ theta X = X := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair theta
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.mul_neg, omega_mul_omega]; simp
  · intro h
    calc Xᵀ * omega = -(omega * (omega * Xᵀ * omega)) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, omega_mul_omega]; simp
      _ = omega * -X := by rw [h, Matrix.mul_neg]

/-- The Plücker vector `w = e₀₁ + e₂₃`. -/
def wVec : Fin 6 → R := ![1, 0, 0, 0, 0, 1]

/-- The Klein polar Gram matrix sends the distinguished bivector `e₀₁+e₂₃`
to itself. -/
theorem kleinGram_mulVec_wVec :
    kleinGram *ᵥ (wVec : Fin 6 → R) = wVec := by
  ext i
  fin_cases i <;> simp [kleinGram, wVec, mulVec, dotProduct, Fin.sum_univ_succ]

/-- The distinguished Plücker vector has squared Klein norm two. -/
theorem wVec_norm : wVec ⬝ᵥ (kleinGram *ᵥ (wVec : Fin 6 → R)) = 2 := by
  rw [kleinGram_mulVec_wVec]
  norm_num [wVec, dotProduct, Fin.sum_univ_succ]

/-- `Λ²X w` in coordinates. -/
theorem lam2_mulVec_wVec (X : Matrix (Fin 4) (Fin 4) R) :
    lam2 X *ᵥ wVec = ![X 0 0 + X 1 1, X 2 1 - X 0 3, X 3 1 + X 0 2, -X 2 0 - X 1 3,
      -X 3 0 + X 1 2, X 2 2 + X 3 3] := by
  ext r; fin_cases r <;> simp [lam2, wVec, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- `θX - X` in coordinates (CAS). -/
theorem theta_sub_eq (X : Matrix (Fin 4) (Fin 4) R) :
    theta X - X =
      !![-X 0 0 - X 1 1, 0, -X 0 2 - X 3 1, -X 0 3 + X 2 1;
         0, -X 0 0 - X 1 1, -X 1 2 + X 3 0, -X 1 3 - X 2 0;
         -X 1 3 - X 2 0, X 0 3 - X 2 1, -X 2 2 - X 3 3, 0;
         X 1 2 - X 3 0, -X 0 2 - X 3 1, 0, -X 2 2 - X 3 3] := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [theta, omega, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct, Matrix.transpose_apply] <;> ring

/-- **`k` is the stabilizer of `w` under `Λ²`** (no trace hypothesis needed). -/
theorem mem_k_iff_lam2_w (X : Matrix (Fin 4) (Fin 4) R) :
    X ∈ kAlg ↔ lam2 X *ᵥ wVec = 0 := by
  rw [mem_k_iff, ← sub_eq_zero, theta_sub_eq, lam2_mulVec_wVec]
  constructor
  · intro h
    have e : ∀ a b, (!![-X 0 0 - X 1 1, 0, -X 0 2 - X 3 1, -X 0 3 + X 2 1;
         0, -X 0 0 - X 1 1, -X 1 2 + X 3 0, -X 1 3 - X 2 0;
         -X 1 3 - X 2 0, X 0 3 - X 2 1, -X 2 2 - X 3 3, 0;
         X 1 2 - X 3 0, -X 0 2 - X 3 1, 0, -X 2 2 - X 3 3] : Matrix (Fin 4) (Fin 4) R) a b = 0 :=
      fun a b => by rw [h]; rfl
    have e00 : -X 0 0 - X 1 1 = 0 := by simpa using e 0 0
    have e02 : -X 0 2 - X 3 1 = 0 := by simpa using e 0 2
    have e03 : -X 0 3 + X 2 1 = 0 := by simpa using e 0 3
    have e12 : -X 1 2 + X 3 0 = 0 := by simpa using e 1 2
    have e13 : -X 1 3 - X 2 0 = 0 := by simpa using e 1 3
    have e22 : -X 2 2 - X 3 3 = 0 := by simpa using e 2 2
    ext r; fin_cases r <;> simp
    · linear_combination -e00
    · linear_combination e03
    · linear_combination -e02
    · linear_combination e13
    · linear_combination -e12
    · linear_combination -e22
  · intro h
    have c : ∀ r, (![X 0 0 + X 1 1, X 2 1 - X 0 3, X 3 1 + X 0 2, -X 2 0 - X 1 3,
        -X 3 0 + X 1 2, X 2 2 + X 3 3] : Fin 6 → R) r = 0 := fun r => by rw [h]; rfl
    have c0 : X 0 0 + X 1 1 = 0 := by simpa using c 0
    have c1 : X 2 1 - X 0 3 = 0 := by simpa using c 1
    have c2 : X 3 1 + X 0 2 = 0 := by simpa using c 2
    have c3 : -X 2 0 - X 1 3 = 0 := by simpa using c 3
    have c4 : -X 3 0 + X 1 2 = 0 := by simpa using c 4
    have c5 : X 2 2 + X 3 3 = 0 := by simpa using c 5
    ext a b; fin_cases a <;> fin_cases b <;> simp
    · linear_combination -c0
    · linear_combination -c2
    · linear_combination c1
    · linear_combination -c0
    · linear_combination -c4
    · linear_combination c3
    · linear_combination c3
    · linear_combination -c1
    · linear_combination -c5
    · linear_combination c4
    · linear_combination -c2
    · linear_combination -c5

/-- `p = {X | θX = -X, tr X = 0}`. -/
def pSet : Set (Matrix (Fin 4) (Fin 4) R) := {X | theta X = -X ∧ X.trace = 0}

/-- **`[k, p] ⊆ p`.** -/
theorem lie_k_p {X Y : Matrix (Fin 4) (Fin 4) R} (hX : X ∈ kAlg) (hY : Y ∈ pSet) :
    X * Y - Y * X ∈ pSet := by
  rw [mem_k_iff] at hX
  refine ⟨?_, ?_⟩
  · rw [theta_lie, hX, hY.1]; simp only [Matrix.mul_neg, Matrix.neg_mul]; abel
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **`[p, p] ⊆ k`.** -/
theorem lie_p_p {X Y : Matrix (Fin 4) (Fin 4) R} (hX : X ∈ pSet) (hY : Y ∈ pSet) :
    X * Y - Y * X ∈ kAlg := by
  rw [mem_k_iff, theta_lie, hX.1, hY.1]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]

/-- Grading element `H = diag(1,-1,1,-1)`. -/
def hGrad : Matrix (Fin 4) (Fin 4) R := Matrix.diagonal ![1, -1, 1, -1]

/-- The grading element belongs to the fixed (symplectic) subalgebra. -/
theorem hGrad_mem_k : (hGrad : Matrix (Fin 4) (Fin 4) R) ∈ kAlg := by
  rw [mem_k_iff]; ext a b; fin_cases a <;> fin_cases b <;>
    simp [theta, omega, hGrad, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecMul,
      dotProduct, Matrix.transpose_apply]

/-- `ad H` is a derivation: graded pieces multiply additively. -/
theorem lie_graded {X Y : Matrix (Fin 4) (Fin 4) R} {a b : R}
    (hX : hGrad * X - X * hGrad = a • X) (hY : hGrad * Y - Y * hGrad = b • Y) :
    hGrad * (X * Y - Y * X) - (X * Y - Y * X) * hGrad = (a + b) • (X * Y - Y * X) := by
  have hX' : hGrad * X = X * hGrad + a • X := by rw [← hX]; abel
  have hY' : hGrad * Y = Y * hGrad + b • Y := by rw [← hY]; abel
  calc hGrad * (X * Y - Y * X) - (X * Y - Y * X) * hGrad
      = hGrad * X * Y - hGrad * Y * X - X * Y * hGrad + Y * X * hGrad := by noncomm_ring
    _ = (X * hGrad + a • X) * Y - (Y * hGrad + b • Y) * X - X * Y * hGrad + Y * X * hGrad := by
        rw [hX', hY']
    _ = X * (hGrad * Y) + a • (X * Y) - (Y * (hGrad * X) + b • (Y * X)) - X * Y * hGrad +
          Y * X * hGrad := by
        simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = X * (Y * hGrad + b • Y) + a • (X * Y) - (Y * (X * hGrad + a • X) + b • (Y * X)) -
          X * Y * hGrad + Y * X * hGrad := by rw [hX', hY']
    _ = (a + b) • (X * Y - Y * X) := by
        simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, add_smul, smul_sub]; abel

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- `k ⊆ sl₄`. -/
theorem trace_eq_zero_of_mem_k {X : Matrix (Fin 4) (Fin 4) K} (hX : X ∈ kAlg) : X.trace = 0 := by
  rw [mem_k_iff] at hX
  have h := trace_theta X
  rw [hX] at h
  have h2 : (2 : K) * X.trace = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- `k ∩ p = 0`. -/
theorem k_inf_p {X : Matrix (Fin 4) (Fin 4) K} (hk : X ∈ kAlg) (hp : X ∈ pSet) : X = 0 := by
  rw [mem_k_iff] at hk
  have h : X = -X := hk.symm.trans hp.1
  have h2 : (2 : K) • X = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel X
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **`sl₄ = k ⊕ p`:** every trace-free `X` splits as `½(X + θX) + ½(X - θX)`. -/
theorem sl_decomposition {X : Matrix (Fin 4) (Fin 4) K} (hX : X.trace = 0) :
    (2⁻¹ : K) • (X + theta X) ∈ kAlg ∧ (2⁻¹ : K) • (X - theta X) ∈ pSet ∧
      X = (2⁻¹ : K) • (X + theta X) + (2⁻¹ : K) • (X - theta X) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_k_iff, theta_smul, theta_add, theta_theta, add_comm]
  · rw [theta_smul, sub_eq_add_neg, theta_add, theta_neg, theta_theta, ← smul_neg]
    congr 1; abel
  · rw [Matrix.trace_smul, Matrix.trace_sub, trace_theta, hX]; simp
  · rw [← smul_add]; ext a b; simp [Matrix.add_apply]; ring

/-- On the anti-fixed trace-free subspace, the infinitesimal action on `w`
is injective: two elements with the same Plücker displacement are equal. -/
theorem p_to_w_injective {X Y : Matrix (Fin 4) (Fin 4) K}
    (hpX : X ∈ pSet) (hpY : Y ∈ pSet)
    (hw : lam2 X *ᵥ wVec = lam2 Y *ᵥ wVec) : X = Y := by
  have hp : X - Y ∈ pSet := by
    constructor
    · change theta (X - Y) = -(X - Y)
      rw [sub_eq_add_neg, theta_add, theta_neg, hpX.1, hpY.1]
      abel
    · change (X - Y).trace = 0
      rw [Matrix.trace_sub, hpX.2, hpY.2, sub_self]
  have hlinear : lam2 (X - Y) *ᵥ wVec = 0 := by
    have hmap : lam2 (X - Y) = lam2 X - lam2 Y := by
      have hneg : lam2 (-Y) = -lam2 Y := by
        rw [show -Y = (-1 : K) • Y by simp, lam2_smul]
        simp
      rw [sub_eq_add_neg, lam2_add, hneg]
      simp [sub_eq_add_neg]
    rw [hmap, Matrix.sub_mulVec, hw, sub_self]
  have hzero := k_inf_p ((mem_k_iff_lam2_w (X - Y)).mpr hlinear) hp
  exact sub_eq_zero.mp hzero

/-- No `ad H`-eigenvalue `±4` occurs in `gl₄`; hence `[m₊, m₊] = [m₋, m₋] = 0`. -/
theorem ad_H_four {X : Matrix (Fin 4) (Fin 4) K} {a : K} (ha : a = 4 ∨ a = -4)
    (hX : hGrad * X - X * hGrad = a • X) : X = 0 := by
  have key : ∀ i j, ((![1, -1, 1, -1] : Fin 4 → K) i - (![1, -1, 1, -1] : Fin 4 → K) j - a) *
      X i j = 0 := by
    intro i j
    have h := congrFun (congrFun hX i) j
    simp only [hGrad, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply, smul_eq_mul] at h
    linear_combination h
  ext i j
  have hne : ((![1, -1, 1, -1] : Fin 4 → K) i - (![1, -1, 1, -1] : Fin 4 → K) j - a) ≠ 0 := by
    rcases ha with rfl | rfl <;> fin_cases i <;> fin_cases j <;> norm_num
  simpa using (mul_eq_zero.mp (key i j)).resolve_left hne

end Field

end InfoGeometry.Projective.DahmCartanDecomposition
