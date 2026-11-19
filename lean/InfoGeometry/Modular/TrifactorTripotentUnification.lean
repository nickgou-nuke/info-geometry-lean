/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
# Unified Theory of the Trifactor Tripotent and Peirce Decompositions

This module formalizes the universal algebraic theory of tripotent operators $T^3 = T$
and their canonical role as the bridge between:
  1. The 3-fold Peirce Projector Decomposition ($p_+, p_-, p_0$)
  2. The Trifold Modular Relative Surprisal ($\mathcal{K} = \alpha I + \beta T + \mathcal{K}_0$)
  3. Spectral Eigenvalues ($\lambda \in \{+1, -1, 0\}$)
  4. Commutator Derivation Invariance ($\operatorname{ad}_T(p_k) = 0$)

THEOREMS PROVED NATIVELY:
  1. `tripotent_factorization`: $T^3 - T = T(T - 1)(T + 1)$.
  2. `peirce_partition_of_unity`: $p_+ + p_- + p_0 = 1$.
  3. `peirce_tripotent_reconstruction`: $p_+ - p_- = T$ and $p_+ + p_- = T^2$.
  4. `peirce_eigen_plus`, `peirce_eigen_minus`, `peirce_eigen_zero`:
     $T p_+ = p_+$, $T p_- = -p_-$, $T p_0 = 0$.
  5. `peirce_idempotent_plus`, `peirce_idempotent_minus`, `peirce_orthogonal_plus_minus`.
  6. `trifactor_surprisal_peirce_spectral_split`:
     $\alpha \cdot 1 + \beta \cdot T = (\alpha + \beta) p_+ + (\alpha - \beta) p_- + \alpha p_0$.
  7. `tripotent_derivation_annihilates_projectors`:
     $[T, p_+] = 0$, $[T, p_-] = 0$, $[T, p_0] = 0$.

All proofs are complete with 0 `sorry`s, 0 custom axioms, and 0 placeholders.
-/

namespace InfoGeometry.Modular.TrifactorTripotentUnification

variable {R : Type*} [Ring R]
variable {A : Type*} [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-! =========================================================================
    1. Tripotents and the Cubic Factorization
    ========================================================================= -/

/-- An element $T \in A$ is a tripotent if $T^3 = T$. -/
def IsTripotent (T : A) : Prop :=
  T * T * T = T

/--
LEMMA 1 (Cubic Factorization of Tripotents):
  `T³ - T = T * (T - 1) * (T + 1)`
-/
theorem tripotent_factorization (T : A) :
    T * T * T - T = T * (T - 1) * (T + 1) := by
  calc
    T * T * T - T = (T * T - T) * (T + 1) := by
      rw [mul_add, mul_one, sub_mul]
      abel_nf
    _ = T * (T - 1) * (T + 1) := by
      rw [mul_sub, mul_one]

/-! =========================================================================
    2. The Three Canonical Peirce Projectors (inv2 = 1/2)
    ========================================================================= -/

/-- Positive Peirce Projector $p_+ = \frac{1}{2}(T^2 + T)$. -/
def projPlus (inv2 : R) (T : A) : A :=
  inv2 • (T * T + T)

/-- Negative Peirce Projector $p_- = \frac{1}{2}(T^2 - T)$. -/
def projMinus (inv2 : R) (T : A) : A :=
  inv2 • (T * T - T)

/-- Vacuum / Apex Peirce Projector $p_0 = 1 - T^2$. -/
def projZero (T : A) : A :=
  1 - T * T

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/--
THEOREM 2 (Partition of Unity / Completeness):
  `p_+ + p_- + p_0 = 1`
-/
theorem peirce_partition_of_unity (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) :
    projPlus inv2 T + projMinus inv2 T + projZero T = 1 := by
  dsimp [projPlus, projMinus, projZero]
  rw [← smul_add]
  have h_add : (T * T + T) + (T * T - T) = (2 : R) • (T * T) := by
    rw [two_smul]
    abel_nf
  rw [h_add, smul_smul, (Commute.ofNat_right inv2 2).eq, h2, one_smul]
  abel_nf

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/--
THEOREM 3A (Tripotent Reconstruction):
  `p_+ - p_- = T`
-/
theorem peirce_tripotent_reconstruction (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) :
    projPlus inv2 T - projMinus inv2 T = T := by
  dsimp [projPlus, projMinus]
  rw [← smul_sub]
  have h_sub : (T * T + T) - (T * T - T) = (2 : R) • T := by
    rw [two_smul]
    abel_nf
  rw [h_sub, smul_smul, (Commute.ofNat_right inv2 2).eq, h2, one_smul]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/--
THEOREM 3B (Tripotent Square Reconstruction):
  `p_+ + p_- = T²`
-/
theorem peirce_tripotent_sq_reconstruction (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) :
    projPlus inv2 T + projMinus inv2 T = T * T := by
  dsimp [projPlus, projMinus]
  rw [← smul_add]
  have h_add : (T * T + T) + (T * T - T) = (2 : R) • (T * T) := by
    rw [two_smul]
    abel_nf
  rw [h_add, smul_smul, (Commute.ofNat_right inv2 2).eq, h2, one_smul]

/-! =========================================================================
    3. Spectral Eigenvalue Equations
    ========================================================================= -/

omit [IsScalarTower R A A] in
/--
THEOREM 4A (Positive Eigenvalue +1):
  `T * p_+ = p_+`
-/
theorem peirce_eigen_plus (inv2 : R) (T : A) (hT : IsTripotent T) :
    T * projPlus inv2 T = projPlus inv2 T := by
  dsimp [projPlus]
  rw [mul_smul_comm, mul_add, ← mul_assoc, hT]
  rw [add_comm T (T * T)]

omit [IsScalarTower R A A] in
/--
THEOREM 4B (Negative Eigenvalue -1):
  `T * p_- = -p_-`
-/
theorem peirce_eigen_minus (inv2 : R) (T : A) (hT : IsTripotent T) :
    T * projMinus inv2 T = - projMinus inv2 T := by
  dsimp [projMinus]
  rw [mul_smul_comm, mul_sub, ← mul_assoc, hT]
  have hneg : T - T * T = - (T * T - T) := by abel_nf
  rw [hneg, smul_neg]

/--
THEOREM 4C (Zero / Apex Null Eigenvalue 0):
  `T * p_0 = 0`
-/
theorem peirce_eigen_zero (T : A) (hT : IsTripotent T) :
    T * projZero T = 0 := by
  dsimp [projZero]
  rw [mul_sub, mul_one, ← mul_assoc, hT, sub_self]

/-! =========================================================================
    4. Orthogonality and Idempotency
    ========================================================================= -/

/--
THEOREM 5A (Idempotency of p_+):
  `p_+ * p_+ = p_+`
-/
theorem peirce_idempotent_plus (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) (hT : IsTripotent T) :
    projPlus inv2 T * projPlus inv2 T = projPlus inv2 T := by
  dsimp [projPlus]
  have h_mul : (T * T + T) * (T * T + T) = (2 : R) • (T * T + T) := by
    have hT4 : T * T * (T * T) = T * T := by
      calc
        T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
        _ = T * (T * T * T) := by rw [mul_assoc T T T]
        _ = T * T := by rw [hT]
    have hT3 : T * (T * T) = T := by
      calc
        T * (T * T) = T * T * T := by rw [mul_assoc]
        _ = T := hT
    calc
      (T * T + T) * (T * T + T)
        = (T * T + T) * (T * T) + (T * T + T) * T := by rw [mul_add]
      _ = T * T * (T * T) + T * (T * T) + (T * T * T + T * T) := by rw [add_mul, add_mul]
      _ = T * T + T + (T + T * T) := by rw [hT4, hT3, hT]
      _ = (T * T + T) + (T * T + T) := by abel_nf
      _ = (2 : R) • (T * T + T) := by rw [two_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, h_mul,
      smul_smul, mul_assoc, (Commute.ofNat_right inv2 2).eq, h2, mul_one]

/--
THEOREM 5B (Idempotency of p_-):
  `p_- * p_- = p_-`
-/
theorem peirce_idempotent_minus (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) (hT : IsTripotent T) :
    projMinus inv2 T * projMinus inv2 T = projMinus inv2 T := by
  dsimp [projMinus]
  have h_mul : (T * T - T) * (T * T - T) = (2 : R) • (T * T - T) := by
    have hT4 : T * T * (T * T) = T * T := by
      calc
        T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
        _ = T * (T * T * T) := by rw [mul_assoc T T T]
        _ = T * T := by rw [hT]
    have hT3 : T * (T * T) = T := by
      calc
        T * (T * T) = T * T * T := by rw [mul_assoc]
        _ = T := hT
    calc
      (T * T - T) * (T * T - T)
        = (T * T - T) * (T * T) - (T * T - T) * T := by rw [mul_sub]
      _ = T * T * (T * T) - T * (T * T) - (T * T * T - T * T) := by rw [sub_mul, sub_mul]
      _ = T * T - T - (T - T * T) := by rw [hT4, hT3, hT]
      _ = (T * T - T) + (T * T - T) := by abel_nf
      _ = (2 : R) • (T * T - T) := by rw [two_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, h_mul,
      smul_smul, mul_assoc, (Commute.ofNat_right inv2 2).eq, h2, mul_one]

/--
THEOREM 5C (Orthogonality p_+ * p_- = 0):
-/
theorem peirce_orthogonal_plus_minus (inv2 : R) (T : A) (hT : IsTripotent T) :
    projPlus inv2 T * projMinus inv2 T = 0 := by
  dsimp [projPlus, projMinus]
  have h_mul : (T * T + T) * (T * T - T) = 0 := by
    have hT4 : T * T * (T * T) = T * T := by
      calc
        T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
        _ = T * (T * T * T) := by rw [mul_assoc T T T]
        _ = T * T := by rw [hT]
    have hT3 : T * (T * T) = T := by
      calc
        T * (T * T) = T * T * T := by rw [mul_assoc]
        _ = T := hT
    calc
      (T * T + T) * (T * T - T)
        = (T * T + T) * (T * T) - (T * T + T) * T := by rw [mul_sub]
      _ = T * T * (T * T) + T * (T * T) - (T * T * T + T * T) := by rw [add_mul, add_mul]
      _ = T * T + T - (T + T * T) := by rw [hT4, hT3, hT]
      _ = 0 := by abel_nf
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, h_mul, smul_zero]

/-- The signed Peirce sectors are orthogonal in the reverse multiplication order. -/
theorem peirce_orthogonal_minus_plus (inv2 : R) (T : A) (hT : IsTripotent T) :
    projMinus inv2 T * projPlus inv2 T = 0 := by
  dsimp [projMinus, projPlus]
  have h_mul : (T * T - T) * (T * T + T) = 0 := by
    have hT4 : T * T * (T * T) = T * T := by
      calc
        T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
        _ = T * (T * T * T) := by rw [mul_assoc T T T]
        _ = T * T := by rw [hT]
    have hT3 : T * (T * T) = T := by
      calc
        T * (T * T) = T * T * T := by rw [mul_assoc]
        _ = T := hT
    calc
      (T * T - T) * (T * T + T)
          = (T * T - T) * (T * T) + (T * T - T) * T := by rw [mul_add]
      _ = T * T * (T * T) - T * (T * T) + (T * T * T - T * T) := by
          rw [sub_mul, sub_mul]
      _ = T * T - T + (T - T * T) := by rw [hT4, hT3, hT]
      _ = 0 := by abel_nf
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, h_mul, smul_zero]

/-- The zero Peirce sector is an idempotent whenever `T` is tripotent. -/
theorem peirce_idempotent_zero (T : A) (hT : IsTripotent T) :
    projZero T * projZero T = projZero T := by
  have hT4 : T * T * T * T = T * T := by
    calc
      T * T * T * T = (T * T * T) * T := by noncomm_ring
      _ = T * T := by rw [hT]
  have hT2 : (T * T) * (T * T) = T * T := by
    calc
      (T * T) * (T * T) = T * T * T * T := by noncomm_ring
      _ = T * T := hT4
  dsimp [projZero]
  calc
    (1 - T * T) * (1 - T * T) = 1 - T * T - T * T + (T * T) * (T * T) := by noncomm_ring
    _ = 1 - T * T := by rw [hT2]; abel_nf

/-- The vacuum Peirce projector annihilates the positive Peirce sector. -/
theorem peirce_orthogonal_zero_plus (inv2 : R) (T : A) (hT : IsTripotent T) :
    projZero T * projPlus inv2 T = 0 ∧ projPlus inv2 T * projZero T = 0 := by
  have hT4 : T * T * T * T = T * T := by
    calc
      T * T * T * T = (T * T * T) * T := by noncomm_ring
      _ = T * T := by rw [hT]
  constructor
  · dsimp [projZero, projPlus]
    rw [mul_smul_comm]
    have hz : (1 - T * T) * (T * T + T) = 0 := by
      calc
        (1 - T * T) * (T * T + T) = T * T + T - (T * T * (T * T) + T * T * T) := by noncomm_ring
        _ = 0 := by
          have hT4' : T * T * (T * T) = T * T := by
            calc
              T * T * (T * T) = T * T * T * T := by noncomm_ring
              _ = T * T := hT4
          rw [hT4', hT]
          noncomm_ring
    rw [hz, smul_zero]
  · dsimp [projZero, projPlus]
    rw [smul_mul_assoc]
    have hz : (T * T + T) * (1 - T * T) = 0 := by
      calc
        (T * T + T) * (1 - T * T) = T * T + T - (T * T * (T * T) + T * T * T) := by noncomm_ring
        _ = 0 := by
          have hT4' : T * T * (T * T) = T * T := by
            calc
              T * T * (T * T) = T * T * T * T := by noncomm_ring
              _ = T * T := hT4
          rw [hT4', hT]
          noncomm_ring
    rw [hz, smul_zero]

/-- The vacuum Peirce projector annihilates the negative Peirce sector. -/
theorem peirce_orthogonal_zero_minus (inv2 : R) (T : A) (hT : IsTripotent T) :
    projZero T * projMinus inv2 T = 0 ∧ projMinus inv2 T * projZero T = 0 := by
  have hT4 : T * T * T * T = T * T := by
    calc
      T * T * T * T = (T * T * T) * T := by noncomm_ring
      _ = T * T := by rw [hT]
  constructor
  · dsimp [projZero, projMinus]
    rw [mul_smul_comm]
    have hz : (1 - T * T) * (T * T - T) = 0 := by
      calc
        (1 - T * T) * (T * T - T) = T * T - T - (T * T * (T * T) - T * T * T) := by noncomm_ring
        _ = 0 := by
          have hT4' : T * T * (T * T) = T * T := by
            calc
              T * T * (T * T) = T * T * T * T := by noncomm_ring
              _ = T * T := hT4
          rw [hT4', hT]
          noncomm_ring
    rw [hz, smul_zero]
  · dsimp [projZero, projMinus]
    rw [smul_mul_assoc]
    have hz : (T * T - T) * (1 - T * T) = 0 := by
      calc
        (T * T - T) * (1 - T * T) = T * T - T - (T * T * (T * T) - T * T * T) := by noncomm_ring
        _ = 0 := by
          have hT4' : T * T * (T * T) = T * T := by
            calc
              T * T * (T * T) = T * T * T * T := by noncomm_ring
              _ = T * T := hT4
          rw [hT4', hT]
          noncomm_ring
    rw [hz, smul_zero]

/-- The full two-sided Peirce multiplication table for a tripotent: the three
spectral pieces are idempotents, sum to the identity, and are pairwise
orthogonal in both orders. This is an algebraic decomposition theorem; it
does not assert self-adjointness or positivity of the projectors. -/
theorem tripotent_two_sided_peirce_system
    (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) (hT : IsTripotent T) :
    projPlus inv2 T + projMinus inv2 T + projZero T = 1 ∧
    projPlus inv2 T * projPlus inv2 T = projPlus inv2 T ∧
    projMinus inv2 T * projMinus inv2 T = projMinus inv2 T ∧
    projZero T * projZero T = projZero T ∧
    projPlus inv2 T * projMinus inv2 T = 0 ∧
    projMinus inv2 T * projPlus inv2 T = 0 ∧
    projZero T * projPlus inv2 T = 0 ∧
    projPlus inv2 T * projZero T = 0 ∧
    projZero T * projMinus inv2 T = 0 ∧
    projMinus inv2 T * projZero T = 0 := by
  refine ⟨peirce_partition_of_unity inv2 h2 T,
    peirce_idempotent_plus inv2 h2 T hT,
    peirce_idempotent_minus inv2 h2 T hT,
    peirce_idempotent_zero T hT,
    peirce_orthogonal_plus_minus inv2 T hT,
    peirce_orthogonal_minus_plus inv2 T hT,
    (peirce_orthogonal_zero_plus inv2 T hT).1,
    (peirce_orthogonal_zero_plus inv2 T hT).2,
    (peirce_orthogonal_zero_minus inv2 T hT).1,
    (peirce_orthogonal_zero_minus inv2 T hT).2⟩

/-! =========================================================================
    5. Trifactor Surprisal Spectral Decomposition
    ========================================================================= -/

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/--
MASTER THEOREM 6 (Trifactor Surprisal Spectral Resolution):
The operator relative surprisal $\mathcal{K} = \alpha I + \beta T$ decomposes
into its three discrete tripotent spectral energy levels:
  `α • 1 + β • T = (α + β) • p_+ + (α - β) • p_- + α • p_0`
-/
theorem trifactor_surprisal_peirce_spectral_split
    (inv2 : R) (h2 : (2 : R) * inv2 = 1)
    (alpha beta : R) (T : A) :
    alpha • (1 : A) + beta • T =
      (alpha + beta) • projPlus inv2 T +
      (alpha - beta) • projMinus inv2 T +
      alpha • projZero T := by
  have h_sum := peirce_partition_of_unity inv2 h2 T
  have h_diff := peirce_tripotent_reconstruction inv2 h2 T
  calc
    alpha • (1 : A) + beta • T
      = alpha • (projPlus inv2 T + projMinus inv2 T + projZero T) +
        beta • (projPlus inv2 T - projMinus inv2 T) := by
        rw [h_sum, h_diff]
    _ = (alpha • projPlus inv2 T + alpha • projMinus inv2 T + alpha • projZero T) +
        (beta • projPlus inv2 T - beta • projMinus inv2 T) := by
        rw [smul_add, smul_add, smul_sub]
    _ = (alpha + beta) • projPlus inv2 T +
        (alpha - beta) • projMinus inv2 T +
        alpha • projZero T := by
        rw [add_smul, sub_smul]
        abel_nf

/-! =========================================================================
    6. Commutator Derivation Invariance: ad_T(p_k) = 0
    ========================================================================= -/

/-- Commutator bracket `[X, Y] = X * Y - Y * X`. -/
def bracket (X Y : A) : A :=
  X * Y - Y * X

/--
THEOREM 7A (Tripotent Derivation Annihilates Positive Projector):
  `[T, p_+] = 0`
-/
theorem tripotent_derivation_annihilates_projPlus (inv2 : R) (T : A) (hT : IsTripotent T) :
    bracket T (projPlus inv2 T) = 0 := by
  dsimp [bracket]
  have h_left : T * projPlus inv2 T = projPlus inv2 T := peirce_eigen_plus inv2 T hT
  have h_right : projPlus inv2 T * T = projPlus inv2 T := by
    dsimp [projPlus]
    rw [smul_mul_assoc, add_mul, hT, add_comm T (T * T)]
  rw [h_left, h_right, sub_self]

/--
THEOREM 7B (Tripotent Derivation Annihilates Negative Projector):
  `[T, p_-] = 0`
-/
theorem tripotent_derivation_annihilates_projMinus (inv2 : R) (T : A) (hT : IsTripotent T) :
    bracket T (projMinus inv2 T) = 0 := by
  dsimp [bracket]
  have h_left : T * projMinus inv2 T = - projMinus inv2 T := peirce_eigen_minus inv2 T hT
  have h_right : projMinus inv2 T * T = - projMinus inv2 T := by
    dsimp [projMinus]
    rw [smul_mul_assoc, sub_mul, hT]
    have hneg : T - T * T = - (T * T - T) := by abel_nf
    rw [hneg, smul_neg]
  rw [h_left, h_right, sub_self]

/--
THEOREM 7C (Tripotent Derivation Annihilates Vacuum / Apex Projector):
  `[T, p_0] = 0`
-/
theorem tripotent_derivation_annihilates_projZero (T : A) (hT : IsTripotent T) :
    bracket T (projZero T) = 0 := by
  dsimp [bracket]
  have h_left : T * projZero T = 0 := peirce_eigen_zero T hT
  have h_right : projZero T * T = 0 := by
    dsimp [projZero]
    rw [sub_mul, one_mul, hT, sub_self]
  rw [h_left, h_right, sub_self]

/-! ### Operator-star refinement for finite complex matrix algebras -/

section MatrixStarPeirce

variable {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)

/-- For a self-adjoint tripotent matrix, the positive Peirce idempotent is
self-adjoint. The carrier remains the full matrix algebra; no diagonal form
or spectral basis is chosen. -/
theorem matrix_projPlus_selfAdjoint
    (hTstar : star T = T) :
    star (projPlus (R := ℂ) (A := Matrix (Fin n) (Fin n) ℂ) (1 / 2 : ℂ) T) =
      projPlus (R := ℂ) (A := Matrix (Fin n) (Fin n) ℂ) (1 / 2 : ℂ) T := by
  simp [projPlus, hTstar]

/-- For a self-adjoint tripotent matrix, the negative Peirce idempotent is
self-adjoint. -/
theorem matrix_projMinus_selfAdjoint
    (hTstar : star T = T) :
    star (projMinus (R := ℂ) (A := Matrix (Fin n) (Fin n) ℂ) (1 / 2 : ℂ) T) =
      projMinus (R := ℂ) (A := Matrix (Fin n) (Fin n) ℂ) (1 / 2 : ℂ) T := by
  simp [projMinus, hTstar]

/-- The vacuum Peirce idempotent of a self-adjoint tripotent matrix is
self-adjoint. -/
theorem matrix_projZero_selfAdjoint
    (hTstar : star T = T) : star (projZero T) = projZero T := by
  simp [projZero, hTstar]


end MatrixStarPeirce

section RealMatrixPeircePositivity

variable {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)

/-- A self-adjoint tripotent on the full finite real matrix algebra has
positive-semidefinite Peirce projections. The assertion concerns the full
quadratic forms, not only their diagonal entries. -/
theorem matrix_tripotent_peirce_posSemidef
    (hT : T * T * T = T) (hTstar : star T = T) :
    Matrix.PosSemidef
        (projPlus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T) ∧
    Matrix.PosSemidef
        (projMinus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T) ∧
    Matrix.PosSemidef (projZero T) := by
  have hhalf : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
  have hplus_idem := peirce_idempotent_plus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ)
    (1 / 2 : ℝ) hhalf T hT
  have hminus_idem := peirce_idempotent_minus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ)
    (1 / 2 : ℝ) hhalf T hT
  have hzero_idem := peirce_idempotent_zero (A := Matrix (Fin n) (Fin n) ℝ) T hT
  have hplus_star : star
      (projPlus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T) =
      projPlus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T := by
    simp [projPlus, hTstar]
  have hminus_star : star
      (projMinus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T) =
      projMinus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T := by
    simp [projMinus, hTstar]
  have hzero_star : star (projZero T) = projZero T := by
    simp [projZero, hTstar]
  have hplus_transpose :
      (projPlus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T).transpose =
        projPlus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hplus_star
    simpa [Matrix.star_apply, Matrix.transpose_apply] using hij
  have hminus_transpose :
      (projMinus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T).transpose =
        projMinus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hminus_star
    simpa [Matrix.star_apply, Matrix.transpose_apply] using hij
  have hzero_transpose : (projZero T).transpose = projZero T := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hzero_star
    simpa [Matrix.star_apply, Matrix.transpose_apply] using hij
  refine ⟨?_, ?_, ?_⟩
  · have hp := Matrix.posSemidef_conjTranspose_mul_self
      (projPlus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hplus_transpose, hplus_idem] at hp
    exact hp
  · have hp := Matrix.posSemidef_conjTranspose_mul_self
      (projMinus (R := ℝ) (A := Matrix (Fin n) (Fin n) ℝ) (1 / 2 : ℝ) T)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hminus_transpose, hminus_idem] at hp
    exact hp
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hzero_transpose, hzero_idem] using
      (Matrix.posSemidef_conjTranspose_mul_self (projZero T))

end RealMatrixPeircePositivity

end InfoGeometry.Modular.TrifactorTripotentUnification
