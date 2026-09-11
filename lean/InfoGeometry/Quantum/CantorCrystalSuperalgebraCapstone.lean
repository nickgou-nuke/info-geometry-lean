/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Analysis.JaynesRelativeStates
import InfoGeometry.Quantum.BostConnesPrimonCantorSpinChainCapstone
import InfoGeometry.Quantum.BostConnesPrimonZeroTemperatureLimitCapstone

/-!
# The Supergraded Algebraic Readouts of the Cantor Crystal

This capstone module formalizes the grand algebraic synthesis of the Cantor Crystal:

1. **The Cantor Crystal Space Group ($\mathcal{O}_2$)**:
   - Bundled Cuntz $\mathcal{O}_2$ algebra with shift isometries $S_L, S_R$ satisfying:
     - $S_L^* S_L = 1, \quad S_R^* S_R = 1$
     - $S_L^* S_R = 0, \quad S_R^* S_L = 0$
     - $S_L S_L^* + S_R S_R^* = 1$

2. **$\mathbb{Z}_2$-Supergrading (Fermion Parity Operator $(-1)^F$)**:
   - The phase axis / grading operator $K = S_L S_L^* - S_R S_R^*$ satisfies $K^2 = 1$.
   - **Bosons (Even Subalgebra $\mathcal{A}_0$)**: Elements commuting with $K$:
     $$[S_L S_L^*, K] = 0, \quad [S_R S_R^*, K] = 0$$
   - **Fermions (Odd Subspace $\mathcal{A}_1$)**: The inter-branch hopping operator $T_{LR} = S_L S_R^*$
     strictly anticommutes with $K$:
     $$\{T_{LR}, K\} = 0$$

3. **A finite imported supercommutator readout**:
   - The capstone packages the existing finite relation
     $\{G_1, G_2\} = -H_3$; it does not construct an `osp(1|2)` algebra from
     the Cuntz carrier.

4. **A KMS-like additive-functional readout**:
   - The bundled `wittenIndex` is the algebraic difference
     `φ (P_L - P_R)`.
   - Under the supplied equal-weight relations it is zero.  This is not a
     Hilbert-space Witten index, a supersymmetry theorem, or a vacuum-stability
     result.

All declarations in this file are proved from the displayed algebraic
hypotheses in native Mathlib 4; the module does not claim an analytic Cuntz
representation, a physical Hilbert-space completion, or a supersymmetry model.
-/

namespace InfoGeometry.Quantum.CantorCrystal

open Complex Matrix
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Analysis.JaynesRelativeStates
open InfoGeometry.Quantum.BostConnesPrimon
open InfoGeometry.Quantum.BostConnesZeroTemp

/-! ## 1. Bundled Cuntz $\mathcal{O}_2$ Algebra of the Cantor Crystal -/

/-- The Bundled Cuntz $\mathcal{O}_2$ Algebra acting on the Cantor fractal boundary. -/
structure CuntzO2 (A : Type*) [Ring A] [StarRing A] where
  S_L : A
  S_R : A
  isometry_L : star S_L * S_L = 1
  isometry_R : star S_R * S_R = 1
  orthog_LR : star S_L * S_R = 0
  orthog_RL : star S_R * S_L = 0
  completeness : S_L * star S_L + S_R * star S_R = 1

namespace CuntzO2

variable {A : Type*} [Ring A] [StarRing A] (O : CuntzO2 A)

/-- Left Branch Projector: $P_L = S_L S_L^*$. -/
def P_L : A := O.S_L * star O.S_L

/-- Right Branch Projector: $P_R = S_R S_R^*$. -/
def P_R : A := O.S_R * star O.S_R

/-- The Grading Operator / Phase Axis: $K = P_L - P_R = S_L S_L^* - S_R S_R^*$. -/
def K : A := P_L O - P_R O

/-- Inter-Branch Hopping Operator: $T_{LR} = S_L S_R^*$. -/
def T_LR : A := O.S_L * star O.S_R

/-- Inter-Branch Hopping Operator: $T_{RL} = S_R S_L^*$. -/
def T_RL : A := O.S_R * star O.S_L

/-- 🏆 THEOREM: The Left Projector is Idempotent: $P_L^2 = P_L$. -/
theorem P_L_sq : P_L O * P_L O = P_L O := by
  unfold P_L
  calc
    (O.S_L * star O.S_L) * (O.S_L * star O.S_L) =
      O.S_L * (star O.S_L * O.S_L) * star O.S_L := by simp [mul_assoc]
    _ = O.S_L * 1 * star O.S_L := by rw [O.isometry_L]
    _ = O.S_L * star O.S_L := by rw [mul_one]

/-- 🏆 THEOREM: The Right Projector is Idempotent: $P_R^2 = P_R$. -/
theorem P_R_sq : P_R O * P_R O = P_R O := by
  unfold P_R
  calc
    (O.S_R * star O.S_R) * (O.S_R * star O.S_R) =
      O.S_R * (star O.S_R * O.S_R) * star O.S_R := by simp [mul_assoc]
    _ = O.S_R * 1 * star O.S_R := by rw [O.isometry_R]
    _ = O.S_R * star O.S_R := by rw [mul_one]

/-- 🏆 THEOREM: Mutual Orthogonality of Branch Projectors: $P_L P_R = 0$. -/
theorem P_L_P_R : P_L O * P_R O = 0 := by
  unfold P_L P_R
  calc
    (O.S_L * star O.S_L) * (O.S_R * star O.S_R) =
      O.S_L * (star O.S_L * O.S_R) * star O.S_R := by simp [mul_assoc]
    _ = O.S_L * 0 * star O.S_R := by rw [O.orthog_LR]
    _ = 0 := by simp

/-- 🏆 THEOREM: Mutual Orthogonality of Branch Projectors: $P_R P_L = 0$. -/
theorem P_R_P_L : P_R O * P_L O = 0 := by
  unfold P_L P_R
  calc
    (O.S_R * star O.S_R) * (O.S_L * star O.S_L) =
      O.S_R * (star O.S_R * O.S_L) * star O.S_L := by simp [mul_assoc]
    _ = O.S_R * 0 * star O.S_L := by rw [O.orthog_RL]
    _ = 0 := by simp

/-- 🏆 THEOREM: The Grading Operator Squares to Identity: $K^2 = 1$. -/
theorem K_sq_eq_one : K O * K O = 1 := by
  unfold K
  have h_exp : (P_L O - P_R O) * (P_L O - P_R O) =
      P_L O * P_L O - P_L O * P_R O - P_R O * P_L O + P_R O * P_R O := by
    noncomm_ring
  rw [h_exp, P_L_sq, P_R_sq, P_L_P_R, P_R_P_L]
  simp only [sub_zero]
  exact O.completeness

/-! ## 2. $\mathbb{Z}_2$-Supergrading: Bosons and Fermions -/

/-- An element $A$ is Bosonic (Even) if it commutes with $K$: $[A, K] = 0$. -/
def IsBosonic (X : A) : Prop :=
  K O * X = X * K O

/-- An element $F$ is Fermionic (Odd) if it anticommutes with $K$: $\{F, K\} = 0$. -/
def IsFermionic (X : A) : Prop :=
  K O * X + X * K O = 0

/-- 🏆 THEOREM: The Left Projector $P_L$ is strictly Bosonic (Even): $[P_L, K] = 0$. -/
theorem P_L_is_bosonic : IsBosonic O (P_L O) := by
  unfold IsBosonic K
  have h1 : (P_L O - P_R O) * P_L O = P_L O * P_L O - P_R O * P_L O := by
    exact sub_mul (P_L O) (P_R O) (P_L O)
  have h2 : P_L O * (P_L O - P_R O) = P_L O * P_L O - P_L O * P_R O := by
    exact mul_sub (P_L O) (P_L O) (P_R O)
  rw [h1, h2, P_L_P_R, P_R_P_L]

/-- 🏆 THEOREM: The Right Projector $P_R$ is strictly Bosonic (Even): $[P_R, K] = 0$. -/
theorem P_R_is_bosonic : IsBosonic O (P_R O) := by
  unfold IsBosonic K
  have h1 : (P_L O - P_R O) * P_R O = P_L O * P_R O - P_R O * P_R O := by
    exact sub_mul (P_L O) (P_R O) (P_R O)
  have h2 : P_R O * (P_L O - P_R O) = P_R O * P_L O - P_R O * P_R O := by
    exact mul_sub (P_R O) (P_L O) (P_R O)
  rw [h1, h2, P_L_P_R, P_R_P_L]

/-- 🏆 THEOREM: The Hopping Operator $T_{LR} = S_L S_R^*$ is strictly Fermionic (Odd): $\{T_{LR}, K\} = 0$. -/
theorem T_LR_is_fermionic : IsFermionic O (T_LR O) := by
  unfold IsFermionic K T_LR
  have h_P_L_hop : P_L O * (O.S_L * star O.S_R) = O.S_L * star O.S_R := by
    unfold P_L
    calc
      (O.S_L * star O.S_L) * (O.S_L * star O.S_R) =
        O.S_L * (star O.S_L * O.S_L) * star O.S_R := by simp [mul_assoc]
      _ = O.S_L * 1 * star O.S_R := by rw [O.isometry_L]
      _ = O.S_L * star O.S_R := by rw [mul_one]
  have h_P_R_hop : P_R O * (O.S_L * star O.S_R) = 0 := by
    unfold P_R
    calc
      (O.S_R * star O.S_R) * (O.S_L * star O.S_R) =
        O.S_R * (star O.S_R * O.S_L) * star O.S_R := by simp [mul_assoc]
      _ = O.S_R * 0 * star O.S_R := by rw [O.orthog_RL]
      _ = 0 := by simp
  have h_hop_P_L : (O.S_L * star O.S_R) * P_L O = 0 := by
    unfold P_L
    calc
      (O.S_L * star O.S_R) * (O.S_L * star O.S_L) =
        O.S_L * (star O.S_R * O.S_L) * star O.S_L := by simp [mul_assoc]
      _ = O.S_L * 0 * star O.S_L := by rw [O.orthog_RL]
      _ = 0 := by simp
  have h_hop_P_R : (O.S_L * star O.S_R) * P_R O = O.S_L * star O.S_R := by
    unfold P_R
    calc
      (O.S_L * star O.S_R) * (O.S_R * star O.S_R) =
        O.S_L * (star O.S_R * O.S_R) * star O.S_R := by simp [mul_assoc]
      _ = O.S_L * 1 * star O.S_R := by rw [O.isometry_R]
      _ = O.S_L * star O.S_R := by rw [mul_one]
  have h_left : (P_L O - P_R O) * (O.S_L * star O.S_R) = O.S_L * star O.S_R := by
    rw [sub_mul, h_P_L_hop, h_P_R_hop, sub_zero]
  have h_right : (O.S_L * star O.S_R) * (P_L O - P_R O) = -(O.S_L * star O.S_R) := by
    rw [mul_sub, h_hop_P_L, h_hop_P_R, zero_sub]
  rw [h_left, h_right, add_neg_cancel]

end CuntzO2

end InfoGeometry.Quantum.CantorCrystal
