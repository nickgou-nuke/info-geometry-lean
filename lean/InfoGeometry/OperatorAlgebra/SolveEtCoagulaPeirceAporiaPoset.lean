/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.Core.IdempotentGraphGrassmannian
import InfoGeometry.Core.IdempotentDefectIteration
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
import InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
import InfoGeometry.Algebra.KreinPeirceTowerIntertwine
import InfoGeometry.Meta

/-!
# Epistemic Compiler Solve et Coagula Noncommutative Peirce–Aporia–Tower Poset

Canonical owner for Milestone 6E: implements the 5-stage causal compilation chain
$\mathcal{E}\mathcal{C}_1 \prec \dots \prec \mathcal{E}\mathcal{C}_5$:
1. $\mathcal{E}\mathcal{C}_1$: Primordial binary cut idempotent complementation and grading laws.
2. $\mathcal{E}\mathcal{C}_2$: Fourfold relational Peirce decomposition and quiver multiplication.
3. $\mathcal{E}\mathcal{C}_3$: Transcendent quartet algebra $(\Phi, J, V, \Sigma)$ and universal creation lock.
4. $\mathcal{E}\mathcal{C}_4$: Socratic aporia boundary defect, Newton–Peirce tower, infinite orbit in $M_2(M_2(\mathbb{Z}))$, and $Cl$-tower transport.
5. $\mathcal{E}\mathcal{C}_5$: Bounded acyclic causal poset `SolveEtCoagulaNode`, rank grading, and master synthesis.
-/

namespace InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Algebra.KreinPeirceTowerIntertwine

/-! ### Matrix Witnesses & Setup -/

/-- OpenGauss T16 matrix cut projector witness on `Matrix (Fin 2) (Fin 2) B`. -/
def cutMat2 {B : Type*} [Zero B] [One B] : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, 0]

/-- OpenGauss T16 matrix probe operator witness on `Matrix (Fin 2) (Fin 2) B`. -/
def probeMat2 {B : Type*} [Zero B] [One B] : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 1, 0]

variable {R : Type*} [Ring R]

/-! ### Section 1: Primordial Binary Cut & Characteristic-Free Non-Commutative Asymmetry -/

/-- **Binary Cut Idempotent & Grading Laws**:
For any ring `R` and idempotent `P : R` (`P * P = P`), with complement `Q = 1 - P` and
Peirce grading involution `S = invS P = P - (1 - P)`:
1. `Q * Q = Q`, `P * Q = 0`, `Q * P = 0`;
2. `S * S = 1`, `S * P = P`, `P * S = P`, `S * Q = -Q`, `Q * S = -Q`.
All identities hold in every associative ring without scalar or division hypotheses. -/
theorem binary_cut_idempotent_and_grading_laws
    (P : R) (hP : P * P = P) :
    let Q := 1 - P
    let S := invS P
    Q * Q = Q ∧
    P * Q = 0 ∧
    Q * P = 0 ∧
    S * S = 1 ∧
    S * P = P ∧
    P * S = P ∧
    S * Q = -Q ∧
    Q * S = -Q := by
  intro Q S
  have hQ : Q * Q = Q := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  have hPQ : P * Q = 0 := by
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hQP : Q * P = 0 := by
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hSS : S * S = 1 := by
    calc
      (P - (1 - P)) * (P - (1 - P))
        = P * P - P * (1 - P) - (1 - P) * P + (1 - P) * (1 - P) := by noncomm_ring
      _ = P - 0 - 0 + (1 - P) := by rw [hP, hPQ, hQP, hQ]
      _ = 1 := by noncomm_ring
  have hSP : S * P = P := by
    calc
      (P - (1 - P)) * P = P * P - (1 - P) * P := by noncomm_ring
      _ = P - 0 := by rw [hP, hQP]
      _ = P := sub_zero P
  have hPS : P * S = P := by
    calc
      P * (P - (1 - P)) = P * P - P * (1 - P) := by noncomm_ring
      _ = P - 0 := by rw [hP, hPQ]
      _ = P := sub_zero P
  have hSQ : S * Q = -Q := by
    calc
      (P - (1 - P)) * (1 - P) = P * (1 - P) - (1 - P) * (1 - P) := by noncomm_ring
      _ = 0 - (1 - P) := by rw [hPQ, hQ]
      _ = -(1 - P) := zero_sub (1 - P)
  have hQS : Q * S = -Q := by
    calc
      (1 - P) * (P - (1 - P)) = (1 - P) * P - (1 - P) * (1 - P) := by noncomm_ring
      _ = 0 - (1 - P) := by rw [hQP, hQ]
      _ = -(1 - P) := zero_sub (1 - P)
  exact ⟨hQ, hPQ, hQP, hSS, hSP, hPS, hSQ, hQS⟩

/-- **Binary Cut Commute Iff Corners Zero (Characteristic-Free)**:
In any associative ring `R` (even of characteristic 2):
1. `peirceGradingDeriv P X = 0 ↔ conePlus P X = 0 ∧ coneMinus P X = 0`;
2. `P * X = X * P ↔ X = evenGrade P X`;
3. `X = evenGrade P X ↔ oddGrade P X = 0`. -/
theorem binary_cut_commute_iff_corners_zero
    (P X : R) (hP : P * P = P) :
    (peirceGradingDeriv P X = 0 ↔ conePlus P X = 0 ∧ coneMinus P X = 0) ∧
    (P * X = X * P ↔ X = evenGrade P X) ∧
    (X = evenGrade P X ↔ oddGrade P X = 0) := by
  have hP_sub : P * (1 - P) = 0 := by
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hsub_P : (1 - P) * P = 0 := by
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]

  have hPart1 : peirceGradingDeriv P X = 0 ↔ conePlus P X = 0 ∧ coneMinus P X = 0 := by
    constructor
    · intro h
      change P * X - X * P = 0 at h
      have hcomm : P * X = X * P := sub_eq_zero.mp h
      have hPlus : conePlus P X = 0 := by
        calc
          conePlus P X = P * X * (1 - P) := rfl
          _ = (X * P) * (1 - P) := by rw [hcomm]
          _ = X * (P * (1 - P)) := by noncomm_ring
          _ = X * 0 := by rw [hP_sub]
          _ = 0 := mul_zero X
      have hMinus : coneMinus P X = 0 := by
        calc
          coneMinus P X = (1 - P) * X * P := rfl
          _ = (1 - P) * (X * P) := by noncomm_ring
          _ = (1 - P) * (P * X) := by rw [hcomm.symm]
          _ = ((1 - P) * P) * X := by noncomm_ring
          _ = 0 * X := by rw [hsub_P]
          _ = 0 := zero_mul X
      exact ⟨hPlus, hMinus⟩
    · rintro ⟨hPlus, hMinus⟩
      change P * X - X * P = 0
      calc
        P * X - X * P = P * X * (1 - P) - (1 - P) * X * P := by noncomm_ring
        _ = conePlus P X - coneMinus P X := rfl
        _ = 0 - 0 := by rw [hPlus, hMinus]
        _ = 0 := sub_self 0

  have hdecomp : evenGrade P X + oddGrade P X = X :=
    (grade_projection_laws hP X).2.2.2.2

  have hPart3 : X = evenGrade P X ↔ oddGrade P X = 0 := by
    constructor
    · intro h
      have hsum : evenGrade P X + oddGrade P X = evenGrade P X := by
        calc
          evenGrade P X + oddGrade P X = X := hdecomp
          _ = evenGrade P X := h
      calc
        oddGrade P X = (evenGrade P X + oddGrade P X) - evenGrade P X := by abel
        _ = evenGrade P X - evenGrade P X := by rw [hsum]
        _ = 0 := sub_self _
    · intro h
      calc
        X = evenGrade P X + oddGrade P X := hdecomp.symm
        _ = evenGrade P X + 0 := by rw [h]
        _ = evenGrade P X := by rw [add_zero]

  have hPart2 : P * X = X * P ↔ X = evenGrade P X := by
    constructor
    · intro hcomm
      have hDeriv : peirceGradingDeriv P X = 0 := by
        change P * X - X * P = 0
        exact sub_eq_zero.mpr hcomm
      have ⟨hPlus, hMinus⟩ := hPart1.mp hDeriv
      have hOdd : oddGrade P X = 0 := by
        calc
          oddGrade P X = conePlus P X + coneMinus P X := rfl
          _ = 0 + 0 := by rw [hPlus, hMinus]
          _ = 0 := add_zero 0
      exact hPart3.mpr hOdd
    · intro hEven
      have hPeven : P * evenGrade P X = P * X * P := by
        unfold evenGrade
        calc
          P * (P * X * P + (1 - P) * X * (1 - P))
            = (P * P) * X * P + (P * (1 - P)) * X * (1 - P) := by noncomm_ring
          _ = P * X * P + 0 * X * (1 - P) := by rw [hP, hP_sub]
          _ = P * X * P := by simp only [zero_mul, add_zero]
      have hevenP : evenGrade P X * P = P * X * P := by
        unfold evenGrade
        calc
          (P * X * P + (1 - P) * X * (1 - P)) * P
            = P * X * (P * P) + (1 - P) * X * ((1 - P) * P) := by noncomm_ring
          _ = P * X * P + (1 - P) * X * 0 := by rw [hP, hsub_P]
          _ = P * X * P := by simp only [mul_zero, add_zero]
      calc
        P * X = P * evenGrade P X := congrArg (fun a => P * a) hEven
        _ = P * X * P := hPeven
        _ = evenGrade P X * P := hevenP.symm
        _ = X * P := congrArg (fun a => a * P) hEven.symm

  exact ⟨hPart1, hPart2, hPart3⟩

/-- Idempotency of the binary cut witness `cutMat2`. -/
theorem cutMat2_idempotent {B : Type*} [Ring B] :
    (cutMat2 : Matrix (Fin 2) (Fin 2) B) * cutMat2 = cutMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cutMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Non-commutativity of `cutMat2` and `probeMat2` over any nontrivial ring `B`. -/
theorem cutMat2_probeMat2_noncomm {B : Type*} [Ring B] [Nontrivial B] :
    (cutMat2 : Matrix (Fin 2) (Fin 2) B) * probeMat2 ≠ probeMat2 * cutMat2 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  revert h01
  simp [cutMat2, probeMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Binary Cut Mat2 Noncommuting (OpenGauss T16 Witness)**:
Over any nontrivial ring `B`, `cutMat2` is an idempotent projector and does not
commute with the off-diagonal probe operator `probeMat2`. -/
theorem binary_cut_mat2_noncommuting {B : Type*} [Ring B] [Nontrivial B] :
    (cutMat2 : Matrix (Fin 2) (Fin 2) B) * cutMat2 = cutMat2 ∧
    (cutMat2 : Matrix (Fin 2) (Fin 2) B) * probeMat2 ≠ probeMat2 * cutMat2 :=
  ⟨cutMat2_idempotent, cutMat2_probeMat2_noncomm⟩

/-! ### Section 2: Fourfold Relational Peirce Anatomy & Noncommutative Quiver Multiplication -/

/-- **Peirce Fourfold Decomposition**:
Every element `X` decomposes uniquely into its 4 Peirce corner components:
`X = peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X`. -/
theorem peirce_fourfold_decomp (P X : R) (hP : P * P = P) :
    X = peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X := by
  calc
    X = evenGrade P X + oddGrade P X := (grade_projection_laws hP X).2.2.2.2.symm
    _ = (peirce11 P X + peirce00 P X) + (conePlus P X + coneMinus P X) := rfl
    _ = peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X := by abel

/-- **Peirce Fourfold Direct Sum Unique**:
If 4 corner elements sum to zero, each corner element must independently vanish.
This establishes the direct sum decomposition `R = R₁₁ ⊕ R₁₀ ⊕ R₀₁ ⊕ R₀₀`. -/
theorem peirce_fourfold_direct_sum_unique (P : R) (hP : P * P = P)
    (X₁₁ X₁₀ X₀₁ X₀₀ : R)
    (h11 : X₁₁ = P * X₁₁ * P)
    (h10 : X₁₀ = P * X₁₀ * (1 - P))
    (h01 : X₀₁ = (1 - P) * X₀₁ * P)
    (h00 : X₀₀ = (1 - P) * X₀₀ * (1 - P))
    (hsum : X₁₁ + X₁₀ + X₀₁ + X₀₀ = 0) :
    X₁₁ = 0 ∧ X₁₀ = 0 ∧ X₀₁ = 0 ∧ X₀₀ = 0 := by
  have hP_sub : P * (1 - P) = 0 := by
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hsub_P : (1 - P) * P = 0 := by
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hsub_sub : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring

  have h11_P : P * X₁₁ * P = X₁₁ := by
    conv_lhs => rw [h11]
    calc
      P * (P * X₁₁ * P) * P = (P * P) * X₁₁ * (P * P) := by noncomm_ring
      _ = P * X₁₁ * P := by rw [hP]
      _ = X₁₁ := h11.symm

  have h10_P : P * X₁₀ * P = 0 := by
    conv_lhs => rw [h10]
    calc
      P * (P * X₁₀ * (1 - P)) * P = (P * P) * X₁₀ * ((1 - P) * P) := by noncomm_ring
      _ = P * X₁₀ * 0 := by rw [hP, hsub_P]
      _ = 0 := by rw [mul_zero]

  have h01_P : P * X₀₁ * P = 0 := by
    conv_lhs => rw [h01]
    calc
      P * ((1 - P) * X₀₁ * P) * P = (P * (1 - P)) * X₀₁ * (P * P) := by noncomm_ring
      _ = 0 * X₀₁ * P := by rw [hP, hP_sub]
      _ = 0 := by rw [zero_mul, zero_mul]

  have h00_P : P * X₀₀ * P = 0 := by
    conv_lhs => rw [h00]
    calc
      P * ((1 - P) * X₀₀ * (1 - P)) * P = (P * (1 - P)) * X₀₀ * ((1 - P) * P) := by noncomm_ring
      _ = 0 * X₀₀ * 0 := by rw [hP_sub, hsub_P]
      _ = 0 := by rw [zero_mul, zero_mul]

  have e11 : X₁₁ = 0 := by
    calc
      X₁₁ = P * X₁₁ * P := h11_P.symm
      _ = P * (X₁₁ + X₁₀ + X₀₁ + X₀₀) * P := by
        simp only [mul_add, add_mul, h10_P, h01_P, h00_P, add_zero]
      _ = P * 0 * P := by rw [hsum]
      _ = 0 := by simp only [mul_zero, zero_mul]

  have h11_Q : P * X₁₁ * (1 - P) = 0 := by
    conv_lhs => rw [h11]
    calc
      P * (P * X₁₁ * P) * (1 - P) = (P * P) * X₁₁ * (P * (1 - P)) := by noncomm_ring
      _ = P * X₁₁ * 0 := by rw [hP, hP_sub]
      _ = 0 := by rw [mul_zero]

  have h10_Q : P * X₁₀ * (1 - P) = X₁₀ := by
    conv_lhs => rw [h10]
    calc
      P * (P * X₁₀ * (1 - P)) * (1 - P) = (P * P) * X₁₀ * ((1 - P) * (1 - P)) := by noncomm_ring
      _ = P * X₁₀ * (1 - P) := by rw [hP, hsub_sub]
      _ = X₁₀ := h10.symm

  have h01_Q : P * X₀₁ * (1 - P) = 0 := by
    conv_lhs => rw [h01]
    calc
      P * ((1 - P) * X₀₁ * P) * (1 - P) = (P * (1 - P)) * X₀₁ * (P * (1 - P)) := by noncomm_ring
      _ = 0 * X₀₁ * 0 := by rw [hP_sub]
      _ = 0 := by rw [zero_mul, zero_mul]

  have h00_Q : P * X₀₀ * (1 - P) = 0 := by
    conv_lhs => rw [h00]
    calc
      P * ((1 - P) * X₀₀ * (1 - P)) * (1 - P) = (P * (1 - P)) * X₀₀ * ((1 - P) * (1 - P)) := by noncomm_ring
      _ = 0 * X₀₀ * (1 - P) := by rw [hP_sub, hsub_sub]
      _ = 0 := by rw [zero_mul, zero_mul]

  have e10 : X₁₀ = 0 := by
    calc
      X₁₀ = P * X₁₀ * (1 - P) := h10_Q.symm
      _ = P * (X₁₁ + X₁₀ + X₀₁ + X₀₀) * (1 - P) := by
        simp only [mul_add, add_mul, h11_Q, h01_Q, h00_Q, add_zero, zero_add]
      _ = P * 0 * (1 - P) := by rw [hsum]
      _ = 0 := by simp only [mul_zero, zero_mul]

  have h11_QP : (1 - P) * X₁₁ * P = 0 := by
    conv_lhs => rw [h11]
    calc
      (1 - P) * (P * X₁₁ * P) * P = ((1 - P) * P) * X₁₁ * (P * P) := by noncomm_ring
      _ = 0 * X₁₁ * P := by rw [hP, hsub_P]
      _ = 0 := by rw [zero_mul, zero_mul]

  have h10_QP : (1 - P) * X₁₀ * P = 0 := by
    conv_lhs => rw [h10]
    calc
      (1 - P) * (P * X₁₀ * (1 - P)) * P = ((1 - P) * P) * X₁₀ * ((1 - P) * P) := by noncomm_ring
      _ = 0 * X₁₀ * 0 := by rw [hsub_P]
      _ = 0 := by rw [zero_mul, zero_mul]

  have h01_QP : (1 - P) * X₀₁ * P = X₀₁ := by
    conv_lhs => rw [h01]
    calc
      (1 - P) * ((1 - P) * X₀₁ * P) * P = ((1 - P) * (1 - P)) * X₀₁ * (P * P) := by noncomm_ring
      _ = (1 - P) * X₀₁ * P := by rw [hP, hsub_sub]
      _ = X₀₁ := h01.symm

  have h00_QP : (1 - P) * X₀₀ * P = 0 := by
    conv_lhs => rw [h00]
    calc
      (1 - P) * ((1 - P) * X₀₀ * (1 - P)) * P = ((1 - P) * (1 - P)) * X₀₀ * ((1 - P) * P) := by noncomm_ring
      _ = (1 - P) * X₀₀ * 0 := by rw [hsub_P, hsub_sub]
      _ = 0 := by rw [mul_zero]

  have e01 : X₀₁ = 0 := by
    calc
      X₀₁ = (1 - P) * X₀₁ * P := h01_QP.symm
      _ = (1 - P) * (X₁₁ + X₁₀ + X₀₁ + X₀₀) * P := by
        simp only [mul_add, add_mul, h11_QP, h10_QP, h00_QP, add_zero, zero_add]
      _ = (1 - P) * 0 * P := by rw [hsum]
      _ = 0 := by simp only [mul_zero, zero_mul]

  have h11_QQ : (1 - P) * X₁₁ * (1 - P) = 0 := by
    conv_lhs => rw [h11]
    calc
      (1 - P) * (P * X₁₁ * P) * (1 - P) = ((1 - P) * P) * X₁₁ * (P * (1 - P)) := by noncomm_ring
      _ = 0 * X₁₁ * 0 := by rw [hsub_P, hP_sub]
      _ = 0 := by rw [zero_mul, zero_mul]

  have h10_QQ : (1 - P) * X₁₀ * (1 - P) = 0 := by
    conv_lhs => rw [h10]
    calc
      (1 - P) * (P * X₁₀ * (1 - P)) * (1 - P) = ((1 - P) * P) * X₁₀ * ((1 - P) * (1 - P)) := by noncomm_ring
      _ = 0 * X₁₀ * (1 - P) := by rw [hsub_P, hsub_sub]
      _ = 0 := by rw [zero_mul, zero_mul]

  have h01_QQ : (1 - P) * X₀₁ * (1 - P) = 0 := by
    conv_lhs => rw [h01]
    calc
      (1 - P) * ((1 - P) * X₀₁ * P) * (1 - P) = ((1 - P) * (1 - P)) * X₀₁ * (P * (1 - P)) := by noncomm_ring
      _ = (1 - P) * X₀₁ * 0 := by rw [hP_sub, hsub_sub]
      _ = 0 := by rw [mul_zero]

  have h00_QQ : (1 - P) * X₀₀ * (1 - P) = X₀₀ := by
    conv_lhs => rw [h00]
    calc
      (1 - P) * ((1 - P) * X₀₀ * (1 - P)) * (1 - P) = ((1 - P) * (1 - P)) * X₀₀ * ((1 - P) * (1 - P)) := by noncomm_ring
      _ = (1 - P) * X₀₀ * (1 - P) := by rw [hsub_sub]
      _ = X₀₀ := h00.symm

  have e00 : X₀₀ = 0 := by
    calc
      X₀₀ = (1 - P) * X₀₀ * (1 - P) := h00_QQ.symm
      _ = (1 - P) * (X₁₁ + X₁₀ + X₀₁ + X₀₀) * (1 - P) := by
        simp only [mul_add, add_mul, h11_QQ, h10_QQ, h01_QQ, add_zero, zero_add]
      _ = (1 - P) * 0 * (1 - P) := by rw [hsum]
      _ = 0 := by simp only [mul_zero, zero_mul]

  exact ⟨e11, e10, e01, e00⟩

/-- **Peirce Fourfold Mul Table (Quiver Path Multiplication)**:
Corner multiplication table for the 2-vertex Peirce quiver:
1. `peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y`
2. `peirce00 P (X * Y) = peirce00 P X * peirce00 P Y + coneMinus P X * conePlus P Y`
3. `conePlus P (X * Y) = peirce11 P X * conePlus P Y + conePlus P X * peirce00 P Y`
4. `coneMinus P (X * Y) = coneMinus P X * peirce11 P Y + peirce00 P X * coneMinus P Y`. -/
theorem peirce_fourfold_mul_table (P : R) (hP : P * P = P) (X Y : R) :
    peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y ∧
    peirce00 P (X * Y) = peirce00 P X * peirce00 P Y + coneMinus P X * conePlus P Y ∧
    conePlus P (X * Y) = peirce11 P X * conePlus P Y + conePlus P X * peirce00 P Y ∧
    coneMinus P (X * Y) = coneMinus P X * peirce11 P Y + peirce00 P X * coneMinus P Y := by
  have hQidem : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [peirce11, conePlus, coneMinus]
    calc
      P * (X * Y) * P = P * X * Y * P := by noncomm_ring
      _ = P * X * 1 * Y * P := by rw [mul_one]
      _ = P * X * (P + (1 - P)) * Y * P := by rw [add_sub_cancel]
      _ = P * X * P * Y * P + P * X * (1 - P) * Y * P := by noncomm_ring
      _ = P * X * (P * P) * Y * P + P * X * ((1 - P) * (1 - P)) * Y * P := by rw [hP, hQidem]
      _ = P * X * P * (P * Y * P) + P * X * (1 - P) * ((1 - P) * Y * P) := by noncomm_ring
  · simp only [peirce00, coneMinus, conePlus]
    calc
      (1 - P) * (X * Y) * (1 - P) = (1 - P) * X * Y * (1 - P) := by noncomm_ring
      _ = (1 - P) * X * 1 * Y * (1 - P) := by rw [mul_one]
      _ = (1 - P) * X * ((1 - P) + P) * Y * (1 - P) := by rw [sub_add_cancel]
      _ = (1 - P) * X * (1 - P) * Y * (1 - P) + (1 - P) * X * P * Y * (1 - P) := by noncomm_ring
      _ = (1 - P) * X * ((1 - P) * (1 - P)) * Y * (1 - P) + (1 - P) * X * (P * P) * Y * (1 - P) := by rw [hP, hQidem]
      _ = (1 - P) * X * (1 - P) * ((1 - P) * Y * (1 - P)) + (1 - P) * X * P * (P * Y * (1 - P)) := by noncomm_ring
  · simp only [conePlus, peirce11, peirce00]
    calc
      P * (X * Y) * (1 - P) = P * X * Y * (1 - P) := by noncomm_ring
      _ = P * X * 1 * Y * (1 - P) := by rw [mul_one]
      _ = P * X * (P + (1 - P)) * Y * (1 - P) := by rw [add_sub_cancel]
      _ = P * X * P * Y * (1 - P) + P * X * (1 - P) * Y * (1 - P) := by noncomm_ring
      _ = P * X * (P * P) * Y * (1 - P) + P * X * ((1 - P) * (1 - P)) * Y * (1 - P) := by rw [hP, hQidem]
      _ = P * X * P * (P * Y * (1 - P)) + P * X * (1 - P) * ((1 - P) * Y * (1 - P)) := by noncomm_ring
  · simp only [coneMinus, peirce11, peirce00]
    calc
      (1 - P) * (X * Y) * P = (1 - P) * X * Y * P := by noncomm_ring
      _ = (1 - P) * X * 1 * Y * P := by rw [mul_one]
      _ = (1 - P) * X * (P + (1 - P)) * Y * P := by rw [add_sub_cancel]
      _ = (1 - P) * X * P * Y * P + (1 - P) * X * (1 - P) * Y * P := by noncomm_ring
      _ = (1 - P) * X * (P * P) * Y * P + (1 - P) * X * ((1 - P) * (1 - P)) * Y * P := by rw [hP, hQidem]
      _ = (1 - P) * X * P * (P * Y * P) + (1 - P) * X * (1 - P) * ((1 - P) * Y * P) := by noncomm_ring

/-- Upper-corner matrix projection evaluation on `(cutMat2, probeMat2)`. -/
theorem conePlus_cutMat2_probeMat2 {B : Type*} [Ring B] :
    conePlus (cutMat2 : Matrix (Fin 2) (Fin 2) B) probeMat2 = !![0, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conePlus, cutMat2, probeMat2, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- Lower-corner matrix projection evaluation on `(cutMat2, probeMat2)`. -/
theorem coneMinus_cutMat2_probeMat2 {B : Type*} [Ring B] :
    coneMinus (cutMat2 : Matrix (Fin 2) (Fin 2) B) probeMat2 = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coneMinus, cutMat2, probeMat2, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- **Strict Order-Asymmetry Witness**:
Over any nontrivial ring `B`, `conePlus` and `coneMinus` do not commute:
`conePlus cutMat2 probeMat2 * coneMinus cutMat2 probeMat2 ≠ coneMinus cutMat2 probeMat2 * conePlus cutMat2 probeMat2`. -/
theorem peirce_order_asymmetry_witness {B : Type*} [Ring B] [Nontrivial B] :
    conePlus (cutMat2 : Matrix (Fin 2) (Fin 2) B) probeMat2 *
      coneMinus cutMat2 probeMat2 ≠
    coneMinus cutMat2 probeMat2 *
      conePlus cutMat2 probeMat2 := by
  rw [conePlus_cutMat2_probeMat2, coneMinus_cutMat2_probeMat2]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Section 3: The Transcendent Function (Phi, J, V, Sigma), Universal Creation Lock, Bruhat Tilt & Noncommutative Fiber Curvature -/

/-- Transcendent quartet algebra: complete quadratic, commutation, and grading duality laws
for the Peirce generators (Phi, J, V, Sigma). -/
theorem transcendent_quartet_algebra {P : R} (hP : P * P = P) (A C : R) :
    peirceGradingDeriv P (genPhi P A C) = genJ P A C ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    anticomm (genJ P A C) (genPhi P A C) = 0 ∧
    comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C ∧
    (invS P * genV P A C = genSig P A C ∧ genV P A C * invS P = genSig P A C) ∧
    (invS P * genSig P A C = genV P A C ∧ genSig P A C * invS P = genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold peirceGradingDeriv; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · rw [two_zsmul]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- Universal creation lock: the boundary Jordan mass `V` vanishes if and only if the spin `Sigma`
vanishes, which in turn is equivalent to the simultaneous vanishing of both chiral cycles `Q_+` and `Q_-`. -/
theorem transcendent_creation_lock_iff {P : R} (hP : P * P = P) (A C : R) :
    (genV P A C = 0 ↔ genSig P A C = 0) ∧
    (genSig P A C = 0 ↔ qgtPlus P A C = 0 ∧ qgtMinus P A C = 0) := by
  have hVS : genV P A C = 0 ↔ genSig P A C = 0 := by
    have h1 : genSig P A C = invS P * genV P A C :=
      ((transcendent_quartet_algebra hP A C).2.2.2.2.2.1.1).symm
    have h2 : genV P A C = invS P * genSig P A C :=
      ((transcendent_quartet_algebra hP A C).2.2.2.2.2.2.1).symm
    constructor
    · intro hV
      rw [h1, hV, mul_zero]
    · intro hSig
      rw [h2, hSig, mul_zero]
  refine ⟨hVS, ?_⟩
  rw [← hVS]
  exact genV_eq_zero_iff_qgt_zero P A C hP

/-- Bruhat tilt unipotent conjugation, idempotent chart stability, Maurer-Cartan curvature
decomposition, and covariant Bianchi identity. -/
theorem bruhat_tilt_and_maurer_cartan_bianchi {P : R} (hP : P * P = P) (A C : R) :
    ((1 + conePlus P A) * (1 - conePlus P A) = 1 ∧
     (1 - conePlus P A) * (1 + conePlus P A) = 1) ∧
    (1 + conePlus P A) * P * (1 - conePlus P A) = P - conePlus P A ∧
    (P - conePlus P A) * (P - conePlus P A) = P - conePlus P A ∧
    (peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
     peirceCovariantDeriv P A C (genV P A C) = 0) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · unfold peirceMaurerCartanCurvature peirceGradingDeriv; peirce_nf hP
  · unfold peirceCovariantDeriv peirceGradingDeriv; peirce_nf hP

/-- Upper corner projection of `cutMat2` on upper triangular element. -/
theorem conePlus_cutMat2_A {B : Type*} [Ring B] (u : B) :
    conePlus cutMat2 (!![0, u; 0, 0] : Matrix (Fin 2) (Fin 2) B) = !![0, u; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conePlus, cutMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Lower corner projection of `cutMat2` on lower triangular element. -/
theorem coneMinus_cutMat2_C {B : Type*} [Ring B] (v : B) :
    coneMinus cutMat2 (!![0, 0; v, 0] : Matrix (Fin 2) (Fin 2) B) = !![0, 0; v, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneMinus, cutMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit matrix form of `genSig` on `cutMat2`. -/
theorem genSig_cutMat2_eq {B : Type*} [Ring B] (u v : B) :
    let A : Matrix (Fin 2) (Fin 2) B := !![0, u; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) B := !![0, 0; v, 0]
    genSig cutMat2 A C = !![u * v, 0; 0, -(v * u)] := by
  intro A C
  rw [genSig, PeirceSpine.comm, conePlus_cutMat2_A, coneMinus_cutMat2_C]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Explicit matrix form of `genV` on `cutMat2`. -/
theorem genV_cutMat2_eq {B : Type*} [Ring B] (u v : B) :
    let A : Matrix (Fin 2) (Fin 2) B := !![0, u; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) B := !![0, 0; v, 0]
    genV cutMat2 A C = !![u * v, 0; 0, v * u] := by
  intro A C
  rw [genV, anticomm, conePlus_cutMat2_A, coneMinus_cutMat2_C]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Explicit matrix form of `invS cutMat2`. -/
theorem invS_cutMat2_eq {B : Type*} [Ring B] :
    invS (cutMat2 : Matrix (Fin 2) (Fin 2) B) = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invS, cutMat2]

/-- Trace of `genSig` equals the fiber commutator `[u, v] = u * v - v * u`. -/
theorem trace_genSig_eq {B : Type*} [Ring B] (u v : B) :
    let A : Matrix (Fin 2) (Fin 2) B := !![0, u; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) B := !![0, 0; v, 0]
    Matrix.trace (genSig cutMat2 A C) = u * v - v * u := by
  intro A C
  rw [genSig_cutMat2_eq]
  simp [Matrix.trace, Fin.sum_univ_two, sub_eq_add_neg]

/-- Supertrace (trace of `invS * genSig`) equals the fiber anticommutator `{u, v} = u * v + v * u`. -/
theorem trace_invS_mul_genSig_eq {B : Type*} [Ring B] (u v : B) :
    let A : Matrix (Fin 2) (Fin 2) B := !![0, u; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) B := !![0, 0; v, 0]
    Matrix.trace (invS cutMat2 * genSig cutMat2 A C) = u * v + v * u := by
  intro A C
  rw [invS_cutMat2_eq, genSig_cutMat2_eq]
  simp [Matrix.trace, Fin.sum_univ_two]

/-- Non-commutative fiber witnesses in M2(Z). -/
def u₀ : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 0, 2]
def v₀ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]
def A₀ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) := !![0, u₀; 0, 0]
def C₀ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) := !![0, 0; v₀, 0]

/-- Explicit matrix form of `genV cutMat2 A₀ C₀`. -/
theorem genV_cutMat2_A0_C0 :
    genV cutMat2 A₀ C₀ = !![u₀ * v₀, 0; 0, v₀ * u₀] := by
  change genV cutMat2 !![0, u₀; 0, 0] !![0, 0; v₀, 0] = !![u₀ * v₀, 0; 0, v₀ * u₀]
  exact genV_cutMat2_eq u₀ v₀

theorem u₀_mul_v₀ : u₀ * v₀ = !![3, 1; 2, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u₀, v₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem v₀_mul_u₀ : v₀ * u₀ = !![2, 1; 2, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u₀, v₀, Matrix.mul_apply, Fin.sum_univ_two]

/-- Non-commutativity witness for M2(Z) fiber elements. -/
theorem u₀_v₀_noncommuting : u₀ * v₀ ≠ v₀ * u₀ := by
  intro h
  have hentry : (u₀ * v₀) 0 0 = (v₀ * u₀) 0 0 := by
    rw [h]
  rw [u₀_mul_v₀, v₀_mul_u₀] at hentry
  revert hentry
  decide

/-- Noncommutative fiber trace, supertrace, and non-vanishing witness in M2(M2(Z)). -/
theorem noncomm_fiber_trace_genSig_and_supertrace :
    (∀ {B : Type*} [Ring B] (u v : B),
      let A : Matrix (Fin 2) (Fin 2) B := !![0, u; 0, 0]
      let C : Matrix (Fin 2) (Fin 2) B := !![0, 0; v, 0]
      Matrix.trace (genSig cutMat2 A C) = u * v - v * u ∧
      Matrix.trace (invS cutMat2 * genSig cutMat2 A C) = u * v + v * u) ∧
    Matrix.trace (genSig cutMat2 A₀ C₀) ≠ 0 := by
  refine ⟨fun u v => ⟨trace_genSig_eq u v, trace_invS_mul_genSig_eq u v⟩, ?_⟩
  intro h
  have htr := trace_genSig_eq u₀ v₀
  change Matrix.trace (genSig cutMat2 A₀ C₀) = u₀ * v₀ - v₀ * u₀ at htr
  rw [h] at htr
  have hentry : (0 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (u₀ * v₀ - v₀ * u₀) 0 0 := by
    rw [htr]
  rw [u₀_mul_v₀, v₀_mul_u₀] at hentry
  revert hentry
  decide

/-! ### Section 4a: Socratic Aporia Bridge & Pinching -/

/-- The idempotency defect of a primordial cut translated by an off-diagonal connection
equals the Jordan mass `genV P A C`. -/
theorem idempotencyDefect_P_add_genPhi {P : R} (hP : P * P = P) (A C : R) :
    idempotencyDefect (P + genPhi P A C) = genV P A C := by
  unfold idempotencyDefect
  peirce_nf hP

/-- Socratic aporia bridge and pinching: relating idempotency defects across Peirce grades
and corner compressions. -/
theorem socratic_aporia_bridge_and_pinching {P : R} (hP : P * P = P)
    (A C X : R) :
    idempotencyDefect (P + genPhi P A C) = genV P A C ∧
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X ∧
    (X * X = X →
      idempotencyDefect (peirce11 P X) = -qgtPlus P X X ∧
      idempotencyDefect (peirce00 P X) = -qgtMinus P X X) := by
  refine ⟨idempotencyDefect_P_add_genPhi hP A C,
          even_idempotencyDefect_sub P X hP,
          fun hX => ⟨idempotencyDefect_peirce11_of_idempotent P X hP hX,
                     idempotencyDefect_peirce00_of_idempotent P X hP hX⟩⟩

/-! ### Section 4b: Meta-Cognitive Defect, Newton–Peirce Tower & Infinite Non-Periodic Orbit -/

variable {B : Type*} [Ring B]

/-- Left support is preserved by one Newton–Peirce correction step. -/
lemma newtonPeirceStep_left_support {p x : B} (h : p * x = x) :
    p * newtonPeirceStep x = newtonPeirceStep x := by
  dsimp [newtonPeirceStep]
  calc
    p * (3 * x * x - 2 * x * x * x) = 3 * (p * x) * x - 2 * (p * x) * x * x := by
      noncomm_ring
    _ = 3 * x * x - 2 * x * x * x := by
      rw [h]

/-- Right support is preserved by one Newton–Peirce correction step. -/
lemma newtonPeirceStep_right_support {p x : B} (h : x * p = x) :
    newtonPeirceStep x * p = newtonPeirceStep x := by
  dsimp [newtonPeirceStep]
  calc
    (3 * x * x - 2 * x * x * x) * p = 3 * x * (x * p) - 2 * x * x * (x * p) := by
      noncomm_ring
    _ = 3 * x * x - 2 * x * x * x := by
      rw [h]

/-- Left support is preserved across all finite Newton–Peirce iterates. -/
lemma newtonPeirceStep_iterates_left_support {p x : B} (h : p * x = x) (n : ℕ) :
    p * newtonPeirceStep^[n] x = newtonPeirceStep^[n] x := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact newtonPeirceStep_left_support ih

/-- Right support is preserved across all finite Newton–Peirce iterates. -/
lemma newtonPeirceStep_iterates_right_support {p x : B} (h : x * p = x) (n : ℕ) :
    newtonPeirceStep^[n] x * p = newtonPeirceStep^[n] x := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact newtonPeirceStep_right_support ih

/-- Upper Peirce cycle retains left support under all Newton–Peirce iterates. -/
lemma qgtPlus_newton_left {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    P * newtonPeirceStep^[n] (qgtPlus P A C) = newtonPeirceStep^[n] (qgtPlus P A C) := by
  apply newtonPeirceStep_iterates_left_support
  simp only [qgtPlus]
  peirce_nf hP

/-- Upper Peirce cycle retains right support under all Newton–Peirce iterates. -/
lemma qgtPlus_newton_right {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    newtonPeirceStep^[n] (qgtPlus P A C) * P = newtonPeirceStep^[n] (qgtPlus P A C) := by
  apply newtonPeirceStep_iterates_right_support
  simp only [qgtPlus]
  peirce_nf hP

/-- Lower Peirce cycle retains complementary left support under all Newton–Peirce iterates. -/
lemma qgtMinus_newton_left {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    (1 - P) * newtonPeirceStep^[n] (qgtMinus P A C) = newtonPeirceStep^[n] (qgtMinus P A C) := by
  apply newtonPeirceStep_iterates_left_support
  simp only [qgtMinus]
  peirce_nf hP

/-- Lower Peirce cycle retains complementary right support under all Newton–Peirce iterates. -/
lemma qgtMinus_newton_right {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    newtonPeirceStep^[n] (qgtMinus P A C) * (1 - P) = newtonPeirceStep^[n] (qgtMinus P A C) := by
  apply newtonPeirceStep_iterates_right_support
  simp only [qgtMinus]
  peirce_nf hP

/-- The two Newton–Peirce iterated cycles remain mutually orthogonal at all depths. -/
lemma qgt_newton_orthogonal {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    newtonPeirceStep^[n] (qgtPlus P A C) * newtonPeirceStep^[n] (qgtMinus P A C) = 0 ∧
    newtonPeirceStep^[n] (qgtMinus P A C) * newtonPeirceStep^[n] (qgtPlus P A C) = 0 := by
  constructor
  · have h1 := qgtPlus_newton_right hP A C n
    have h2 := qgtMinus_newton_left hP A C n
    calc
      newtonPeirceStep^[n] (qgtPlus P A C) * newtonPeirceStep^[n] (qgtMinus P A C) =
          (newtonPeirceStep^[n] (qgtPlus P A C) * P) * ((1 - P) * newtonPeirceStep^[n] (qgtMinus P A C)) := by rw [h1, h2]
      _ = newtonPeirceStep^[n] (qgtPlus P A C) * (P * (1 - P)) * newtonPeirceStep^[n] (qgtMinus P A C) := by
        noncomm_ring
      _ = 0 := by
        have hpq : P * (1 - P) = 0 := by
          noncomm_ring [hP]
        rw [hpq, mul_zero, zero_mul]
  · have h1 := qgtMinus_newton_right hP A C n
    have h2 := qgtPlus_newton_left hP A C n
    calc
      newtonPeirceStep^[n] (qgtMinus P A C) * newtonPeirceStep^[n] (qgtPlus P A C) =
          (newtonPeirceStep^[n] (qgtMinus P A C) * (1 - P)) * (P * newtonPeirceStep^[n] (qgtPlus P A C)) := by rw [h1, h2]
      _ = newtonPeirceStep^[n] (qgtMinus P A C) * ((1 - P) * P) * newtonPeirceStep^[n] (qgtPlus P A C) := by
        noncomm_ring
      _ = 0 := by
        have hqp : (1 - P) * P = 0 := by
          noncomm_ring [hP]
        rw [hqp, mul_zero, zero_mul]

/-- The Newton–Peirce iteration splits additively across the two orthogonal Peirce cycles. -/
lemma newtonPeirceStep_iterates_genV {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    newtonPeirceStep^[n] (genV P A C) =
      newtonPeirceStep^[n] (qgtPlus P A C) + newtonPeirceStep^[n] (qgtMinus P A C) := by
  induction n with
  | zero =>
    change genV P A C = qgtPlus P A C + qgtMinus P A C
    simp only [genV, anticomm, qgtPlus, qgtMinus]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact newtonPeirceStep_add_of_orthogonal
      (qgt_newton_orthogonal hP A C n).1
      (qgt_newton_orthogonal hP A C n).2

/-- **Meta-Cognitive Defect & Newton–Peirce Tower Theorem**:
Unites the shift of finite defect iterates under off-diagonal perturbations,
orthogonal cycle splitting, orbit commutativity, polynomial factorization,
and Newton–Peirce cycle preservation. -/
theorem meta_cognitive_defect_and_newton_tower {P : B} (hP : P * P = P)
    (A C X : B) (n m : ℕ) :
    idempotencyDefect^[n + 1] (P + genPhi P A C) = idempotencyDefect^[n] (genV P A C) ∧
    (idempotencyDefect^[n] (genV P A C) =
        idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C) ∧
      P * idempotencyDefect^[n] (genV P A C) = idempotencyDefect^[n] (qgtPlus P A C) ∧
      idempotencyDefect^[n] (genV P A C) * P = idempotencyDefect^[n] (qgtPlus P A C) ∧
      (1 - P) * idempotencyDefect^[n] (genV P A C) = idempotencyDefect^[n] (qgtMinus P A C) ∧
      idempotencyDefect^[n] (genV P A C) * (1 - P) = idempotencyDefect^[n] (qgtMinus P A C)) ∧
    idempotencyDefect^[n] X * idempotencyDefect^[m] X =
      idempotencyDefect^[m] X * idempotencyDefect^[n] X ∧
    idempotencyDefect (newtonPeirceStep X) =
      idempotencyDefect X * idempotencyDefect X * (4 * idempotencyDefect X - 3) ∧
    newtonPeirceStep^[n] (genV P A C) =
      newtonPeirceStep^[n] (qgtPlus P A C) + newtonPeirceStep^[n] (qgtMinus P A C) := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Function.iterate_succ_apply, idempotencyDefect_P_add_genPhi hP]
  · exact genV_defect_iterates_cycle_split hP A C n
  · exact genV_defect_iterates_left_projection hP A C n
  · exact genV_defect_iterates_right_projection hP A C n
  · exact genV_defect_iterates_complement_left hP A C n
  · exact genV_defect_iterates_complement_right hP A C n
  · exact idempotencyDefect_iterates_commute X n m
  · exact idempotencyDefect_newtonPeirceStep X
  · exact newtonPeirceStep_iterates_genV hP A C n

/-- Socratic aporia eigenvalue sequence under the defect map `x ↦ x² - x`. -/
def aporiaEigenSeq : ℕ → ℤ
  | 0 => 4
  | n + 1 => aporiaEigenSeq n ^ 2 - aporiaEigenSeq n

theorem aporiaEigenSeq_ge_four (n : ℕ) : 4 ≤ aporiaEigenSeq n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [aporiaEigenSeq]
    have h1 : aporiaEigenSeq n ^ 2 - aporiaEigenSeq n = aporiaEigenSeq n * (aporiaEigenSeq n - 1) := by
      ring
    rw [h1]
    have h2 : 3 ≤ aporiaEigenSeq n - 1 := by
      linarith
    nlinarith

theorem aporiaEigenSeq_lt_succ (n : ℕ) : aporiaEigenSeq n < aporiaEigenSeq (n + 1) := by
  rw [aporiaEigenSeq]
  have h4 := aporiaEigenSeq_ge_four n
  have h1 : aporiaEigenSeq n ^ 2 - aporiaEigenSeq n - aporiaEigenSeq n = aporiaEigenSeq n * (aporiaEigenSeq n - 2) := by
    ring
  have h2 : 2 ≤ aporiaEigenSeq n - 2 := by
    linarith
  have hpos : 0 < aporiaEigenSeq n * (aporiaEigenSeq n - 2) := by
    nlinarith
  linarith

theorem aporiaEigenSeq_strictMono : StrictMono aporiaEigenSeq :=
  strictMono_nat_of_lt_succ aporiaEigenSeq_lt_succ

lemma u0_mul_v0_mulVec : (u₀ * v₀).mulVec ![1, 1] = (4 : ℤ) • ![1, 1] := by
  ext i
  fin_cases i <;> decide

theorem idempotencyDefect_mulVec_eigen (M : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ)
    (hM : M.mulVec ![1, 1] = c • ![1, 1]) :
    (idempotencyDefect M).mulVec ![1, 1] = (c ^ 2 - c) • ![1, 1] := by
  dsimp [idempotencyDefect]
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, hM, smul_smul]
  ext i
  fin_cases i
  · simp
    ring
  · simp
    ring

theorem aporia_eigen_iterates (n : ℕ) :
    (idempotencyDefect^[n] (u₀ * v₀)).mulVec ![1, 1] = aporiaEigenSeq n • ![1, 1] := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, aporiaEigenSeq, u0_mul_v0_mulVec]
  | succ n ih =>
    rw [Function.iterate_succ_apply', aporiaEigenSeq]
    exact idempotencyDefect_mulVec_eigen (idempotencyDefect^[n] (u₀ * v₀)) (aporiaEigenSeq n) ih

lemma idempotencyDefect_diag2 {B : Type*} [Ring B] (X Y : B) :
    idempotencyDefect (!![X, 0; 0, Y] : Matrix (Fin 2) (Fin 2) B) =
      !![idempotencyDefect X, 0; 0, idempotencyDefect Y] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [idempotencyDefect]

lemma idempotencyDefect_iterates_diag2 {B : Type*} [Ring B] (X Y : B) (n : ℕ) :
    idempotencyDefect^[n] (!![X, 0; 0, Y] : Matrix (Fin 2) (Fin 2) B) =
      !![idempotencyDefect^[n] X, 0; 0, idempotencyDefect^[n] Y] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, idempotencyDefect_diag2]
    rw [Function.iterate_succ_apply' idempotencyDefect n X]
    rw [Function.iterate_succ_apply' idempotencyDefect n Y]

lemma genV_iterates_00 (n : ℕ) :
    (idempotencyDefect^[n] (genV cutMat2 A₀ C₀)) 0 0 =
      idempotencyDefect^[n] (u₀ * v₀) := by
  rw [genV_cutMat2_A0_C0, idempotencyDefect_iterates_diag2]
  rfl

/-- **Infinite Non-Periodic Socratic Aporia Orbit Theorem**:
In `M₂(M₂(ℤ))`, the iterated idempotency defect orbit of `genV cutMat2 A₀ C₀`
is strictly non-vanishing and non-periodic for all `m ≠ n`. -/
theorem infinite_nonperiodic_aporia_orbit_nestedMatZ :
    (∀ n, 4 ≤ aporiaEigenSeq n) ∧
    StrictMono aporiaEigenSeq ∧
    (∀ n, (idempotencyDefect^[n] (u₀ * v₀)).mulVec ![1, 1] = aporiaEigenSeq n • ![1, 1]) ∧
    (∀ (m n : ℕ),
      idempotencyDefect^[n] (genV cutMat2 A₀ C₀) ≠ 0 ∧
      (m ≠ n → idempotencyDefect^[m] (genV cutMat2 A₀ C₀) ≠ idempotencyDefect^[n] (genV cutMat2 A₀ C₀))) := by
  refine ⟨aporiaEigenSeq_ge_four, aporiaEigenSeq_strictMono, aporia_eigen_iterates, ?_⟩
  intro m n
  constructor
  · intro h0
    have h00 : (idempotencyDefect^[n] (genV cutMat2 A₀ C₀)) 0 0 = 0 := by
      rw [h0]
      rfl
    rw [genV_iterates_00] at h00
    have hvec : (idempotencyDefect^[n] (u₀ * v₀)).mulVec ![1, 1] = 0 := by
      rw [h00, Matrix.zero_mulVec]
    rw [aporia_eigen_iterates] at hvec
    have hval : aporiaEigenSeq n = 0 := by
      have he := congrFun hvec 0
      simpa using he
    have hge := aporiaEigenSeq_ge_four n
    omega
  · intro hmn heq
    have h00 : (idempotencyDefect^[m] (genV cutMat2 A₀ C₀)) 0 0 =
        (idempotencyDefect^[n] (genV cutMat2 A₀ C₀)) 0 0 := by
      rw [heq]
    rw [genV_iterates_00, genV_iterates_00] at h00
    have hvec : (idempotencyDefect^[m] (u₀ * v₀)).mulVec ![1, 1] =
        (idempotencyDefect^[n] (u₀ * v₀)).mulVec ![1, 1] := by
      rw [h00]
    rw [aporia_eigen_iterates, aporia_eigen_iterates] at hvec
    have heigen : aporiaEigenSeq m = aporiaEigenSeq n := by
      have he := congrFun hvec 0
      simpa using he
    have hinj := aporiaEigenSeq_strictMono.injective heigen
    exact hmn hinj

open CategoryTheory CategoryTheory.Limits

universe u

lemma ringHom_preserves_newtonPeirceStep {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x : R) :
    f (newtonPeirceStep x) = newtonPeirceStep (f x) := by
  dsimp [newtonPeirceStep]
  simp only [map_sub, map_mul, map_ofNat]

lemma ringHom_preserves_newtonPeirceStep_iterates {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (x : R) (k : ℕ) :
    f (newtonPeirceStep^[k] x) = newtonPeirceStep^[k] (f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ringHom_preserves_newtonPeirceStep, ih]

lemma ringHom_preserves_genPhi {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (P A C : R) :
    f (genPhi P A C) = genPhi (f P) (f A) (f C) := by
  dsimp [genPhi, conePlus, coneMinus]
  simp only [map_add, map_sub, map_mul, map_one]

lemma ringHom_preserves_genV {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (P A C : R) :
    f (genV P A C) = genV (f P) (f A) (f C) := by
  dsimp [genV, anticomm, conePlus, coneMinus]
  simp only [map_add, map_sub, map_mul, map_one]

/-- Pure algebraic `RingHom` transport of the Socratic aporia orbit and Newton–Peirce tower
across `clTowerHom B h` and into the colimit cocone `ClTowerColimit B`. -/
theorem clTower_and_colimit_aporia_transport_hom {B : Type u} [Ring B]
    {m n : ℕ} (h : m ≤ n) (P A C : ClTower B m) (k : ℕ) :
    clTowerHom B h (idempotencyDefect^[k] (P + genPhi P A C)) =
      idempotencyDefect^[k] (clTowerHom B h P + genPhi (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) ∧
    clTowerHom B h (idempotencyDefect^[k] (genV P A C)) =
      idempotencyDefect^[k] (genV (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) ∧
    clTowerHom B h (newtonPeirceStep^[k] (genV P A C)) =
      newtonPeirceStep^[k] (genV (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) ∧
    (colimit.ι (clTowerFunctor B) n).hom
        (clTowerHom B h (idempotencyDefect^[k] (genV P A C))) =
      (colimit.ι (clTowerFunctor B) m).hom (idempotencyDefect^[k] (genV P A C)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_idempotencyDefect_iterates, map_add, ringHom_preserves_genPhi]
  · rw [map_idempotencyDefect_iterates, ringHom_preserves_genV]
  · rw [ringHom_preserves_newtonPeirceStep_iterates, ringHom_preserves_genV]
  · exact clTowerColimit_ι_comp h (idempotencyDefect^[k] (genV P A C))

/-- **ClTower & Colimit Aporia Transport Theorem (with Krein Positivity)**:
Transports the Socratic defect orbit, perturbed generator, and Newton–Peirce iterates
across Clifford tower scales `m ≤ n` and into `ClTowerColimit B`, simultaneously
with StarOrderedRing Krein positivity on the `+1`-sector `peirce11`. -/
theorem clTower_and_colimit_aporia_transport
    {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    {m n : ℕ} (h : m ≤ n) (P A C : ClTower B m) (k : ℕ)
    {γ₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (hP_sq : P * P = P) (hP_star : star P = P)
    (hP_pos : kroneckerGamma γ₀ m * P = P) :
    clTowerHom B h (idempotencyDefect^[k] (P + genPhi P A C)) =
      idempotencyDefect^[k] (clTowerHom B h P + genPhi (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) ∧
    clTowerHom B h (idempotencyDefect^[k] (genV P A C)) =
      idempotencyDefect^[k] (genV (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) ∧
    clTowerHom B h (newtonPeirceStep^[k] (genV P A C)) =
      newtonPeirceStep^[k] (genV (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) ∧
    (colimit.ι (clTowerFunctor B) n).hom
        (clTowerHom B h (idempotencyDefect^[k] (genV P A C))) =
      (colimit.ι (clTowerFunctor B) m).hom (idempotencyDefect^[k] (genV P A C)) ∧
    kreinAdjoint γ₀ m (peirce11 P (idempotencyDefect^[k] (genV P A C))) =
      star (peirce11 P (idempotencyDefect^[k] (genV P A C))) ∧
    (0 : B) ≤ towerTrace (kreinAdjoint γ₀ m
      (peirce11 P (idempotencyDefect^[k] (genV P A C))) *
        peirce11 P (idempotencyDefect^[k] (genV P A C))) := by
  have htrans := clTower_and_colimit_aporia_transport_hom h P A C k
  have hpos := peirce11_positive_sector_krein_positivity_and_bianchi hγ₀_star m P
    (idempotencyDefect^[k] (genV P A C)) A C hP_sq hP_star hP_pos
  exact ⟨htrans.1, htrans.2.1, htrans.2.2.1, htrans.2.2.2, hpos.1, hpos.2.1⟩

/-! ### Section 5: Bounded Acyclic Causal Poset `SolveEtCoagulaNode` & Master Synthesis -/

/-- Five stages of the Noncommutative Solve et Coagula Epistemic Compilation. -/
inductive SolveEtCoagulaNode where
  | EC1_BinaryCut
  | EC2_PeirceAnatomy
  | EC3_TranscendentQuartet
  | EC4_AporiaDefectTower
  | EC5_MasterCoagulation
  deriving DecidableEq, Repr, Inhabited

/-- Strict rank grading function `SolveEtCoagulaNode → ℕ`. -/
def ecRank : SolveEtCoagulaNode → ℕ
  | .EC1_BinaryCut => 0
  | .EC2_PeirceAnatomy => 1
  | .EC3_TranscendentQuartet => 2
  | .EC4_AporiaDefectTower => 3
  | .EC5_MasterCoagulation => 4

/-- The 5 covering edges of the causal compilation DAG:
EC1 → EC2, EC2 → EC3, EC2 → EC4, EC3 → EC4, EC4 → EC5. -/
inductive Covers : SolveEtCoagulaNode → SolveEtCoagulaNode → Prop where
  | cov_1_2 : Covers .EC1_BinaryCut .EC2_PeirceAnatomy
  | cov_2_3 : Covers .EC2_PeirceAnatomy .EC3_TranscendentQuartet
  | cov_2_4 : Covers .EC2_PeirceAnatomy .EC4_AporiaDefectTower
  | cov_3_4 : Covers .EC3_TranscendentQuartet .EC4_AporiaDefectTower
  | cov_4_5 : Covers .EC4_AporiaDefectTower .EC5_MasterCoagulation

theorem ecRank_strictMono {a b : SolveEtCoagulaNode} (h : Covers a b) :
    ecRank a < ecRank b := by
  cases h <;> decide

lemma ecRank_injective : Function.Injective ecRank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : PartialOrder SolveEtCoagulaNode :=
  PartialOrder.lift ecRank ecRank_injective

theorem covers_transGen_ecRank_strictMono {a b : SolveEtCoagulaNode}
    (h : Relation.TransGen Covers a b) : ecRank a < ecRank b := by
  induction h with
  | single hab => exact ecRank_strictMono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (ecRank_strictMono hbc)

/-- Causal reachability is strictly irreflexive. -/
theorem covers_irreflexive (a : SolveEtCoagulaNode) :
    ¬ Relation.TransGen Covers a a := by
  intro h
  have hlt := covers_transGen_ecRank_strictMono h
  exact Nat.lt_irrefl (ecRank a) hlt

/-- The Solve et Coagula compilation graph is acyclic. -/
theorem covers_acyclic {a b : SolveEtCoagulaNode}
    (h1 : Relation.TransGen Covers a b) (h2 : Relation.TransGen Covers b a) : False := by
  have hlt1 := covers_transGen_ecRank_strictMono h1
  have hlt2 := covers_transGen_ecRank_strictMono h2
  exact Nat.lt_irrefl (ecRank a) (Nat.lt_trans hlt1 hlt2)

/-- Verification that all 5 required covering edges exist in `Covers`. -/
theorem covering_edges :
    Covers .EC1_BinaryCut .EC2_PeirceAnatomy ∧
    Covers .EC2_PeirceAnatomy .EC3_TranscendentQuartet ∧
    Covers .EC2_PeirceAnatomy .EC4_AporiaDefectTower ∧
    Covers .EC3_TranscendentQuartet .EC4_AporiaDefectTower ∧
    Covers .EC4_AporiaDefectTower .EC5_MasterCoagulation :=
  ⟨Covers.cov_1_2, Covers.cov_2_3, Covers.cov_2_4, Covers.cov_3_4, Covers.cov_4_5⟩

/-- **Master Noncommutative Solve et Coagula Synthesis Theorem**:
Unites the 5 foundational stages:
1. $\mathcal{E}\mathcal{C}_1$: Primordial binary cut idempotent complementation and involution.
2. $\mathcal{E}\mathcal{C}_2$: Fourfold Peirce decomposition and quiver multiplication.
3. $\mathcal{E}\mathcal{C}_3$: Transcendent quartet algebra and universal creation lock.
4. $\mathcal{E}\mathcal{C}_4$: Socratic aporia boundary jump, finite defect orbit splitting, and Newton–Peirce tower.
5. $\mathcal{E}\mathcal{C}_5$: Bounded acyclic causal poset, rank grading, and irreflexivity. -/
theorem master_solve_et_coagula_noncommutative_synthesis
    {B : Type*} [Ring B] {P : B} (hP : P * P = P)
    (A C X Y : B) (n : ℕ) :
    ((1 - P) * (1 - P) = 1 - P ∧ invS P * invS P = 1) ∧
    (X = peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X ∧
      peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y) ∧
    (genPhi P A C * genPhi P A C = genV P A C ∧
      genJ P A C * genJ P A C = -genV P A C ∧
      (genV P A C = 0 ↔ genSig P A C = 0)) ∧
    (idempotencyDefect (P + genPhi P A C) = genV P A C ∧
      idempotencyDefect^[n] (genV P A C) =
        idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C) ∧
      newtonPeirceStep^[n] (genV P A C) =
        newtonPeirceStep^[n] (qgtPlus P A C) + newtonPeirceStep^[n] (qgtMinus P A C)) ∧
    (Covers .EC1_BinaryCut .EC2_PeirceAnatomy ∧
      Covers .EC4_AporiaDefectTower .EC5_MasterCoagulation ∧
      (∀ a : SolveEtCoagulaNode, ¬ Relation.TransGen Covers a a)) := by
  refine ⟨⟨(binary_cut_idempotent_and_grading_laws P hP).1,
            (binary_cut_idempotent_and_grading_laws P hP).2.2.2.1⟩,
          ⟨peirce_fourfold_decomp P X hP,
            (peirce_fourfold_mul_table P hP X Y).1⟩,
          ⟨(transcendent_quartet_algebra hP A C).2.1,
            (transcendent_quartet_algebra hP A C).2.2.1,
            (transcendent_creation_lock_iff hP A C).1⟩,
          ⟨idempotencyDefect_P_add_genPhi hP A C,
            (meta_cognitive_defect_and_newton_tower hP A C X n 0).2.1.1,
            (meta_cognitive_defect_and_newton_tower hP A C X n 0).2.2.2.2⟩,
          ⟨covering_edges.1,
            covering_edges.2.2.2.2,
            covers_irreflexive⟩⟩

open InfoGeometry.MetaCompiler

/-- Epistemic compiler certified archetype registration for Milestone 6E. -/
def solveEtCoagulaPeirceAporiaArchetype : TypedArchetype Unit .proved where
  name := `solveEtCoagulaPeirceAporiaArchetype
  phase := 5
  claim := fun _ =>
    ∀ {B : Type*} [Ring B] {P : B} (_hP : P * P = P)
      (A C X Y : B) (n : ℕ),
      ((1 - P) * (1 - P) = 1 - P ∧ invS P * invS P = 1) ∧
      (X = peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X ∧
        peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y) ∧
      (genPhi P A C * genPhi P A C = genV P A C ∧
        genJ P A C * genJ P A C = -genV P A C ∧
        (genV P A C = 0 ↔ genSig P A C = 0)) ∧
      (idempotencyDefect (P + genPhi P A C) = genV P A C ∧
        idempotencyDefect^[n] (genV P A C) =
          idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C) ∧
        newtonPeirceStep^[n] (genV P A C) =
          newtonPeirceStep^[n] (qgtPlus P A C) + newtonPeirceStep^[n] (qgtMinus P A C)) ∧
      (Covers .EC1_BinaryCut .EC2_PeirceAnatomy ∧
        Covers .EC4_AporiaDefectTower .EC5_MasterCoagulation ∧
        (∀ a : SolveEtCoagulaNode, ¬ Relation.TransGen Covers a a))
  evidence := fun _ =>
    master_solve_et_coagula_noncommutative_synthesis

end InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset
