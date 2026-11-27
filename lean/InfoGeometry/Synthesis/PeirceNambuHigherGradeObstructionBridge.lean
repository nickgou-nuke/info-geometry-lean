/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.DeWittPeirceSuperalgebra
import InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Peirce–Nambu Higher-Grade Noncommutativity Obstruction Bridge

This module lifts the grade `0 → 1 → 2` Peirce–DeWitt noncommutativity
obstruction tower in `DeWittPeirceSuperalgebra` to **grade 3** using the
totally antisymmetric Nambu–Lie 3-commutator `nambu3` and the Jacobi identity
from `SochichiuNambu3AlgebraObstruction`.

## Main Results
1. **Abstract Grade `0 → 1 → 2 → 3` Tower (`section AbstractGradeTower`)**:
   - `comm_eq_lieComm` and `jacobi_identity_peirce_comm`.
   - `odd_comm_is_even`: the commutator `[U, V]` of two `G`-odd elements is `G`-even.
   - `nambu3_three_odd_anticomm_G`: `nambu3 U V W` of three `G`-odd elements stays `G`-odd.
   - `nambu3_PL_of_body`: when `X, Y` lie in `body`, `nambu3 S.PL X Y = S.PL * lieComm X Y`.
   - `nambu3_G_odd_pair_eq_three_G_mul_comm` and `nambu3_G_two_halmos_obstructions`:
     pairing the chiral grading `G` with two `G`-odd Halmos obstructions `[P_L, P_1]`,
     `[P_L, P_2]` produces `(3 : A) * (G * [[P_L, P_1], [P_L, P_2]])`, which is `G`-even.
2. **Sharp Dimensional Emergence (`M₂(ℤ)` vs `M₄(ℤ)`)**:
   - In `M₂(ℤ)`, grade-1 (`[P_L, X]`) and grade-2 (`[U, V]`, `nambu3 G U V`)
     obstructions are already nonvanishing (`mat2_grade1_grade2_nonvanishing`), while any
     three anti-diagonal odd matrices satisfy `nambu3 U V W = 0` identically
     (`mat2_pure_odd_nambu3_vanishes`).
   - In `M₄(ℤ)` (with `2 ⊕ 2` chiral Peirce split), odd transition corners have
     dimension `8 > 2`, and the pure odd Nambu 3-commutator genuinely emerges
     nonvanishing (`mat4_odd_nambu3_trivector_emerges` with `nambu3 U V W = E₀₃ ≠ 0`).
-/

namespace InfoGeometry.Synthesis.PeirceNambuHigherGradeObstructionBridge

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra
open InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction

/-! ## Section 1: Concrete Noncommutativity Witnesses (`M₂(ℤ)` and `M₄(ℤ)`) -/

/-- Left Peirce idempotent `diag(1, 0)` on `M₂(ℤ)`. -/
def mat2PL : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Right Peirce idempotent `diag(0, 1)` on `M₂(ℤ)`. -/
def mat2PR : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 0, 1]

/-- Chiral grading `G = diag(1, -1)` on `M₂(ℤ)`. -/
def mat2G : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- Odd transition basis element `E₀₁` on `M₂(ℤ)`. -/
def mat2E01 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Odd transition basis element `E₁₀` on `M₂(ℤ)`. -/
def mat2E10 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

private theorem mat2PL_sq : mat2PL * mat2PL = mat2PL := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem mat2PR_sq : mat2PR * mat2PR = mat2PR := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem mat2_sum : mat2PL + mat2PR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem mat2_ortho : mat2PL * mat2PR = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Constructive `ChiralPeirceSystem` on `M₂(ℤ)`. -/
@[instance_reducible]
def mat2ChiralPeirceSystem : ChiralPeirceSystem (Matrix (Fin 2) (Fin 2) ℤ) where
  PL := mat2PL
  PR := mat2PR
  h_PL_sq := mat2PL_sq
  h_PR_sq := mat2PR_sq
  h_sum := mat2_sum
  h_PL_PR := mat2_ortho

/-- Closed noncommutativity witness on `M₂(ℤ)` (T16 carrier discipline). -/
theorem mat2_int_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A := by
  refine ⟨mat2PL, mat2E01, ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  revert h01
  decide

/-- Left block Peirce idempotent `diag(1, 1, 0, 0)` on `M₄(ℤ)`. -/
def mat4PL : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Right block Peirce idempotent `diag(0, 0, 1, 1)` on `M₄(ℤ)`. -/
def mat4PR : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- First odd transition block element `E₀₂` on `M₄(ℤ)`. -/
def mat4U : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Second odd transition block element `E₂₁` on `M₄(ℤ)`. -/
def mat4V : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0]

/-- Third odd transition block element `E₁₃` on `M₄(ℤ)`. -/
def mat4W : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Emergent grade-3 odd corner element `E₀₃` on `M₄(ℤ)`. -/
def mat4E03 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

private theorem mat4PL_sq : mat4PL * mat4PL = mat4PL := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem mat4PR_sq : mat4PR * mat4PR = mat4PR := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem mat4_sum : mat4PL + mat4PR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem mat4_ortho : mat4PL * mat4PR = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Constructive `ChiralPeirceSystem` on `M₄(ℤ)`. -/
@[instance_reducible]
def mat4ChiralPeirceSystem : ChiralPeirceSystem (Matrix (Fin 4) (Fin 4) ℤ) where
  PL := mat4PL
  PR := mat4PR
  h_PL_sq := mat4PL_sq
  h_PR_sq := mat4PR_sq
  h_sum := mat4_sum
  h_PL_PR := mat4_ortho

/-- Closed noncommutativity witness on `M₄(ℤ)` (T16 carrier discipline). -/
theorem mat4_int_noncommutative :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℤ, A * B ≠ B * A := by
  refine ⟨mat4PL, mat4U, ?_⟩
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 0 2) h
  revert h02
  decide

/-! ## Section 2: Abstract Grade `0 → 1 → 2 → 3` Noncommutativity Tower -/

section AbstractGradeTower

section PureRingComm

variable {A : Type*} [Ring A]

/-- Peirce `comm` agrees definitionally with `lieComm`. -/
theorem comm_eq_lieComm (x y : A) :
    Algebra.DeWittPeirceSuperalgebra.comm x y = lieComm x y := rfl

/-- The Jacobi identity for the Peirce commutator `comm` holds in every associative ring. -/
theorem jacobi_identity_peirce_comm (x y z : A) :
    Algebra.DeWittPeirceSuperalgebra.comm x (Algebra.DeWittPeirceSuperalgebra.comm y z) +
      Algebra.DeWittPeirceSuperalgebra.comm y (Algebra.DeWittPeirceSuperalgebra.comm z x) +
      Algebra.DeWittPeirceSuperalgebra.comm z (Algebra.DeWittPeirceSuperalgebra.comm x y) = 0 := by
  dsimp [Algebra.DeWittPeirceSuperalgebra.comm]
  noncomm_ring

end PureRingComm

variable {A : Type*} [Ring A] [S : ChiralPeirceSystem A]

private lemma chiral_G_sq : G (A := A) * G (A := A) = 1 := by
  dsimp [G]
  have h_ortho := PR_PL_ortho (A := A)
  calc
    (S.PL - S.PR) * (S.PL - S.PR)
        = S.PL * S.PL - S.PL * S.PR - (S.PR * S.PL - S.PR * S.PR) := by noncomm_ring
    _ = S.PL - 0 - (0 - S.PR) := by
        rw [S.h_PL_sq, S.h_PL_PR, h_ortho, S.h_PR_sq]
    _ = S.PL + S.PR := by abel
    _ = 1 := S.h_sum

/-- Grade `1 + 1 → 2`: the commutator `[U, V]` of two `G`-odd operators commutes with `G`. -/
theorem odd_comm_is_even (U V : A)
    (hU : G (A := A) * U = -(U * G (A := A)))
    (hV : G (A := A) * V = -(V * G (A := A))) :
    G (A := A) * lieComm U V = lieComm U V * G (A := A) := by
  have hUG : U * G (A := A) = -(G (A := A) * U) := by
    calc
      U * G (A := A) = -(-(U * G (A := A))) := (neg_neg _).symm
      _ = -(G (A := A) * U) := by rw [← hU]
  have hVG : V * G (A := A) = -(G (A := A) * V) := by
    calc
      V * G (A := A) = -(-(V * G (A := A))) := (neg_neg _).symm
      _ = -(G (A := A) * V) := by rw [← hV]
  dsimp [lieComm]
  calc
    G (A := A) * (U * V - V * U)
        = (G (A := A) * U) * V - (G (A := A) * V) * U := by noncomm_ring
    _ = (-(U * G (A := A))) * V - (-(V * G (A := A))) * U := by rw [hU, hV]
    _ = -U * (G (A := A) * V) + V * (G (A := A) * U) := by noncomm_ring
    _ = -U * (-(V * G (A := A))) + V * (-(U * G (A := A))) := by rw [hV, hU]
    _ = (U * V - V * U) * G (A := A) := by noncomm_ring
    _ = (U * V - V * U) * G (A := A) := rfl

private lemma odd_mul_even_anticomm (X E : A)
    (hX : G (A := A) * X = -(X * G (A := A)))
    (hE : G (A := A) * E = E * G (A := A)) :
    G (A := A) * (X * E) = -((X * E) * G (A := A)) := by
  calc
    G (A := A) * (X * E) = (G (A := A) * X) * E := by rw [mul_assoc]
    _ = (-(X * G (A := A))) * E := by rw [hX]
    _ = -(X * (G (A := A) * E)) := by noncomm_ring
    _ = -(X * (E * G (A := A))) := by rw [hE]
    _ = -((X * E) * G (A := A)) := by rw [mul_assoc]

/-- Grade `1 + 1 + 1 → 3`: the Nambu 3-commutator of three `G`-odd operators remains `G`-odd. -/
theorem nambu3_three_odd_anticomm_G (U V W : A)
    (hU : G (A := A) * U = -(U * G (A := A)))
    (hV : G (A := A) * V = -(V * G (A := A)))
    (hW : G (A := A) * W = -(W * G (A := A))) :
    G (A := A) * nambu3 U V W = -(nambu3 U V W * G (A := A)) := by
  rw [nambu3_eq_sum_comm]
  have h1 : G (A := A) * (U * lieComm V W) = -((U * lieComm V W) * G (A := A)) :=
    odd_mul_even_anticomm U (lieComm V W) hU (odd_comm_is_even V W hV hW)
  have h2 : G (A := A) * (V * lieComm W U) = -((V * lieComm W U) * G (A := A)) :=
    odd_mul_even_anticomm V (lieComm W U) hV (odd_comm_is_even W U hW hU)
  have h3 : G (A := A) * (W * lieComm U V) = -((W * lieComm U V) * G (A := A)) :=
    odd_mul_even_anticomm W (lieComm U V) hW (odd_comm_is_even U V hU hV)
  calc
    G (A := A) * (U * lieComm V W + V * lieComm W U + W * lieComm U V)
        = G (A := A) * (U * lieComm V W) + G (A := A) * (V * lieComm W U) +
            G (A := A) * (W * lieComm U V) := by noncomm_ring
    _ = -((U * lieComm V W) * G (A := A)) + -((V * lieComm W U) * G (A := A)) +
            -((W * lieComm U V) * G (A := A)) := by rw [h1, h2, h3]
    _ = -((U * lieComm V W + V * lieComm W U + W * lieComm U V) * G (A := A)) := by
        noncomm_ring

/-- When two operators lie strictly in the Peirce `body`, the Nambu 3-commutator
with `P_L` collapses to `P_L * [X, Y]`. -/
theorem nambu3_PL_of_body (X Y : A)
    (hX : X = body X) (hY : Y = body Y) :
    nambu3 S.PL X Y = S.PL * lieComm X Y := by
  have hcommX : comm S.PL X = 0 := (comm_PL_eq_zero_iff_eq_body X).mpr hX
  have hcommY : comm S.PL Y = 0 := (comm_PL_eq_zero_iff_eq_body Y).mpr hY
  have hPLX : S.PL * X = X * S.PL := sub_eq_zero.mp hcommX
  have hPLY : S.PL * Y = Y * S.PL := sub_eq_zero.mp hcommY
  exact nambu3_of_comm_left S.PL X Y hPLX hPLY

/-- Pairing chiral grading `G` with two `G`-odd operators yields `3 * (G * [U, V])`. -/
theorem nambu3_G_odd_pair_eq_three_G_mul_comm (U V : A)
    (hU : G (A := A) * U = -(U * G (A := A)))
    (hV : G (A := A) * V = -(V * G (A := A))) :
    nambu3 (G (A := A)) U V = (3 : A) * (G (A := A) * lieComm U V) := by
  have hUG : U * G (A := A) = -(G (A := A) * U) := by
    calc
      U * G (A := A) = -(-(U * G (A := A))) := (neg_neg _).symm
      _ = -(G (A := A) * U) := by rw [← hU]
  have hVG : V * G (A := A) = -(G (A := A) * V) := by
    calc
      V * G (A := A) = -(-(V * G (A := A))) := (neg_neg _).symm
      _ = -(G (A := A) * V) := by rw [← hV]
  have hUVG : U * V * G (A := A) = G (A := A) * U * V := by
    calc
      U * V * G (A := A) = U * (V * G (A := A)) := by rw [mul_assoc]
      _ = U * (-(G (A := A) * V)) := by rw [hVG]
      _ = -(U * G (A := A)) * V := by noncomm_ring
      _ = -(-(G (A := A) * U)) * V := by rw [hUG]
      _ = G (A := A) * U * V := by noncomm_ring
  have hVUG : V * U * G (A := A) = G (A := A) * V * U := by
    calc
      V * U * G (A := A) = V * (U * G (A := A)) := by rw [mul_assoc]
      _ = V * (-(G (A := A) * U)) := by rw [hUG]
      _ = -(V * G (A := A)) * U := by noncomm_ring
      _ = -(-(G (A := A) * V)) * U := by rw [hVG]
      _ = G (A := A) * V * U := by noncomm_ring
  have hU_GV : U * (G (A := A) * V) = -(G (A := A) * U * V) := by
    calc
      U * (G (A := A) * V) = (U * G (A := A)) * V := by rw [mul_assoc]
      _ = (-(G (A := A) * U)) * V := by rw [hUG]
      _ = -(G (A := A) * U * V) := by noncomm_ring
  have hV_GU : V * (G (A := A) * U) = -(G (A := A) * V * U) := by
    calc
      V * (G (A := A) * U) = (V * G (A := A)) * U := by rw [mul_assoc]
      _ = (-(G (A := A) * V)) * U := by rw [hVG]
      _ = -(G (A := A) * V * U) := by noncomm_ring
  rw [nambu3_eq_sum_comm]
  dsimp [lieComm]
  calc
    G (A := A) * (U * V - V * U) + U * (V * G (A := A) - G (A := A) * V) +
        V * (G (A := A) * U - U * G (A := A))
        = G (A := A) * U * V - G (A := A) * V * U +
            (U * V * G (A := A) - U * (G (A := A) * V)) +
            (V * (G (A := A) * U) - V * U * G (A := A)) := by noncomm_ring
    _ = G (A := A) * U * V - G (A := A) * V * U +
            (G (A := A) * U * V - -(G (A := A) * U * V)) +
            (-(G (A := A) * V * U) - G (A := A) * V * U) := by
          rw [hUVG, hU_GV, hV_GU, hVUG]
    _ = (3 : A) * (G (A := A) * (U * V - V * U)) := by
          norm_num [mul_sub, sub_mul]
          noncomm_ring

/-- Pairing chiral grading `G` with two Halmos noncommutativity obstructions `[P_L, P_1]`
and `[P_L, P_2]` gives an explicit `G`-even grade-3 element `(3 : A) * (G * [[P_L, P_1], [P_L, P_2]])`. -/
theorem nambu3_G_two_halmos_obstructions (P₁ P₂ : A) :
    nambu3 (G (A := A)) (comm S.PL P₁) (comm S.PL P₂) =
        (3 : A) * (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂)) ∧
      G (A := A) * nambu3 (G (A := A)) (comm S.PL P₁) (comm S.PL P₂) =
        nambu3 (G (A := A)) (comm S.PL P₁) (comm S.PL P₂) * G (A := A) := by
  have h1 : G (A := A) * comm S.PL P₁ = -(comm S.PL P₁ * G (A := A)) :=
    two_idempotent_comm_anticomm_G (A := A) P₁
  have h2 : G (A := A) * comm S.PL P₂ = -(comm S.PL P₂ * G (A := A)) :=
    two_idempotent_comm_anticomm_G (A := A) P₂
  have hval := nambu3_G_odd_pair_eq_three_G_mul_comm (comm S.PL P₁) (comm S.PL P₂) h1 h2
  have heven := odd_comm_is_even (comm S.PL P₁) (comm S.PL P₂) h1 h2
  have hG :
      G (A := A) * (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂)) =
        (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂)) * G (A := A) := by
    calc
      G (A := A) * (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂))
          = (G (A := A) * G (A := A)) * lieComm (comm S.PL P₁) (comm S.PL P₂) := by
              rw [mul_assoc]
      _ = lieComm (comm S.PL P₁) (comm S.PL P₂) := by rw [chiral_G_sq (A := A), one_mul]
      _ = lieComm (comm S.PL P₁) (comm S.PL P₂) * (G (A := A) * G (A := A)) := by
            rw [chiral_G_sq (A := A), mul_one]
      _ = (lieComm (comm S.PL P₁) (comm S.PL P₂) * G (A := A)) * G (A := A) := by
            rw [← mul_assoc]
      _ = (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂)) * G (A := A) := by
            rw [← heven]
  refine ⟨hval, ?_⟩
  rw [hval]
  calc
    G (A := A) * ((3 : A) * (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂)))
        = (3 : A) * (G (A := A) * (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂))) := by
            noncomm_ring
    _ = (3 : A) * ((G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂)) * G (A := A)) := by
          rw [hG]
    _ = ((3 : A) * (G (A := A) * lieComm (comm S.PL P₁) (comm S.PL P₂))) * G (A := A) := by
          noncomm_ring

end AbstractGradeTower

/-! ## Section 3: Sharp Dimensional Emergence (`M₂(ℤ)` Ceiling vs `M₄(ℤ)` Emergence) -/

/-- In `M₂(ℤ)`, grade-1 (`[P_L, E₀₁]`), grade-2 (`[E₀₁, E₁₀]`), and chiral-paired
grade-3 (`nambu3 G E₀₁ E₁₀ = 3 · I₂`) obstructions are all explicitly nonvanishing. -/
theorem mat2_grade1_grade2_nonvanishing :
    lieComm mat2PL mat2E01 = mat2E01 ∧
      lieComm mat2E01 mat2E10 = mat2G ∧
      nambu3 mat2G mat2E01 mat2E10 = !![(3 : ℤ), 0; 0, 3] ∧
      lieComm mat2PL mat2E01 ≠ 0 ∧
      lieComm mat2E01 mat2E10 ≠ 0 ∧
      nambu3 mat2G mat2E01 mat2E10 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **2D Soul Ceiling**: for ANY three anti-diagonal `2×2` matrices over a commutative ring `R`,
the pure odd Nambu 3-commutator vanishes identically (`nambu3 U V W = 0`), because the odd
Peirce corner space has dimension only `2`. -/
theorem mat2_pure_odd_nambu3_vanishes {R : Type*} [CommRing R]
    (u₁ u₂ v₁ v₂ w₁ w₂ : R) :
    nambu3 (!![(0 : R), u₁; u₂, 0]) (!![(0 : R), v₁; v₂, 0]) (!![(0 : R), w₁; w₂, 0]) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nambu3] <;> ring

/-- **Grade-3 Dimensional Emergence in `M₄(ℤ)`**: when each chiral sheet is enlarged to
rank `2` (`P_L = diag(1, 1, 0, 0)`), the odd Peirce subspace has dimension `8 > 2`, and three
odd transition generators `U, V, W` (`G * · = - · * G`) generate an emergent nonvanishing
`G`-odd Nambu trivector `nambu3 U V W = E₀₃ ≠ 0`. -/
theorem mat4_odd_nambu3_trivector_emerges :
    let G₄ := @G (Matrix (Fin 4) (Fin 4) ℤ) _ mat4ChiralPeirceSystem
    G₄ * mat4U = -(mat4U * G₄) ∧
      G₄ * mat4V = -(mat4V * G₄) ∧
      G₄ * mat4W = -(mat4W * G₄) ∧
      nambu3 mat4U mat4V mat4W = mat4E03 ∧
      nambu3 mat4U mat4V mat4W ≠ 0 ∧
      G₄ * nambu3 mat4U mat4V mat4W = -(nambu3 mat4U mat4V mat4W * G₄) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end InfoGeometry.Synthesis.PeirceNambuHigherGradeObstructionBridge
