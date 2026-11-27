/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.PeirceNambuHigherGradeObstructionBridge
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Algebra.AssociativityObstruction
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Algebra.H3ZornFreudenthalTKK5E8
import InfoGeometry.Canonical.SouriauBostConnesTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Higher-Grade Obstruction Tower & Theoretical Framework Closure

This module completes the obstruction-to-higher-grade emergence spine across
grades `1 → 2 → 3 → 4 → 5`, nonassociative octonionic obstructions, the
248-dimensional 5-graded simple Killing Lie algebra `FreudenthalTKK5E8` (`E₈(8)`),
and infinite-dimensional `H_lp` sewn `Cl(1,1)` / Cuntz `O₂` boundary anomaly
cancellation:

1. **Standard Antisymmetric Obstruction Tower (`alt4`, `alt5`)**:
   - Every commutative ring collapses `lieComm`, `nambu3`, `alt4`, and `alt5` to `0`
     (`commRing_higher_grades_collapse`).
   - Under a chiral Peirce system `[ChiralPeirceSystem A]` with grading `G`:
     - Grade 1 (`[P_L, ·]`): `G`-odd;
     - Grade 2 (`[U, V]`): `G`-even;
     - Grade 3 (`nambu3 U V W`): `G`-odd;
     - Grade 4 (`alt4 U₁ U₂ U₃ U₄`): `G`-even (`alt4_four_odd_is_even`);
     - Grade 5 (`alt5 U₁ U₂ U₃ U₄ U₅`): `G`-odd (`alt5_five_odd_anticomm_G`).
2. **Sharp Dimensional Thresholds (Amitsur–Levitzki `2 → 4 → 6`)**:
   - `amitsur_levitzki_mat2_alt4_vanishes` & `amitsur_levitzki_mat2_alt5_vanishes`:
     for ANY matrices on `M₂(R)` (`[CommRing R]`), `alt4 = 0` and `alt5 = 0` identically.
   - `mat4_alt4_odd_regenerates_chiral_grading`: on `M₄(ℤ)`, four odd generators
     `E₀₂, E₂₁, E₁₃, E₃₀` satisfy `alt4 E₀₂ E₂₁ E₁₃ E₃₀ = G₄ ≠ 0` (the grade-4
     obstruction regenerates the chiral grading involution).
   - `mat6_alt5_odd_emerges_nonzero`: on `M₆(ℤ)` (rank-3 sheets), five odd
     generators `E₀₃, E₃₁, E₁₄, E₄₂, E₂₅` satisfy `alt5 = E₀₅ ≠ 0`, `G₆`-odd.
3. **Nonassociative Threshold & Consolidated Framework Capstone**:
   - `zorn_no_associative_embedding`: nonassociativity of `ZornMatrix ℝ` blocks
     any injective multiplicative embedding into any associative semigroup.
   - `framework_obstruction_to_higher_grade_closure`: unifies Peirce Maurer–Cartan
     self-dual Yang–Mills (`genV`), grade `3 → 4 → 5` obstruction emergence,
     the octonionic associativity obstruction, the 248D 5-graded simple Killing Lie
     algebra `FreudenthalTKK5E8`, and infinite-dimensional `H_lp` boundary anomaly
     cancellation.
-/

namespace InfoGeometry.Synthesis.HigherGradeObstructionTowerClosure

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra
open InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
open InfoGeometry.Synthesis.PeirceNambuHigherGradeObstructionBridge

/-! ## Section 1: Closed T16 Witnesses & `M₆(ℤ)` Chiral Peirce System -/

/-- Closed noncommutativity witness on `M₂(ℤ)` inherited from `PeirceNambuHigherGradeObstructionBridge`. -/
theorem mat2_int_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A :=
  mat2_int_noncommutative

/-- Closed noncommutativity witness on `M₄(ℤ)` inherited from `PeirceNambuHigherGradeObstructionBridge`. -/
theorem mat4_int_noncomm :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℤ, A * B ≠ B * A :=
  mat4_int_noncommutative

/-- Standard matrix unit `Eᵢⱼ` on `M₆(ℤ)`. -/
def mat6Unit (i j : Fin 6) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of (fun r c => if r = i ∧ c = j then 1 else 0)

@[simp]
theorem mat6Unit_mul (i j k l : Fin 6) :
    mat6Unit i j * mat6Unit k l = if j = k then mat6Unit i l else 0 := by
  ext r c
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte, mat6Unit, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single j]
    · by_cases hr : r = i <;> by_cases hc : c = l <;> simp [hr, hc]
    · intro x _ hx
      simp [hx]
    · intro hmem
      exact absurd (Finset.mem_univ j) hmem
  · simp only [hjk, ↓reduceIte, mat6Unit, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = j
    · subst hx
      simp [hjk]
    · simp [hx]

/-- Closed noncommutativity witness on `M₆(ℤ)` (T16 carrier discipline). -/
theorem mat6_int_noncomm :
    ∃ A B : Matrix (Fin 6) (Fin 6) ℤ, A * B ≠ B * A := by
  refine ⟨mat6Unit 0 3, mat6Unit 3 1, ?_⟩
  rw [mat6Unit_mul, mat6Unit_mul]
  simp only [↓reduceIte, show (1 : Fin 6) ≠ 0 by decide]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M 0 1) h
  simp [mat6Unit] at h01

/-- Fourth odd transition generator `E₃₀` on `M₄(ℤ)` closing the alternating 4-cycle. -/
def mat4X : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0]

/-- Left rank-3 block idempotent `diag(1, 1, 1, 0, 0, 0)` on `M₆(ℤ)`. -/
def mat6PL : Matrix (Fin 6) (Fin 6) ℤ :=
  mat6Unit 0 0 + mat6Unit 1 1 + mat6Unit 2 2

/-- Right rank-3 block idempotent `diag(0, 0, 0, 1, 1, 1)` on `M₆(ℤ)`. -/
def mat6PR : Matrix (Fin 6) (Fin 6) ℤ :=
  mat6Unit 3 3 + mat6Unit 4 4 + mat6Unit 5 5

private theorem mat6PL_sq : mat6PL * mat6PL = mat6PL := by
  dsimp [mat6PL]
  simp only [mul_add, add_mul, mat6Unit_mul]
  simp

private theorem mat6PR_sq : mat6PR * mat6PR = mat6PR := by
  dsimp [mat6PR]
  simp only [mul_add, add_mul, mat6Unit_mul]
  simp

private theorem mat6_sum : mat6PL + mat6PR = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [mat6PL, mat6PR, mat6Unit]

private theorem mat6_ortho : mat6PL * mat6PR = 0 := by
  dsimp [mat6PL, mat6PR]
  simp only [mul_add, add_mul, mat6Unit_mul]
  simp

/-- Constructive rank `(3, 3)` `ChiralPeirceSystem` on `M₆(ℤ)`. -/
@[instance_reducible]
def mat6ChiralPeirceSystem : ChiralPeirceSystem (Matrix (Fin 6) (Fin 6) ℤ) where
  PL := mat6PL
  PR := mat6PR
  h_PL_sq := mat6PL_sq
  h_PR_sq := mat6PR_sq
  h_sum := mat6_sum
  h_PL_PR := mat6_ortho

/-! ## Section 2: Inductive Grade `2 → 3 → 4 → 5` Obstruction Tower -/

section StandardObstructionTower

section GeneralRing

variable {R : Type*} [Ring R]

/-- Standard 4-ary alternating associative polynomial built inductively from `nambu3`:
`alt4 A B C D = A * nambu3 B C D - B * nambu3 C D A + C * nambu3 D A B - D * nambu3 A B C`. -/
def alt4 (A B C D : R) : R :=
  A * nambu3 B C D - B * nambu3 C D A + C * nambu3 D A B - D * nambu3 A B C

/-- Standard 5-ary alternating associative polynomial built inductively from `alt4`:
`alt5 A B C D E = ∑_cyc X₁ * alt4 X₂ X₃ X₄ X₅`. -/
def alt5 (A B C D E : R) : R :=
  A * alt4 B C D E + B * alt4 C D E A + C * alt4 D E A B +
    D * alt4 E A B C + E * alt4 A B C D

/-- Commutativity of `1` kills `alt4` in any associative ring. -/
theorem alt4_one_left (B C D : R) : alt4 (1 : R) B C D = 0 := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_swap12 (A B C D : R) : alt4 B A C D = -alt4 A B C D := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_swap23 (A B C D : R) : alt4 A C B D = -alt4 A B C D := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_swap34 (A B C D : R) : alt4 A B D C = -alt4 A B C D := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_one_two (A C D : R) : alt4 A (1 : R) C D = 0 := by
  rw [alt4_swap12, alt4_one_left, neg_zero]

theorem alt4_one_three (A B D : R) : alt4 A B (1 : R) D = 0 := by
  rw [alt4_swap23, alt4_one_two, neg_zero]

theorem alt4_one_four (A B C : R) : alt4 A B C (1 : R) = 0 := by
  rw [alt4_swap34, alt4_one_three, neg_zero]

theorem alt4_diag12 (A C D : R) : alt4 A A C D = 0 := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_diag23 (A B D : R) : alt4 A B B D = 0 := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_diag34 (A B C : R) : alt4 A B C C = 0 := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_diag13 (A B D : R) : alt4 A B A D = 0 := by
  rw [alt4_swap23, alt4_diag12, neg_zero]

theorem alt4_diag14 (A B C : R) : alt4 A B C A = 0 := by
  rw [alt4_swap34, alt4_diag13, neg_zero]

theorem alt4_diag24 (A B C : R) : alt4 A B C B = 0 := by
  rw [alt4_swap34, alt4_diag23, neg_zero]

theorem alt4_add_left (A₁ A₂ B C D : R) :
    alt4 (A₁ + A₂) B C D = alt4 A₁ B C D + alt4 A₂ B C D := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_add_two (A B₁ B₂ C D : R) :
    alt4 A (B₁ + B₂) C D = alt4 A B₁ C D + alt4 A B₂ C D := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_add_three (A B C₁ C₂ D : R) :
    alt4 A B (C₁ + C₂) D = alt4 A B C₁ D + alt4 A B C₂ D := by
  dsimp [alt4, nambu3]
  noncomm_ring

theorem alt4_add_four (A B C D₁ D₂ : R) :
    alt4 A B C (D₁ + D₂) = alt4 A B C D₁ + alt4 A B C D₂ := by
  dsimp [alt4, nambu3]
  noncomm_ring

/-- All higher-grade obstructions `lieComm`, `nambu3`, `alt4`, and `alt5` collapse identically
in every commutative ring. -/
theorem commRing_higher_grades_collapse {C : Type*} [CommRing C] (a b c d e : C) :
    lieComm a b = 0 ∧ nambu3 a b c = 0 ∧ alt4 a b c d = 0 ∧ alt5 a b c d e = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [alt5, alt4, nambu3, lieComm]
      ring

end GeneralRing

section CommRingAlgebra

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]

theorem alt4_smul_left (c : K) (X Y Z W : A) :
    alt4 (c • X) Y Z W = c • alt4 X Y Z W := by
  dsimp [alt4, nambu3]
  simp only [mul_add, mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  module

theorem alt4_smul_two (c : K) (X Y Z W : A) :
    alt4 X (c • Y) Z W = c • alt4 X Y Z W := by
  dsimp [alt4, nambu3]
  simp only [mul_add, mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  module

theorem alt4_smul_three (c : K) (X Y Z W : A) :
    alt4 X Y (c • Z) W = c • alt4 X Y Z W := by
  dsimp [alt4, nambu3]
  simp only [mul_add, mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  module

theorem alt4_smul_four (c : K) (X Y Z W : A) :
    alt4 X Y Z (c • W) = c • alt4 X Y Z W := by
  dsimp [alt4, nambu3]
  simp only [mul_add, mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  module

theorem alt4_unit_add_left (c : K) (X Y Z W : A) :
    alt4 (c • (1 : A) + X) Y Z W = alt4 X Y Z W := by
  rw [alt4_add_left, alt4_smul_left, alt4_one_left, smul_zero, zero_add]

theorem alt4_unit_add_two (c : K) (X Y Z W : A) :
    alt4 X (c • (1 : A) + Y) Z W = alt4 X Y Z W := by
  rw [alt4_add_two, alt4_smul_two, alt4_one_two, smul_zero, zero_add]

theorem alt4_unit_add_three (c : K) (X Y Z W : A) :
    alt4 X Y (c • (1 : A) + Z) W = alt4 X Y Z W := by
  rw [alt4_add_three, alt4_smul_three, alt4_one_three, smul_zero, zero_add]

theorem alt4_unit_add_four (c : K) (X Y Z W : A) :
    alt4 X Y Z (c • (1 : A) + W) = alt4 X Y Z W := by
  rw [alt4_add_four, alt4_smul_four, alt4_one_four, smul_zero, zero_add]

/-- **Pigeonhole Vanishing on a 3-Generator Submodule**: in any `K`-algebra `A`, any four
elements lying in the span of three generators `{e₁, e₂, e₃}` satisfy `alt4 = 0`. -/
theorem alt4_eq_zero_of_three_generators (e₁ e₂ e₃ : A)
    (x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ w₁ w₂ w₃ : K) :
    alt4 (x₁ • e₁ + x₂ • e₂ + x₃ • e₃) (y₁ • e₁ + y₂ • e₂ + y₃ • e₃)
      (z₁ • e₁ + z₂ • e₂ + z₃ • e₃) (w₁ • e₁ + w₂ • e₂ + w₃ • e₃) = 0 := by
  simp only [alt4_add_left, alt4_add_two, alt4_add_three, alt4_add_four,
    alt4_smul_left, alt4_smul_two, alt4_smul_three, alt4_smul_four,
    alt4_diag12, alt4_diag13, alt4_diag14, alt4_diag23, alt4_diag24, alt4_diag34,
    smul_zero, add_zero]

end CommRingAlgebra

section ChiralGradingParityTower

variable {A : Type*} [Ring A] [S : ChiralPeirceSystem A]

private lemma odd_mul_odd_is_even (X Y : A)
    (hX : G (A := A) * X = -(X * G (A := A)))
    (hY : G (A := A) * Y = -(Y * G (A := A))) :
    G (A := A) * (X * Y) = (X * Y) * G (A := A) := by
  calc
    G (A := A) * (X * Y) = (G (A := A) * X) * Y := by rw [mul_assoc]
    _ = (-(X * G (A := A))) * Y := by rw [hX]
    _ = -(X * (G (A := A) * Y)) := by noncomm_ring
    _ = -(X * (-(Y * G (A := A)))) := by rw [hY]
    _ = (X * Y) * G (A := A) := by noncomm_ring

private lemma odd_mul_even_is_odd (X E : A)
    (hX : G (A := A) * X = -(X * G (A := A)))
    (hE : G (A := A) * E = E * G (A := A)) :
    G (A := A) * (X * E) = -((X * E) * G (A := A)) := by
  calc
    G (A := A) * (X * E) = (G (A := A) * X) * E := by rw [mul_assoc]
    _ = (-(X * G (A := A))) * E := by rw [hX]
    _ = -(X * (G (A := A) * E)) := by noncomm_ring
    _ = -(X * (E * G (A := A))) := by rw [hE]
    _ = -((X * E) * G (A := A)) := by rw [mul_assoc]

/-- Grade `3 + 1 → 4`: the 4-ary alternating obstruction of four `G`-odd elements is `G`-even. -/
theorem alt4_four_odd_is_even (U₁ U₂ U₃ U₄ : A)
    (h1 : G (A := A) * U₁ = -(U₁ * G (A := A)))
    (h2 : G (A := A) * U₂ = -(U₂ * G (A := A)))
    (h3 : G (A := A) * U₃ = -(U₃ * G (A := A)))
    (h4 : G (A := A) * U₄ = -(U₄ * G (A := A))) :
    G (A := A) * alt4 U₁ U₂ U₃ U₄ = alt4 U₁ U₂ U₃ U₄ * G (A := A) := by
  have t1 := odd_mul_odd_is_even U₁ (nambu3 U₂ U₃ U₄) h1
    (nambu3_three_odd_anticomm_G U₂ U₃ U₄ h2 h3 h4)
  have t2 := odd_mul_odd_is_even U₂ (nambu3 U₃ U₄ U₁) h2
    (nambu3_three_odd_anticomm_G U₃ U₄ U₁ h3 h4 h1)
  have t3 := odd_mul_odd_is_even U₃ (nambu3 U₄ U₁ U₂) h3
    (nambu3_three_odd_anticomm_G U₄ U₁ U₂ h4 h1 h2)
  have t4 := odd_mul_odd_is_even U₄ (nambu3 U₁ U₂ U₃) h4
    (nambu3_three_odd_anticomm_G U₁ U₂ U₃ h1 h2 h3)
  dsimp [alt4]
  calc
    G (A := A) * (U₁ * nambu3 U₂ U₃ U₄ - U₂ * nambu3 U₃ U₄ U₁ +
        U₃ * nambu3 U₄ U₁ U₂ - U₄ * nambu3 U₁ U₂ U₃)
        = G (A := A) * (U₁ * nambu3 U₂ U₃ U₄) - G (A := A) * (U₂ * nambu3 U₃ U₄ U₁) +
            G (A := A) * (U₃ * nambu3 U₄ U₁ U₂) - G (A := A) * (U₄ * nambu3 U₁ U₂ U₃) := by
              noncomm_ring
    _ = (U₁ * nambu3 U₂ U₃ U₄) * G (A := A) - (U₂ * nambu3 U₃ U₄ U₁) * G (A := A) +
            (U₃ * nambu3 U₄ U₁ U₂) * G (A := A) - (U₄ * nambu3 U₁ U₂ U₃) * G (A := A) := by
              rw [t1, t2, t3, t4]
    _ = (U₁ * nambu3 U₂ U₃ U₄ - U₂ * nambu3 U₃ U₄ U₁ +
            U₃ * nambu3 U₄ U₁ U₂ - U₄ * nambu3 U₁ U₂ U₃) * G (A := A) := by noncomm_ring

/-- Grade `4 + 1 → 5`: the 5-ary alternating obstruction of five `G`-odd elements stays `G`-odd. -/
theorem alt5_five_odd_anticomm_G (U₁ U₂ U₃ U₄ U₅ : A)
    (h1 : G (A := A) * U₁ = -(U₁ * G (A := A)))
    (h2 : G (A := A) * U₂ = -(U₂ * G (A := A)))
    (h3 : G (A := A) * U₃ = -(U₃ * G (A := A)))
    (h4 : G (A := A) * U₄ = -(U₄ * G (A := A)))
    (h5 : G (A := A) * U₅ = -(U₅ * G (A := A))) :
    G (A := A) * alt5 U₁ U₂ U₃ U₄ U₅ = -(alt5 U₁ U₂ U₃ U₄ U₅ * G (A := A)) := by
  have t1 := odd_mul_even_is_odd U₁ (alt4 U₂ U₃ U₄ U₅) h1
    (alt4_four_odd_is_even U₂ U₃ U₄ U₅ h2 h3 h4 h5)
  have t2 := odd_mul_even_is_odd U₂ (alt4 U₃ U₄ U₅ U₁) h2
    (alt4_four_odd_is_even U₃ U₄ U₅ U₁ h3 h4 h5 h1)
  have t3 := odd_mul_even_is_odd U₃ (alt4 U₄ U₅ U₁ U₂) h3
    (alt4_four_odd_is_even U₄ U₅ U₁ U₂ h4 h5 h1 h2)
  have t4 := odd_mul_even_is_odd U₄ (alt4 U₅ U₁ U₂ U₃) h4
    (alt4_four_odd_is_even U₅ U₁ U₂ U₃ h5 h1 h2 h3)
  have t5 := odd_mul_even_is_odd U₅ (alt4 U₁ U₂ U₃ U₄) h5
    (alt4_four_odd_is_even U₁ U₂ U₃ U₄ h1 h2 h3 h4)
  dsimp [alt5]
  calc
    G (A := A) * (U₁ * alt4 U₂ U₃ U₄ U₅ + U₂ * alt4 U₃ U₄ U₅ U₁ +
        U₃ * alt4 U₄ U₅ U₁ U₂ + U₄ * alt4 U₅ U₁ U₂ U₃ + U₅ * alt4 U₁ U₂ U₃ U₄)
        = G (A := A) * (U₁ * alt4 U₂ U₃ U₄ U₅) + G (A := A) * (U₂ * alt4 U₃ U₄ U₅ U₁) +
            G (A := A) * (U₃ * alt4 U₄ U₅ U₁ U₂) + G (A := A) * (U₄ * alt4 U₅ U₁ U₂ U₃) +
            G (A := A) * (U₅ * alt4 U₁ U₂ U₃ U₄) := by noncomm_ring
    _ = -((U₁ * alt4 U₂ U₃ U₄ U₅) * G (A := A)) + -((U₂ * alt4 U₃ U₄ U₅ U₁) * G (A := A)) +
            -((U₃ * alt4 U₄ U₅ U₁ U₂) * G (A := A)) + -((U₄ * alt4 U₅ U₁ U₂ U₃) * G (A := A)) +
            -((U₅ * alt4 U₁ U₂ U₃ U₄) * G (A := A)) := by rw [t1, t2, t3, t4, t5]
    _ = -((U₁ * alt4 U₂ U₃ U₄ U₅ + U₂ * alt4 U₃ U₄ U₅ U₁ + U₃ * alt4 U₄ U₅ U₁ U₂ +
            U₄ * alt4 U₅ U₁ U₂ U₃ + U₅ * alt4 U₁ U₂ U₃ U₄) * G (A := A)) := by noncomm_ring

end ChiralGradingParityTower

end StandardObstructionTower

/-! ## Section 3: Sharp Amitsur–Levitzki Thresholds (`M₂` Ceiling vs `M₄` vs `M₆`) -/

private lemma mat2_decomp {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M = M 1 1 • (1 : Matrix (Fin 2) (Fin 2) R) +
      ((M 0 0 - M 1 1) • !![(1 : R), 0; 0, 0] +
        M 0 1 • !![(0 : R), 1; 0, 0] + M 1 0 • !![(0 : R), 0; 1, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Amitsur–Levitzki `2×2` Ceiling (Grade 4)**: for ANY four `2×2` matrices over a commutative
ring `R`, `alt4` vanishes identically (by unit stripping + 3-generator pigeonhole). -/
theorem amitsur_levitzki_mat2_alt4_vanishes {R : Type*} [CommRing R]
    (A B C D : Matrix (Fin 2) (Fin 2) R) :
    alt4 A B C D = 0 := by
  conv_lhs => rw [mat2_decomp A, mat2_decomp B, mat2_decomp C, mat2_decomp D]
  rw [alt4_unit_add_left, alt4_unit_add_two, alt4_unit_add_three, alt4_unit_add_four]
  exact alt4_eq_zero_of_three_generators
    !![(1 : R), 0; 0, 0] !![(0 : R), 1; 0, 0] !![(0 : R), 0; 1, 0]
    (A 0 0 - A 1 1) (A 0 1) (A 1 0)
    (B 0 0 - B 1 1) (B 0 1) (B 1 0)
    (C 0 0 - C 1 1) (C 0 1) (C 1 0)
    (D 0 0 - D 1 1) (D 0 1) (D 1 0)

/-- **Amitsur–Levitzki `2×2` Ceiling (Grade 5)**: for ANY five `2×2` matrices over a commutative
ring `R`, `alt5` vanishes identically as a direct consequence of grade-4 vanishing. -/
theorem amitsur_levitzki_mat2_alt5_vanishes {R : Type*} [CommRing R]
    (A B C D E : Matrix (Fin 2) (Fin 2) R) :
    alt5 A B C D E = 0 := by
  unfold alt5
  simp [amitsur_levitzki_mat2_alt4_vanishes]

/-- **Grade-4 Chiral Regeneration in `M₄(ℤ)`**: four odd transition generators
`E₀₂, E₂₁, E₁₃, E₃₀` in `M₄(ℤ)` break the Amitsur–Levitzki `M₂` ceiling and regenerate
the exact chiral grading operator `G₄ = P_L - P_R ≠ 0`. -/
theorem mat4_alt4_odd_regenerates_chiral_grading :
    let G₄ := @G (Matrix (Fin 4) (Fin 4) ℤ) _ mat4ChiralPeirceSystem
    G₄ * mat4U = -(mat4U * G₄) ∧
      G₄ * mat4V = -(mat4V * G₄) ∧
      G₄ * mat4W = -(mat4W * G₄) ∧
      G₄ * mat4X = -(mat4X * G₄) ∧
      alt4 mat4U mat4V mat4W mat4X = G₄ ∧
      alt4 mat4U mat4V mat4W mat4X ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Grade-5 Odd Emergence in `M₆(ℤ)`**: enlarging each chiral sheet to rank `3`
(`PL = diag(1, 1, 1, 0, 0, 0)`) breaks the `M₄` grade-4 ceiling; five odd transition units
`E₀₃, E₃₁, E₁₄, E₄₂, E₂₅` satisfy `alt5 = E₀₅ ≠ 0` and remain `G₆`-odd. -/
theorem mat6_alt5_odd_emerges_nonzero :
    let G₆ := @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem
    let U₁ := mat6Unit 0 3
    let U₂ := mat6Unit 3 1
    let U₃ := mat6Unit 1 4
    let U₄ := mat6Unit 4 2
    let U₅ := mat6Unit 2 5
    G₆ * U₁ = -(U₁ * G₆) ∧
      G₆ * U₂ = -(U₂ * G₆) ∧
      G₆ * U₃ = -(U₃ * G₆) ∧
      G₆ * U₄ = -(U₄ * G₆) ∧
      G₆ * U₅ = -(U₅ * G₆) ∧
      alt5 U₁ U₂ U₃ U₄ U₅ = mat6Unit 0 5 ∧
      alt5 U₁ U₂ U₃ U₄ U₅ ≠ 0 ∧
      G₆ * alt5 U₁ U₂ U₃ U₄ U₅ = -(alt5 U₁ U₂ U₃ U₄ U₅ * G₆) := by
  have hU1 : @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem * mat6Unit 0 3 =
      -(mat6Unit 0 3 * @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem) := by
    change (mat6PL - mat6PR) * mat6Unit 0 3 = -(mat6Unit 0 3 * (mat6PL - mat6PR))
    simp [mat6PL, mat6PR, sub_mul, mul_sub, add_mul, mul_add]
  have hU2 : @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem * mat6Unit 3 1 =
      -(mat6Unit 3 1 * @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem) := by
    change (mat6PL - mat6PR) * mat6Unit 3 1 = -(mat6Unit 3 1 * (mat6PL - mat6PR))
    simp [mat6PL, mat6PR, sub_mul, mul_sub, add_mul, mul_add]
  have hU3 : @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem * mat6Unit 1 4 =
      -(mat6Unit 1 4 * @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem) := by
    change (mat6PL - mat6PR) * mat6Unit 1 4 = -(mat6Unit 1 4 * (mat6PL - mat6PR))
    simp [mat6PL, mat6PR, sub_mul, mul_sub, add_mul, mul_add]
  have hU4 : @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem * mat6Unit 4 2 =
      -(mat6Unit 4 2 * @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem) := by
    change (mat6PL - mat6PR) * mat6Unit 4 2 = -(mat6Unit 4 2 * (mat6PL - mat6PR))
    simp [mat6PL, mat6PR, sub_mul, mul_sub, add_mul, mul_add]
  have hU5 : @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem * mat6Unit 2 5 =
      -(mat6Unit 2 5 * @G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem) := by
    change (mat6PL - mat6PR) * mat6Unit 2 5 = -(mat6Unit 2 5 * (mat6PL - mat6PR))
    simp [mat6PL, mat6PR, sub_mul, mul_sub, add_mul, mul_add]
  have halt5 :
      alt5 (mat6Unit 0 3) (mat6Unit 3 1) (mat6Unit 1 4) (mat6Unit 4 2) (mat6Unit 2 5) =
        mat6Unit 0 5 := by
    simp [alt5, alt4, nambu3]
  have hne : mat6Unit 0 5 ≠ 0 := by
    intro h
    have h05 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M 0 5) h
    simp [mat6Unit] at h05
  have hodd5 :=
    @alt5_five_odd_anticomm_G (Matrix (Fin 6) (Fin 6) ℤ) _ mat6ChiralPeirceSystem
      (mat6Unit 0 3) (mat6Unit 3 1) (mat6Unit 1 4) (mat6Unit 4 2) (mat6Unit 2 5)
      hU1 hU2 hU3 hU4 hU5
  refine ⟨hU1, hU2, hU3, hU4, hU5, halt5, ?_, hodd5⟩
  rw [halt5]
  exact hne

/-! ## Section 4: Nonassociative Threshold & Consolidated Framework Capstone -/

/-- **Nonassociative Obstruction Threshold**: the real split-octonion Zorn carrier `ZornMatrix ℝ`
cannot embed injectively and multiplicatively into any associative semigroup (or matrix algebra). -/
theorem zorn_no_associative_embedding {A : Type*} [Semigroup A] :
    ¬ ∃ φ : InfoGeometry.Algebra.ZornMatrix ℝ → A,
        Function.Injective φ ∧ (∀ x y, φ (x * y) = φ x * φ y) :=
  InfoGeometry.Algebra.no_injective_mul_map_to_semigroup_of_nonassociative
    ⟨InfoGeometry.Algebra.ZornMatrix.U 0, InfoGeometry.Algebra.ZornMatrix.U 1,
      InfoGeometry.Algebra.ZornMatrix.U 2,
      InfoGeometry.Algebra.ZornMatrix.nonassociative_witness (R := ℝ)⟩

/-- **Unified Framework Closure Theorem**: connects:
1. Grade `1–2` Peirce Maurer–Cartan curvature decomposition & covariant self-dual Yang–Mills Bianchi
   identity (`PeirceDefectBridge`),
2. Grade `3` Nambu trivector emergence (`M₄(ℤ)`),
3. Grade `4` Amitsur–Levitzki chiral regeneration `alt4 = G₄` (`M₄(ℤ)`),
4. Grade `5` antisymmetric 5-bracket emergence `alt5 = E₀₅ ≠ 0` (`M₆(ℤ)`),
5. Nonassociative split-octonion associator obstruction (`ZornMatrix ℝ`),
6. Simple Killing 248-dimensional 5-graded split `E₈(8)` realization (`FreudenthalTKK5E8`), and
7. Infinite-dimensional `H_lp` sewn `Cl(1,1)` / Cuntz `O₂` boundary anomaly cancellation. -/
theorem framework_obstruction_to_higher_grade_closure
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A_op C_op : B)
    (R_alg : Type*) [Semigroup R_alg]
    {i j : ℤ} {U V : InfoGeometry.Algebra.FreudenthalTKK5E8}
    (hU : U ∈ InfoGeometry.Algebra.gGrade i)
    (hV : V ∈ InfoGeometry.Algebra.gGrade j) :
    InfoGeometry.OperatorAlgebra.PeirceDefectBridge.peirceCovariantDeriv P A_op C_op
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op) = 0 ∧
      nambu3 mat4U mat4V mat4W ≠ 0 ∧
      alt4 mat4U mat4V mat4W mat4X =
        @G (Matrix (Fin 4) (Fin 4) ℤ) _ mat4ChiralPeirceSystem ∧
      alt5 (mat6Unit 0 3) (mat6Unit 3 1) (mat6Unit 1 4) (mat6Unit 4 2) (mat6Unit 2 5) =
        mat6Unit 0 5 ∧
      (¬ ∃ φ : InfoGeometry.Algebra.ZornMatrix ℝ → R_alg,
        Function.Injective φ ∧ (∀ x y, φ (x * y) = φ x * φ y)) ∧
      Module.finrank ℝ InfoGeometry.Algebra.FreudenthalTKK5E8 = 248 ∧
      LieAlgebra.IsSimple ℝ InfoGeometry.Algebra.FreudenthalTKK5E8 ∧
      LieAlgebra.IsKilling ℝ InfoGeometry.Algebra.FreudenthalTKK5E8 ∧
      ⁅U, V⁆ ∈ InfoGeometry.Algebra.gGrade (i + j) ∧
      (∀ k : ℤ, 2 < |k| → InfoGeometry.Algebra.gGrade k = ⊥) ∧
      InfoGeometry.Canonical.SouriauBostConnesTransition.d7InfiniteHilbertSewnAnomalyCancellationArchetype.claim () := by
  have hYM :=
    InfoGeometry.OperatorAlgebra.PeirceDefectBridge.peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills
      hP A_op C_op A_op C_op
  have hG3 := mat4_odd_nambu3_trivector_emerges
  have hG4 := mat4_alt4_odd_regenerates_chiral_grading
  have hG5 := mat6_alt5_odd_emerges_nonzero
  have hE8 := InfoGeometry.Algebra.freudenthalTKK5E8_split_real_form_invariants
  have hd7 := InfoGeometry.Canonical.SouriauBostConnesTransition.d7InfiniteHilbertSewnAnomalyCancellationArchetype.evidence ()
  exact ⟨hYM.2.2.2.2.2.2.2.2.2.1, hG3.2.2.2.2.1, hG4.2.2.2.2.1, hG5.2.2.2.2.2.1,
    zorn_no_associative_embedding, hE8.1, hE8.2.2.2.2.2.2.2.2.1, hE8.2.2.2.2.2.2.2.2.2.1,
    InfoGeometry.Algebra.gGrade_bracket_mem hU hV,
    InfoGeometry.Algebra.gGrade_eq_bot_of_abs_gt_two, hd7⟩

end InfoGeometry.Synthesis.HigherGradeObstructionTowerClosure
