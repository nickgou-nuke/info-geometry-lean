/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.RoseDrazinPolynomial

/-!
# Greville 1973: Souriau--Frame algorithm and Drazin pseudoinverse

Source digest:

T. N. E. Greville, "The Souriau--Frame Algorithm and the Drazin
Pseudoinverse", Linear Algebra and Its Applications 6, 205--208 (1973).

The paper shows that the Souriau--Frame/Faddeev--LeVerrier coefficient
sequence does not merely produce the ordinary inverse in the nonsingular case:
for a singular square matrix it produces the Drazin pseudoinverse.  If `r` is
the first index with `B_r = 0`, `s` is the last index with `p_s ≠ 0`, and
`k = r - s`, then Greville's formula is

`X = p_s^(-k-1) A^k B_(s-1)^(k+1)`.

The Lean-native part below formalizes:
1. A strict exact rational packet with `s = 1`, `r = 3`, `k = 2` (proved constructively
   via explicit matrix entry evaluations without `native_decide`).  The separate
   `mat3_noncommutativity_witness` only records that `Mat3 ℚ` is a noncommutative ring
   (two matrix units fail to commute); it is not part of the Greville content.
2. **Ring-level specialisation of the polynomial construction (`Section 2`)**:
   `grevilleSouriauFrameCandidate a b_prev inv_ps k` is by definition
   `polynomialDrazinCandidate a (b_prev * inv_ps) k`.  If `a` commutes with `b_prev`
   and `inv_ps` and the index-`k` factorization hypothesis
   `a ^ (k + 1) * (b_prev * inv_ps) = a ^ k` holds, it is an index-`k` Drazin inverse
   of `a`.

Not formalized: deriving that factorization from the Souriau--Frame recurrence
(`B_r = 0`, `p_s ≠ 0`); and `inv_ps` is an arbitrary ring element, so Greville's
scalar formula `p_s^(-k-1) A^k B_(s-1)^(k+1)` is recovered only when `inv_ps` is a
central scalar `p_s⁻¹`.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrevilleSouriauFrameDrazin

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RoseDrazinPolynomial

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-- Two matrix units used to make the noncommutative `Mat3 ℚ` carrier explicit. -/
def matrixUnit01 : Mat3 ℚ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- The transposed matrix unit to `matrixUnit01`. -/
def matrixUnit10 : Mat3 ℚ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- Explicit non-commutativity witness on `Mat3 ℚ`: `matrixUnit01` and `matrixUnit10` do not commute. -/
theorem mat3_noncommutativity_witness :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : Mat3 ℚ => M 0 0) h
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-! ## Exact `k = 2` Souriau--Frame packet -/

/-- A matrix with a size-two zero Jordan block and a regular eigenvalue `2`. -/
def grevilleA : Mat3 ℚ :=
  !![0, 1, 0;
     0, 0, 0;
     0, 0, 2]

/-- `B₀ = I`. -/
def grevilleB0 : Mat3 ℚ :=
  1

/-- `p₁ = trace(A B₀) = 2`. -/
def grevilleP1 : ℚ :=
  2

/-- `B₁ = A B₀ - p₁ I`. -/
def grevilleB1 : Mat3 ℚ :=
  grevilleA * grevilleB0 - grevilleP1 • (1 : Mat3 ℚ)

/-- `p₂ = 1/2 trace(A B₁) = 0`. -/
def grevilleP2 : ℚ :=
  0

/-- `B₂ = A B₁ - p₂ I`. -/
def grevilleB2 : Mat3 ℚ :=
  grevilleA * grevilleB1 - grevilleP2 • (1 : Mat3 ℚ)

/-- `p₃ = 1/3 trace(A B₂) = 0`. -/
def grevilleP3 : ℚ :=
  0

/-- `B₃ = A B₂ - p₃ I = 0`; this is the first zero in the packet. -/
def grevilleB3 : Mat3 ℚ :=
  grevilleA * grevilleB2 - grevilleP3 • (1 : Mat3 ℚ)

/-- Explicit matrix form of `grevilleB1`. -/
theorem grevilleB1_eq :
    grevilleB1 = !![(-2 : ℚ), 1, 0; 0, -2, 0; 0, 0, 0] := by
  unfold grevilleB1 grevilleB0 grevilleP1
  rw [mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [grevilleA]; try norm_num)

/-- Explicit matrix form of `grevilleB2`. -/
theorem grevilleB2_eq :
    grevilleB2 = !![(0 : ℚ), -2, 0; 0, 0, 0; 0, 0, 0] := by
  unfold grevilleB2 grevilleP2
  rw [zero_smul, sub_zero, grevilleB1_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA]; try norm_num)

/-- The first Souriau--Frame scalar is the trace readout. -/
theorem greville_trace_p1 :
    Matrix.trace (grevilleA * grevilleB0) = grevilleP1 := by
  simp [Matrix.trace, Fin.sum_univ_three, grevilleA, grevilleB0, grevilleP1]

/-- The second Souriau--Frame scalar is zero in this packet. -/
theorem greville_trace_p2 :
    (1 / 2 : ℚ) * Matrix.trace (grevilleA * grevilleB1) = grevilleP2 := by
  rw [grevilleB1_eq]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    grevilleA, grevilleP2]

/-- The third Souriau--Frame scalar is zero in this packet. -/
theorem greville_trace_p3 :
    (1 / 3 : ℚ) * Matrix.trace (grevilleA * grevilleB2) = grevilleP3 := by
  rw [grevilleB2_eq]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    grevilleA, grevilleP3]

/-- The packet has `B₃ = 0`. -/
theorem greville_B3_eq_zero :
    grevilleB3 = 0 := by
  unfold grevilleB3 grevilleP3
  rw [zero_smul, sub_zero, grevilleB2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA]; try norm_num)

/-- The packet has `B₂ ≠ 0`, so the first zero is not earlier than `3`. -/
theorem greville_B2_ne_zero :
    grevilleB2 ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Mat3 ℚ => M 0 1) (grevilleB2_eq.symm.trans h)
  norm_num at h01

/-- Explicit square of `grevilleA`. -/
theorem grevilleA_sq_eq :
    grevilleA ^ 2 = !![0, 0, 0; 0, 0, 0; 0, 0, (4 : ℚ)] := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA]; try norm_num)

/-- Explicit cube of `grevilleA`. -/
theorem grevilleA_cube_eq :
    grevilleA ^ 3 = !![0, 0, 0; 0, 0, 0; 0, 0, (8 : ℚ)] := by
  rw [pow_succ, grevilleA_sq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA]; try norm_num)

/-- The characteristic-polynomial relation in the packet: `A³ = 2 A²`. -/
theorem greville_A_cube_eq_two_smul_A_sq :
    grevilleA ^ 3 = (2 : ℚ) • (grevilleA ^ 2) := by
  rw [grevilleA_cube_eq, grevilleA_sq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

/-- Greville's formula with `s = 1`, `k = 2`, `B₀ = I`, and `p₁ = 2`. -/
def grevilleFormulaCandidate : Mat3 ℚ :=
  ((grevilleP1) ^ 3)⁻¹ • (grevilleA ^ 2 * grevilleB0 ^ 3)

/-- Expected Drazin inverse: zero on the nilpotent block and `1/2` on the regular lane. -/
def grevilleExpectedDrazin : Mat3 ℚ :=
  !![0, 0, 0;
     0, 0, 0;
     0, 0, 1 / 2]

/-- Greville's formula produces the expected Drazin inverse. -/
theorem greville_formula_candidate_eq_expected :
    grevilleFormulaCandidate = grevilleExpectedDrazin := by
  unfold grevilleFormulaCandidate grevilleB0 grevilleP1
  rw [one_pow, mul_one, grevilleA_sq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [grevilleExpectedDrazin]; try norm_num)

/-- Greville's formula satisfies the Drazin laws at index `2`. -/
theorem greville_formula_candidate_isDrazinInverse :
    Drazin.IsDrazinInverse grevilleA grevilleFormulaCandidate 2 := by
  rw [greville_formula_candidate_eq_expected]
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA, grevilleExpectedDrazin]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA, grevilleExpectedDrazin]; try norm_num)
  · rw [grevilleA_cube_eq, grevilleA_sq_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleExpectedDrazin]; try norm_num)

/-- The regular Drazin projector selected by Greville's formula. -/
theorem greville_regular_projector_readout :
    Drazin.IsDrazinInverse.projection grevilleA grevilleFormulaCandidate =
      !![0, 0, 0;
         0, 0, 0;
         0, 0, 1] := by
  unfold Drazin.IsDrazinInverse.projection
  rw [greville_formula_candidate_eq_expected]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, grevilleA, grevilleExpectedDrazin]; try norm_num)

/-- The nilpotent zero-root projector selected by Greville's formula. -/
theorem greville_nilpotent_projector_readout :
    Drazin.IsDrazinInverse.complementaryProjection grevilleA grevilleFormulaCandidate =
      !![1, 0, 0;
         0, 1, 0;
         0, 0, 0] := by
  unfold Drazin.IsDrazinInverse.complementaryProjection
  rw [greville_regular_projector_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

/-! ## Strict finite `GL₃(Q)` conjugation readout -/

/-- A permutation matrix used as a concrete `GL₃(Q)` representative. -/
def grevillePermutation : Mat3 ℚ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The permutation representative is its own inverse. -/
theorem grevillePermutation_sq_eq_one :
    grevillePermutation * grevillePermutation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, grevillePermutation]; try norm_num)

/-- The permutation as a strict unit of the matrix algebra. -/
def grevillePermutationUnit : (Mat3 ℚ)ˣ where
  val := grevillePermutation
  inv := grevillePermutation
  val_inv := grevillePermutation_sq_eq_one
  inv_val := grevillePermutation_sq_eq_one

/-- Unit conjugation on the matrix algebra. -/
def unitConj (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) : Mat3 ℚ :=
  (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)

/-- Unit conjugation is a ring equivalence on `Mat3 ℚ`. -/
def unitConjRingEquiv (u : (Mat3 ℚ)ˣ) : Mat3 ℚ ≃+* Mat3 ℚ where
  toFun := unitConj u
  invFun := unitConj u⁻¹
  left_inv A := by
    simp [unitConj, mul_assoc]
  right_inv A := by
    simp [unitConj, mul_assoc]
  map_mul' A B := by
    dsimp [unitConj]
    calc
      (u : Mat3 ℚ) * (A * B) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)
          = (u : Mat3 ℚ) * A * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * B *
              ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by simp [mul_assoc]
      _ = ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) *
            ((u : Mat3 ℚ) * B * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) := by simp [mul_assoc]
  map_add' A B := by
    dsimp [unitConj]
    noncomm_ring

/-- The conjugated Greville candidate is the Drazin inverse of the conjugated matrix. -/
theorem greville_conjugated_formula_isDrazinInverse :
    Drazin.IsDrazinInverse
      (unitConj grevillePermutationUnit grevilleA)
      (unitConj grevillePermutationUnit grevilleFormulaCandidate)
      2 :=
  Drazin.IsDrazinInverse.map_ringEquiv
    (unitConjRingEquiv grevillePermutationUnit)
    greville_formula_candidate_isDrazinInverse

/-! ## Section 2: Greville's General Ring-Level Souriau--Frame Drazin Theorem (1973) -/

section GeneralGrevilleSouriauFrame

variable {R : Type*} [Ring R]

/-- Greville-shaped Drazin candidate `a ^ k * (b_prev * inv_ps) ^ (k + 1)`; an alias of
`polynomialDrazinCandidate a (b_prev * inv_ps) k`.  It matches Greville's formula when
`b_prev = B_{s-1}` and `inv_ps` is the central scalar `p_s⁻¹`. -/
def grevilleSouriauFrameCandidate (a b_prev inv_ps : R) (k : ℕ) : R :=
  polynomialDrazinCandidate a (b_prev * inv_ps) k

/-- Over any associative ring `R`, if `a` commutes with `b_prev` and `inv_ps` and the
index-`k` factorization hypothesis `a ^ (k + 1) * (b_prev * inv_ps) = a ^ k` holds, then
`grevilleSouriauFrameCandidate a b_prev inv_ps k` is an index-`k` Drazin inverse of `a`.
This is the polynomial construction specialised to `p := b_prev * inv_ps`; deriving the
hypothesis from the Souriau--Frame recurrence is not formalized. -/
theorem isDrazinInverse_grevilleSouriauFrameCandidate
    (a b_prev inv_ps : R) (k : ℕ)
    (hcomm_b : a * b_prev = b_prev * a)
    (hcomm_ps : a * inv_ps = inv_ps * a)
    (hrec : a ^ (k + 1) * (b_prev * inv_ps) = a ^ k) :
    Drazin.IsDrazinInverse a (grevilleSouriauFrameCandidate a b_prev inv_ps k) k := by
  have hc_b : Commute a b_prev := hcomm_b
  have hc_ps : Commute a inv_ps := hcomm_ps
  exact isDrazinInverse_polynomialDrazinCandidate a (b_prev * inv_ps) k
    (hc_b.mul_right hc_ps).eq hrec

/-- The regular Drazin projector `a * X` of Greville's Souriau--Frame candidate equals
`a ^ k * (b_prev * inv_ps) ^ k`. -/
theorem grevilleSouriauFrameCandidate_projection_eq
    (a b_prev inv_ps : R) (k : ℕ)
    (hrec : a ^ (k + 1) * (b_prev * inv_ps) = a ^ k) :
    Drazin.IsDrazinInverse.projection a (grevilleSouriauFrameCandidate a b_prev inv_ps k) =
      a ^ k * (b_prev * inv_ps) ^ k :=
  polynomialDrazinCandidate_projection_eq a (b_prev * inv_ps) k hrec

end GeneralGrevilleSouriauFrame

end InfoGeometry.Canonical.GrevilleSouriauFrameDrazin
