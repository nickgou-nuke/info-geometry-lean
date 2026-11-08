/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Concrete real Tetraktys carry on four states

This finite matrix owner connects the real two-dimensional Tetraktys complex structure
`J = [[0,1],[-1,0]]` to a four-state carry. It proves the polynomial laws
`ζ² = J₁`, `ζ⁴ = -I`, and `ζ⁸ = I` over `ℤ`, using no scalar complex numbers or square roots.
The result is a finite carrier calculation; it does not assert exact order eight in every ring,
nor does it construct a physical parafermion braid representation.

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `tetraktysJ_is_internal_complex_structure`: `tetraktysJ = !![0, 1; -1, 0]` and `tetraktysJ * tetraktysJ = -1`.
- `tetraktys_real_carry_power_laws`: `zetaCarry * zetaCarry = firstJ`, `(zetaCarry²)² = -one4`, and `((zetaCarry²)²)² = one4`.
- `tetraktys_real_z4_weyl_pair`: `clock4 ^ 4 = 1`, `shift4 ^ 4 = 1`, `phase4 ^ 2 = -1`, and `clock4 * shift4 = phase4 * shift4 * clock4`.

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- None (all declarations in this module are unconditional finite integer-matrix evaluations).

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`).
-/

namespace InfoGeometry.Parafermion.TetraktysRealCarryMatrix

open Matrix
open scoped Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine

abbrev State := Fin 4
abbrev Mat := Matrix State State ℤ

/-- Identity on the four two-bit states. -/
def one4 : Mat := !![
  1, 0, 0, 0;
  0, 1, 0, 0;
  0, 0, 1, 0;
  0, 0, 0, 1]

/-- Integer Peirce idempotent used for the one-bit Tetraktys complex structure. -/
def tetraktysProjector : Matrix (Fin 2) (Fin 2) ℤ := !![
  1, 0;
  0, 0]

/-- Upper Peirce matrix unit. -/
def tetraktysUpper : Matrix (Fin 2) (Fin 2) ℤ := !![
  0, 1;
  0, 0]

/-- Lower Peirce matrix unit. -/
def tetraktysLower : Matrix (Fin 2) (Fin 2) ℤ := !![
  0, 0;
  1, 0]

/-- The imported Peirce-spine `genJ` in the concrete integer two-state carrier. -/
def tetraktysJ : Matrix (Fin 2) (Fin 2) ℤ :=
  genJ tetraktysProjector tetraktysUpper tetraktysLower

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℤ`. -/
lemma tetraktysProjector_mul_tetraktysJ_ne_comm :
    tetraktysProjector * tetraktysJ ≠ tetraktysJ * tetraktysProjector := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  revert h01
  decide

/-- The endogenous Tetraktys bivector is the standard real matrix complex structure. -/
theorem tetraktysJ_is_internal_complex_structure :
    tetraktysJ = !![
      0, 1;
     -1, 0] ∧
    tetraktysJ * tetraktysJ = -!![
      1, 0;
      0, 1] := by
  have hJ : tetraktysJ = !![
      0, 1;
     -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  constructor
  · exact hJ
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- Second-bit Peirce projector, with basis order `00, 01, 10, 11`. -/
def secondProjector : Mat := !![
  1, 0, 0, 0;
  0, 0, 0, 0;
  0, 0, 1, 0;
  0, 0, 0, 0]

/-- Second-bit flip. -/
def secondFlip : Mat := !![
  0, 1, 0, 0;
  1, 0, 0, 0;
  0, 0, 0, 1;
  0, 0, 1, 0]

/-- First-bit lift of the imported integer Tetraktys bivector. The second bit is unchanged. -/
def firstJ : Mat := !![
  tetraktysJ 0 0, 0, tetraktysJ 0 1, 0;
  0, tetraktysJ 0 0, 0, tetraktysJ 0 1;
  tetraktysJ 1 0, 0, tetraktysJ 1 1, 0;
  0, tetraktysJ 1 0, 0, tetraktysJ 1 1]

/-- Carry phase built from the first-bit real complex structure and second-bit Peirce cut. -/
def zetaCarry : Mat :=
  secondProjector * secondFlip +
    (one4 - secondProjector) * firstJ * secondFlip

/-- Explicit non-commutativity witness for `Mat = Matrix State State ℤ`. -/
lemma secondProjector_mul_secondFlip_ne_comm :
    secondProjector * secondFlip ≠ secondFlip * secondProjector := by
  intro h
  have h01 := congrArg (fun M : Mat => M 0 1) h
  revert h01
  decide

/-- Exact finite integer-matrix laws for the Tetraktys-generated carry. -/
theorem tetraktys_real_carry_power_laws :
    secondProjector * secondProjector = secondProjector ∧
    secondFlip * secondFlip = one4 ∧
    firstJ * firstJ = -one4 ∧
    secondFlip * secondProjector =
      (one4 - secondProjector) * secondFlip ∧
    zetaCarry * zetaCarry = firstJ ∧
    (zetaCarry * zetaCarry) * (zetaCarry * zetaCarry) = -one4 ∧
    (((zetaCarry * zetaCarry) * (zetaCarry * zetaCarry)) *
      ((zetaCarry * zetaCarry) * (zetaCarry * zetaCarry))) = one4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    decide

/-!
## A real eight-coordinate `Z₄` Weyl pair

The coefficient ring below is itself the integer Tetraktys plane. Consequently this is an
`8 × 8` integer matrix representation (four states, each with two real coordinates), rather
than a `4 × 4` complex matrix representation.
-/

abbrev Plane := Matrix (Fin 2) (Fin 2) ℤ
abbrev WeylMat := Matrix (Fin 4) (Fin 4) Plane

/-- The integer Tetraktys complex structure used as the scalar phase block. -/
def planeJ : Plane := !![
  0, 1;
 -1, 0]

/-- The `Z₄` clock with eigenblocks `1, J, -1, -J`. -/
def clock4 : WeylMat := !![
  1,       0,       0,        0;
  0, planeJ,       0,        0;
  0,       0,      -1,        0;
  0,       0,       0, -planeJ]

/-- The cyclic four-state shift, with identity blocks on its nonzero entries. -/
def shift4 : WeylMat := !![
  0, 0, 0, 1;
  1, 0, 0, 0;
  0, 1, 0, 0;
  0, 0, 1, 0]

/-- The diagonal lift of the Tetraktys phase `J` to all four clock sectors. -/
def phase4 : WeylMat := !![
  planeJ,      0,      0,      0;
       0, planeJ,      0,      0;
       0,      0, planeJ,      0;
       0,      0,      0, planeJ]

/-- Explicit non-commutativity witness for `WeylMat = Matrix (Fin 4) (Fin 4) Plane`. -/
lemma clock4_mul_shift4_ne_comm :
    clock4 * shift4 ≠ shift4 * clock4 := by
  intro h
  have h10 := congrArg (fun M : WeylMat => M 1 0 0 1) h
  revert h10
  decide

/-- The real `Z₄` Weyl relations on four Tetraktys-complex states. -/
theorem tetraktys_real_z4_weyl_pair :
    clock4 ^ 4 = 1 ∧
    shift4 ^ 4 = 1 ∧
    phase4 ^ 2 = -1 ∧
    phase4 * clock4 = clock4 * phase4 ∧
    phase4 * shift4 = shift4 * phase4 ∧
    clock4 * shift4 = phase4 * shift4 * clock4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j r c <;> fin_cases i <;> fin_cases j <;>
    fin_cases r <;> fin_cases c <;>
    decide

end InfoGeometry.Parafermion.TetraktysRealCarryMatrix
