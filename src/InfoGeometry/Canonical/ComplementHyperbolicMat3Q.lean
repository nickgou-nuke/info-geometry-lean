/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ComplementHyperbolicOrbit

/-! # A rational hyperbolic orbit with proper active support

The orbit is constructed by the native `ComplementHyperbolicOrbit` module.
The actual E01/E10 seeds act on the first two coordinates of the existing
rational matrix carrier. The third coordinate remains fixed by the rotor.
The moving idempotent is nontrivial and nonsymmetric; no metric or state is
asserted. All numerical certificates use exact rational arithmetic.
-/
namespace InfoGeometry.Canonical.ComplementHyperbolicMat3Q
open DeBruijnRotorAlternationCycle ComplementHyperbolicOrbit

abbrev Mat3Q := Matrix (Fin 3) (Fin 3) ℚ

/-- The actual upper matrix-unit seed. -/
def seedD : Mat3Q := Matrix.single 0 1 1

/-- The actual lower matrix-unit seed. -/
def seedB : Mat3Q := Matrix.single 1 0 1

/-- Primitive square-zero and reflexivity laws on the native matrix carrier. -/
theorem seed_pair : IsDualSeedPair seedD seedB := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [seedD, seedB, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]

/-- The initial plus pole is exactly E00. -/
theorem seed_plus_matrix :
    seedD*seedB = !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedD, seedB, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]

/-- The initial minus pole is exactly E11. -/
theorem seed_minus_matrix :
    seedB*seedD = !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedD, seedB, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]

/-- The actual rational matrix seeds do not commute. -/
theorem seed_noncommute : seedD*seedB ≠ seedB*seedD := by
  intro he
  have hx := congrArg (fun M : Mat3Q => M 0 0) he
  rw [seed_plus_matrix, seed_minus_matrix] at hx
  norm_num at hx

/-- The native active carrier has a nonzero inactive complement. -/
theorem seed_support_matrix :
    carrierSupport seedD seedB = !![1, 0, 0; 0, 1, 0; 0, 0, 0] := by
  unfold carrierSupport polePlus poleMinus
  rw [seed_plus_matrix, seed_minus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The third diagonal entry distinguishes the active carrier from full identity. -/
theorem seed_support_ne_one : carrierSupport seedD seedB ≠ (1 : Mat3Q) := by
  intro he
  have hx := congrArg (fun M : Mat3Q => M 2 2) he
  rw [seed_support_matrix] at hx
  norm_num [Matrix.one_apply] at hx

/-- The native complementary support is exactly the inactive corner E22. -/
theorem seed_complement_matrix :
    ReflexiveNilpotentFlows.complement seedD seedB =
      (Matrix.single 2 2 1 : Mat3Q) := by
  unfold ReflexiveNilpotentFlows.complement ReflexiveNilpotentFlows.support
  rw [seed_plus_matrix, seed_minus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply, Matrix.single_apply]

/-- Exact rational hyperbola normalization. -/
theorem rational_hyperbola :
    (5/3 : ℚ)*(5/3)-(4/3)*(4/3)=1 := by norm_num

/-- Unlike an integer solution of this hyperbola, the chosen boost is nonzero. -/
theorem rational_motion_ne_zero : (4/3 : ℚ) ≠ 0 := by norm_num

/-- Entry readback of the actual complement-preserving generic rotor. -/
theorem hyperbolicRotor_matrix :
    hyperbolicRotor (5/3 : ℚ) (4/3) seedD seedB =
      !![5/3, 4/3, 0; 4/3, 5/3, 0; 0, 0, 1] := by
  unfold hyperbolicRotor ReflexiveNilpotentFlows.complement ReflexiveNilpotentFlows.support
  rw [seed_plus_matrix, seed_minus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedD, seedB, Matrix.single_apply, Matrix.one_apply]

/-- Readback of the generic plus orbit, including the asymmetric cross-term signs. -/
theorem hyperbolicPlus_matrix :
    hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB =
      !![25/9, -20/9, 0; 20/9, -16/9, 0; 0, 0, 0] := by
  rw [hyperbolicPlus_expansion seed_pair, seed_plus_matrix, seed_minus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedD, seedB, Matrix.single_apply]

/-- Idempotence is an application of the generic orbit theorem to the proved pair. -/
theorem rational_orbit_idempotent :
    hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB *
      hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB =
        hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB :=
  hyperbolicPlus_idempotent seed_pair (5/3) (4/3) rational_hyperbola

/-- The orbit actually moves the initial pole. -/
theorem rational_orbit_ne_plus :
    hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB ≠ seedD*seedB := by
  intro he
  have hx := congrArg (fun M : Mat3Q => M 0 0) he
  rw [hyperbolicPlus_matrix, seed_plus_matrix] at hx
  norm_num at hx

/-- The moving idempotent is oblique: its transpose is different. -/
theorem rational_orbit_transpose_ne :
    (hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB).transpose ≠
      hyperbolicPlus (5/3 : ℚ) (4/3) seedD seedB := by
  intro he
  have hx := congrArg (fun M : Mat3Q => M 0 1) he
  rw [hyperbolicPlus_matrix] at hx
  norm_num [Matrix.transpose_apply] at hx

/-- The third basis vector is fixed by the actual rotor action. -/
theorem hyperbolicRotor_fixes_inactive_vector :
    Matrix.mulVec (hyperbolicRotor (5/3 : ℚ) (4/3) seedD seedB)
      ![0, 0, 1] = ![0, 0, 1] := by
  rw [hyperbolicRotor_matrix]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Left multiplication fixes the inactive matrix corner. -/
theorem hyperbolicRotor_fixes_inactive_corner_left :
    hyperbolicRotor (5/3 : ℚ) (4/3) seedD seedB *
      (Matrix.single 2 2 1 : Mat3Q) = Matrix.single 2 2 1 := by
  rw [hyperbolicRotor_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]

/-- Right multiplication fixes the same inactive corner. -/
theorem hyperbolicRotor_fixes_inactive_corner_right :
    (Matrix.single 2 2 1 : Mat3Q) *
      hyperbolicRotor (5/3 : ℚ) (4/3) seedD seedB = Matrix.single 2 2 1 := by
  rw [hyperbolicRotor_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]

end InfoGeometry.Canonical.ComplementHyperbolicMat3Q
