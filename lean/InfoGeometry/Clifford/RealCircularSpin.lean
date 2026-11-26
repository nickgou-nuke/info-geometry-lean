/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GullDoranPseudoscalarBridge
import InfoGeometry.Clifford.Cl11KleinTwist

/-!
# Circular spin operators on the native real Pauli carrier

The Pauli matrices are the existing `GullDoranPseudoscalarBridge.realSigma*`.
The internal phase is the negative of that owner's `realPhaseAxis`; this fixes
the orientation of the quaternion triple and of the two circular ladders.
All new scalars and carriers are real. No physical helicity classification is
asserted: the ladder commutators give weights for the specified grading axis.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealCircularSpin

open GullDoranPseudoscalarBridge
open scoped Matrix

/-- The three existing real Pauli matrices, indexed from zero. -/
def sigma (a : Fin 3) : Mat4R := ![realSigma1, realSigma2, realSigma3] a

/-- Internal phase with the orientation used by the circular spin ladders. -/
def fiberPhase : Mat4R := -realPhaseAxis

/-- Real quaternion generators, with positive cyclic orientation. -/
def quaternionAxis (a : Fin 3) : Mat4R := fiberPhase * sigma a

/-- The normalized real spin generators. -/
def rotation (a : Fin 3) : Mat4R := (1 / 2 : ℝ) • quaternionAxis a

/-- Upper circular spin ladder, retaining the internal real phase. -/
def circularPlus : Mat4R := rotation 0 - fiberPhase * rotation 1

/-- Lower circular spin ladder, retaining the internal real phase. -/
def circularMinus : Mat4R := rotation 0 + fiberPhase * rotation 1

/-- Positive longitudinal projector. -/
def polePlus : Mat4R := (1 / 2 : ℝ) • (1 + sigma 2)

/-- Negative longitudinal projector. -/
def poleMinus : Mat4R := (1 / 2 : ℝ) • (1 - sigma 2)

/-- Real Pauli soldering, expressed in the native matrix basis. -/
def solder (t x y z : ℝ) : Mat4R :=
  t • 1 + x • sigma 0 + y • sigma 1 + z • sigma 2

/-- Spatially reversed soldering. This is not the Hilbert adjoint. -/
def solderConjugate (t x y z : ℝ) : Mat4R := solder t (-x) (-y) (-z)

local macro "spin_entrywise" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [sigma, fiberPhase, quaternionAxis, rotation, circularPlus,
      circularMinus, polePlus, poleMinus, solder, solderConjugate,
      realSigma1, realSigma2, realSigma3, realPhaseAxis,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one] <;> ring))

theorem sigma_square (a : Fin 3) : sigma a * sigma a = 1 := by
  fin_cases a
  · exact realSigma1_sq
  · exact realSigma2_sq
  · exact realSigma3_sq

theorem sigma_transpose (a : Fin 3) : (sigma a)ᵀ = sigma a := by
  fin_cases a <;> spin_entrywise

theorem fiberPhase_square : fiberPhase * fiberPhase = -1 := by
  simpa [fiberPhase] using realPhaseAxis_sq

theorem fiberPhase_transpose : fiberPhaseᵀ = -fiberPhase := by
  spin_entrywise

theorem fiberPhase_commutes_sigma (a : Fin 3) :
    fiberPhase * sigma a = sigma a * fiberPhase := by
  fin_cases a <;> spin_entrywise

theorem quaternionAxis_square (a : Fin 3) :
    quaternionAxis a * quaternionAxis a = -1 := by
  fin_cases a <;> spin_entrywise

theorem quaternionAxis_cyclic (a : Fin 3) :
    quaternionAxis a * quaternionAxis (a + 1) = quaternionAxis (a + 2) := by
  fin_cases a <;> spin_entrywise

theorem quaternionAxis_volume :
    quaternionAxis 0 * quaternionAxis 1 * quaternionAxis 2 = -1 := by
  rw [show quaternionAxis 0 * quaternionAxis 1 = quaternionAxis 2 from
    quaternionAxis_cyclic 0, quaternionAxis_square]

theorem twice_rotation (a : Fin 3) :
    (2 : ℝ) • rotation a = quaternionAxis a := by
  simp [rotation, smul_smul]

theorem rotation_square (a : Fin 3) :
    rotation a * rotation a = (-1 / 4 : ℝ) • (1 : Mat4R) := by
  fin_cases a <;> spin_entrywise

theorem rotation_transpose (a : Fin 3) : (rotation a)ᵀ = -rotation a := by
  fin_cases a <;> spin_entrywise

theorem rotation_commutator_cyclic (a : Fin 3) :
    rotation a * rotation (a + 1) - rotation (a + 1) * rotation a =
      rotation (a + 2) := by
  fin_cases a <;> spin_entrywise

theorem rotation_sigma_commutator_cyclic (a : Fin 3) :
    rotation a * sigma (a + 1) - sigma (a + 1) * rotation a = sigma (a + 2) := by
  fin_cases a <;> spin_entrywise

theorem sigma_commutator_cyclic (a : Fin 3) :
    sigma a * sigma (a + 1) - sigma (a + 1) * sigma a =
      (-4 : ℝ) • rotation (a + 2) := by
  fin_cases a <;> spin_entrywise

theorem circularPlus_square : circularPlus * circularPlus = 0 := by
  spin_entrywise

theorem circularMinus_square : circularMinus * circularMinus = 0 := by
  spin_entrywise

theorem circularPlus_ne_zero : circularPlus ≠ 0 := by
  intro h
  have h03 := congrArg (fun M : Mat4R => M 0 3) h
  norm_num [circularPlus, rotation, quaternionAxis, fiberPhase, sigma,
    realSigma1, realSigma2, realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four] at h03

theorem circularMinus_ne_zero : circularMinus ≠ 0 := by
  intro h
  have h21 := congrArg (fun M : Mat4R => M 2 1) h
  norm_num [circularMinus, rotation, quaternionAxis, fiberPhase, sigma,
    realSigma1, realSigma2, realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four] at h21

/-- Adjoint weight for `sigma 2`; this is not a physical helicity theorem. -/
theorem circularPlus_grading_commutator :
    sigma 2 * circularPlus - circularPlus * sigma 2 = (2 : ℝ) • circularPlus := by
  spin_entrywise

theorem circularMinus_grading_commutator :
    sigma 2 * circularMinus - circularMinus * sigma 2 = (-2 : ℝ) • circularMinus := by
  spin_entrywise

theorem circularPlus_mul_minus : circularPlus * circularMinus = -polePlus := by
  spin_entrywise

theorem circularMinus_mul_plus : circularMinus * circularPlus = -poleMinus := by
  spin_entrywise

theorem polePlus_add_poleMinus : polePlus + poleMinus = 1 := by
  spin_entrywise

theorem polePlus_square : polePlus * polePlus = polePlus := by
  spin_entrywise

theorem poleMinus_square : poleMinus * poleMinus = poleMinus := by
  spin_entrywise

theorem polePlus_mul_poleMinus : polePlus * poleMinus = 0 := by
  spin_entrywise

theorem poleMinus_mul_polePlus : poleMinus * polePlus = 0 := by
  spin_entrywise

/-- The negative lower ladder has the positive one-mode CAR normalization. -/
theorem signed_circular_anticommutator :
    circularPlus * (-circularMinus) + (-circularMinus) * circularPlus = 1 := by
  rw [mul_neg, neg_mul, circularPlus_mul_minus, circularMinus_mul_plus,
    neg_neg, neg_neg, polePlus_add_poleMinus]

theorem solder_coordinates (t x y z : ℝ) :
    solder t x y z =
      !![t + z, 0, x, y; 0, t + z, -y, x;
         x, -y, t - z, 0; y, x, 0, t - z] := by
  spin_entrywise

theorem solder_transpose (t x y z : ℝ) : (solder t x y z)ᵀ = solder t x y z := by
  spin_entrywise

theorem solder_mul_conjugate (t x y z : ℝ) :
    solder t x y z * solderConjugate t x y z =
      (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) • (1 : Mat4R) := by
  spin_entrywise

theorem solderConjugate_mul_solder (t x y z : ℝ) :
    solderConjugate t x y z * solder t x y z =
      (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) • (1 : Mat4R) := by
  spin_entrywise

/-- A genuine real algebra representation of the split atom. The lower
matrix unit maps to the *negative* circular ladder. -/
def circularRepresentation : Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] Mat4R where
  toFun A := A 0 0 • polePlus + A 0 1 • circularPlus -
    A 1 0 • circularMinus + A 1 1 • poleMinus
  map_one' := by spin_entrywise
  map_mul' A B := by spin_entrywise
  map_zero' := by spin_entrywise
  map_add' A B := by spin_entrywise
  commutes' r := by spin_entrywise

theorem circularRepresentation_coordinates (A : Matrix (Fin 2) (Fin 2) ℝ) :
    circularRepresentation A =
      !![A 0 0, 0, 0, A 0 1; 0, A 0 0, -(A 0 1), 0;
         0, -(A 1 0), A 1 1, 0; A 1 0, 0, 0, A 1 1] := by
  change A 0 0 • polePlus + A 0 1 • circularPlus -
    A 1 0 • circularMinus + A 1 1 • poleMinus = _
  spin_entrywise

theorem circularRepresentation_injective : Function.Injective circularRepresentation := by
  intro A B h
  rw [circularRepresentation_coordinates, circularRepresentation_coordinates] at h
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M : Mat4R => M 0 0) h
  · exact congrArg (fun M : Mat4R => M 0 3) h
  · exact congrArg (fun M : Mat4R => M 3 0) h
  · exact congrArg (fun M : Mat4R => M 2 2) h

theorem circularRepresentation_upperLadder :
    circularRepresentation (SplitAtomDoubling.upperLadder (A := ℝ)) = circularPlus := by
  change _ • polePlus + _ • circularPlus - _ • circularMinus + _ • poleMinus = _
  simp [SplitAtomDoubling.upperLadder]

theorem circularRepresentation_lowerLadder :
    circularRepresentation (SplitAtomDoubling.lowerLadder (A := ℝ)) = -circularMinus := by
  change _ • polePlus + _ • circularPlus - _ • circularMinus + _ • poleMinus = _
  simp [SplitAtomDoubling.lowerLadder]

theorem circularRepresentation_upperCorner :
    circularRepresentation (SplitAtomDoubling.upperCorner (A := ℝ)) = polePlus := by
  change _ • polePlus + _ • circularPlus - _ • circularMinus + _ • poleMinus = _
  simp [SplitAtomDoubling.upperCorner]

theorem circularRepresentation_lowerCorner :
    circularRepresentation (SplitAtomDoubling.lowerCorner (A := ℝ)) = poleMinus := by
  change _ • polePlus + _ • circularPlus - _ • circularMinus + _ • poleMinus = _
  simp [SplitAtomDoubling.lowerCorner]

end InfoGeometry.Clifford.RealCircularSpin
