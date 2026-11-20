/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint
import InfoGeometry.OperatorAlgebra.InnerConjugation
import InfoGeometry.Quantum.SylvesterWeylBraidBridge
import InfoGeometry.Algebra.LieCyclotomicBridge
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A full real matrix witness for a cubic twisted differential

The carrier is the full algebra of three-by-three matrices of two-by-two real
blocks. The internal third-root phase is noncentral in this algebra. Existing
clock and shift matrices construct its actual conjugation automorphism.
The twisted differential is a native real-linear endomorphism whose cube is
zero and whose square is nonzero on a displayed matrix unit.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness

open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
open InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint
open InfoGeometry.Algebra.IsotropicCyclotomicGalois
open InfoGeometry.Algebra.LieCyclotomicBridge

abbrev RealCubicOperator :=
  Matrix (ZMod 3) (ZMod 3) (Matrix (Fin 2) (Fin 2) ℝ)

/-- An internal phase, using the existing real companion matrix. -/
def phase : RealCubicOperator := Matrix.scalar (ZMod 3) thirdRoot

/-- The existing cyclic shift, with actual real operator blocks as coefficients. -/
def charge : RealCubicOperator := SylvesterWeylBraid.shiftMatrix 3

/-- The existing clock evaluated at the internal real third root. -/
def clock : RealCubicOperator := SylvesterWeylBraid.clockMatrix 3 thirdRoot

theorem clock_eq_diagonal :
    clock = Matrix.diagonal (fun i : ZMod 3 => thirdRoot ^ i.val) := rfl

theorem clock_cube : clock ^ 3 = 1 := by
  rw [clock_eq_diagonal, Matrix.diagonal_pow]
  have h : (fun i : ZMod 3 => thirdRoot ^ i.val) ^ 3 = 1 := by
    funext i
    change (thirdRoot ^ i.val) ^ 3 = 1
    rw [← pow_mul, Nat.mul_comm i.val 3, pow_mul, thirdRoot_pow_three, one_pow]
  rw [h, Matrix.diagonal_one']

theorem clock_mul_square : clock * clock ^ 2 = 1 := by
  simpa only [pow_succ', pow_zero, mul_one] using clock_cube

theorem clock_square_mul : clock ^ 2 * clock = 1 := by
  simpa only [pow_succ, pow_zero, one_mul] using clock_cube

/-- Multiplication by the actual shift translates the row index. -/
theorem charge_mul_apply (x : RealCubicOperator) (i j : ZMod 3) :
    (charge * x) i j = x (i - 1) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - 1)]
  · simp [charge, SylvesterWeylBraid.shiftMatrix]
  · intro k _ hk
    have hne : i ≠ k + 1 := by
      intro h
      apply hk
      exact (eq_sub_iff_add_eq).2 h.symm
    simp [charge, SylvesterWeylBraid.shiftMatrix, hne]
  · intro h
    exact (h (Finset.mem_univ (i - 1))).elim

/-- Right multiplication translates the column index and preserves block order. -/
theorem mul_charge_apply (x : RealCubicOperator) (i j : ZMod 3) :
    (x * charge) i j = x i (j + 1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
  · simp [charge, SylvesterWeylBraid.shiftMatrix]
  · intro k _ hk
    simp [charge, SylvesterWeylBraid.shiftMatrix, hk]
  · intro h
    exact (h (Finset.mem_univ (j + 1))).elim

theorem charge_cube : charge ^ 3 = 1 := by
  have hindices : ∀ i j : ZMod 3, (i - 1 - 1 = j + 1 ↔ i = j) := by decide
  rw [pow_succ, pow_two, Matrix.mul_assoc]
  apply Matrix.ext
  intro i j
  simp only [charge_mul_apply]
  simp only [charge, SylvesterWeylBraid.shiftMatrix, Matrix.of_apply, Matrix.one_apply]
  simp only [hindices i j]

theorem phase_cyclotomic : cyclo3 phase = 0 := by
  have h : thirdRoot * thirdRoot + thirdRoot + 1 = 0 := by
    simpa only [Polynomial.cyclotomic_three, map_add, map_mul, map_pow,
      Polynomial.aeval_X, map_one, pow_two] using thirdRoot_aeval
  change Matrix.scalar (ZMod 3) thirdRoot * Matrix.scalar (ZMod 3) thirdRoot +
    Matrix.scalar (ZMod 3) thirdRoot + 1 = 0
  simpa only [map_add, map_mul, map_one, map_zero] using
    congrArg (Matrix.scalar (ZMod 3)) h

theorem phase_commutes_charge : Commute phase charge := by
  change phase * charge = charge * phase
  ext i j
  simp only [phase, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    charge, SylvesterWeylBraid.shiftMatrix, Matrix.of_apply]
  split_ifs <;> simp

theorem phase_commutes_clock : Commute phase clock := by
  change phase * clock = clock * phase
  rw [phase, Matrix.scalar_apply, clock_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact ((Commute.refl thirdRoot).pow_right i.val).eq

def clockUnit : RealCubicOperatorˣ where
  val := clock
  inv := clock ^ 2
  val_inv := clock_mul_square
  inv_val := clock_square_mul

/-- Actual clock conjugation, promoted to a real algebra equivalence. -/
def clockAutomorphism : RealCubicOperator ≃ₐ[ℝ] RealCubicOperator :=
  AlgEquiv.ofRingEquiv (f := innerConjugationRingEquiv clockUnit) (by
    intro r
    change clock * algebraMap ℝ RealCubicOperator r * clock ^ 2 =
      algebraMap ℝ RealCubicOperator r
    rw [← Algebra.commutes r clock, mul_assoc, clock_mul_square, mul_one])

@[simp] theorem clockAutomorphism_apply (x : RealCubicOperator) :
    clockAutomorphism x = clock * x * clock ^ 2 := rfl

/-- Clock conjugation acts on each real block by an ordered left and right phase. -/
theorem clockAutomorphism_apply_entry (x : RealCubicOperator) (i j : ZMod 3) :
    clockAutomorphism x i j =
      thirdRoot ^ i.val * x i j * (thirdRoot ^ j.val) ^ 2 := by
  simp only [clockAutomorphism_apply, clock_eq_diagonal, Matrix.diagonal_pow,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.pow_apply]

theorem clockAutomorphism_cube (x : RealCubicOperator) :
    clockAutomorphism (clockAutomorphism (clockAutomorphism x)) = x := by
  have hinv : (clock ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, clock_cube, one_pow]
  calc
    clockAutomorphism (clockAutomorphism (clockAutomorphism x)) =
        clock ^ 3 * x * (clock ^ 2) ^ 3 := by
          simp only [clockAutomorphism_apply]
          noncomm_ring
    _ = x := by rw [clock_cube, hinv, one_mul, mul_one]

theorem clockAutomorphism_phase : clockAutomorphism phase = phase := by
  rw [clockAutomorphism_apply, phase_commutes_clock.eq.symm, mul_assoc,
    clock_mul_square, mul_one]

/-- The charge covariance comes from the actual Sylvester Weyl relation. -/
theorem clockAutomorphism_charge : clockAutomorphism charge = phase * charge := by
  have h := SylvesterWeylBraid.sylvester_weyl_braid_relation
    3 thirdRoot thirdRoot_pow_three
  change clock * charge = thirdRoot • (charge * clock) at h
  rw [Matrix.smul_eq_diagonal_mul] at h
  change clock * charge = phase * (charge * clock) at h
  rw [clockAutomorphism_apply, h]
  calc
    phase * (charge * clock) * clock ^ 2 =
        phase * (charge * (clock * clock ^ 2)) := by noncomm_ring
    _ = phase * charge := by rw [clock_mul_square, mul_one]

/-- The actual existing adjoint, as a real-linear operator on the full matrix algebra. -/
def differential : Module.End ℝ RealCubicOperator :=
  gradedAdjoint clockAutomorphism charge

@[simp] theorem differential_apply (x : RealCubicOperator) :
    differential x = charge * x - clockAutomorphism x * charge := rfl

/-- The same native differential evaluated at an actual block entry. -/
theorem differential_entry (x : RealCubicOperator) (i j : ZMod 3) :
    differential x i j = x (i - 1) j -
      thirdRoot ^ i.val * x i (j + 1) * (thirdRoot ^ (j + 1).val) ^ 2 := by
  rw [differential_apply, Matrix.sub_apply, charge_mul_apply,
    mul_charge_apply, clockAutomorphism_apply_entry]

theorem differential_cube_zero : differential ^ 3 = 0 := by
  apply LinearMap.ext
  intro x
  change ringGradedAdjoint clockAutomorphism.toRingEquiv charge
    (ringGradedAdjoint clockAutomorphism.toRingEquiv charge
      (ringGradedAdjoint clockAutomorphism.toRingEquiv charge x)) = 0
  rw [ringGradedAdjoint_cube_eq_inner_apply clockAutomorphism.toRingEquiv
    charge phase clockAutomorphism_charge clockAutomorphism_phase
    phase_commutes_charge phase_cyclotomic clockAutomorphism_cube,
    charge_cube, one_mul, mul_one, sub_self]

/-- The first diagonal matrix unit, with identity real block. -/
def testMatrix : RealCubicOperator := Matrix.single 0 0 1

/-- This entry of the second iterate is one, so the cubic nilpotency is exact. -/
theorem differential_square_test_entry :
    ((differential ^ 2) testMatrix) 2 0 0 0 = (1 : ℝ) := by
  change (differential (differential testMatrix)) 2 0 0 0 = 1
  simp only [differential_entry]
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  norm_num [testMatrix, Matrix.single_apply, Matrix.sub_apply, Matrix.one_apply, h02]

theorem differential_square_ne_zero : differential ^ 2 ≠ 0 := by
  intro h
  have hx := congrArg
    (fun T : Module.End ℝ RealCubicOperator => T testMatrix 2 0 0 0) h
  change ((differential ^ 2) testMatrix) 2 0 0 0 = 0 at hx
  rw [differential_square_test_entry] at hx
  exact one_ne_zero hx

/-- A real block matrix that fails to commute with the internal phase. -/
def phaseProbe : RealCubicOperator :=
  Matrix.single 0 0 !![(1 : ℝ), 0; 0, 0]

theorem phase_noncentral : phase * phaseProbe ≠ phaseProbe * phase := by
  intro h
  have hx := congrArg (fun M : RealCubicOperator => M 0 0 1 0) h
  simp only [phase, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    phaseProbe, Matrix.single_apply] at hx
  norm_num [thirdRoot, Matrix.mul_apply, Fin.sum_univ_two] at hx

end InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness
