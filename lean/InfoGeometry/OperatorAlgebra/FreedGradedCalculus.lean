/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Algebra.SupermatrixKoszul
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Noncommutative graded block calculus

The coefficient algebra is an arbitrary ring. The diagonal difference is
coefficient-valued and is not assumed cyclic. Its graded cyclicity defects
are explicit commutators; a cyclic additive functional annihilates them.

The square and cubic identities below are algebraic identities. They do not
construct a Fredholm family, an analytic index, a differential superconnection,
or a Chern--Weil class. See `docs/FREED_GRADED_OPERATOR_CONTRACT.md`.
-/

namespace InfoGeometry.OperatorAlgebra.FreedGradedCalculus

open Matrix
open InfoGeometry.Algebra.SupermatrixKoszul
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments

variable {R : Type*} [Ring R]

/-- The coefficient-valued diagonal difference, packaged as an additive map. -/
def superTrace : Matrix (Fin 2) (Fin 2) R →+ R where
  toFun M := M 0 0 - M 1 1
  map_zero' := by simp
  map_add' M N := by simp; abel

@[simp] theorem superTrace_evenBlock (a d : R) :
    superTrace (evenBlock a d) = a - d := rfl

@[simp] theorem superTrace_oddBlock (b c : R) :
    superTrace (oddBlock b c) = 0 := by simp [superTrace]

/-- This is the ordinary matrix trace weighted by the parity matrix. -/
theorem superTrace_eq_trace_parity (M : Matrix (Fin 2) (Fin 2) R) :
    superTrace M = Matrix.trace (parityBlock * M) := by
  change M 0 0 - M 1 1 = ∑ i : Fin 2, ((parityBlock : Matrix (Fin 2) (Fin 2) R) * M) i i
  simp only [Fin.sum_univ_two, Matrix.mul_apply]
  simp [parityBlock, sub_eq_add_neg]

/-- Equal additive changes to both diagonal entries cancel exactly. -/
theorem superTrace_paired_shift (a d delta : R) :
    superTrace (evenBlock (a + delta) (d + delta)) = superTrace (evenBlock a d) := by
  simp only [superTrace_evenBlock]
  abel

/-- The ungraded trace retains twice the common additive change. -/
theorem trace_paired_shift (a d delta : R) :
    Matrix.trace (evenBlock (a + delta) (d + delta)) =
      Matrix.trace (evenBlock a d) + (delta + delta) := by
  simp [Matrix.trace, Fin.sum_univ_two]
  abel

/-- The exact obstruction to coefficient-valued graded cyclicity. -/
theorem superTrace_odd_anticommutator (b c e f : R) :
    superTrace (anticomm (oddBlock b c) (oddBlock e f)) = PeirceSpine.comm b f + PeirceSpine.comm e c := by
  simp only [anticomm, oddBlock_mul_oddBlock, map_add, superTrace_evenBlock, PeirceSpine.comm]
  abel

/-- Even graded commutators retain the two coefficient commutators. -/
theorem superTrace_even_commutator (a d e f : R) :
    superTrace (PeirceSpine.comm (evenBlock a d) (evenBlock e f)) = PeirceSpine.comm a e - PeirceSpine.comm d f := by
  simp only [PeirceSpine.comm, evenBlock_mul_evenBlock, map_sub, superTrace_evenBlock]
  abel

theorem superTrace_even_odd_commutator (a d b c : R) :
    superTrace (PeirceSpine.comm (evenBlock a d) (oddBlock b c)) = 0 := by
  simp [PeirceSpine.comm, evenBlock_mul_oddBlock, oddBlock_mul_evenBlock]

/-- Universal vanishing of even these elementary odd anticommutators would
force the coefficient ring to be commutative. -/
theorem superTrace_elementary_odd_vanish_iff :
    (∀ a b : R, superTrace (anticomm (oddBlock a 0) (oddBlock 0 b)) = 0) ↔
      ∀ a b : R, a * b = b * a := by
  simp [superTrace_odd_anticommutator, PeirceSpine.comm, sub_eq_zero]

section CyclicFunctional

variable {G : Type*} [AddCommGroup G] (tau : R →+ G)
variable (hcyc : ∀ a b : R, tau (a * b) = tau (b * a))
include hcyc

/-- A cyclic additive functional supplies the missing graded cyclicity. -/
theorem cyclic_superTrace_odd_anticommutator (b c e f : R) :
    tau (superTrace (anticomm (oddBlock b c) (oddBlock e f))) = 0 := by
  rw [superTrace_odd_anticommutator]
  simp only [PeirceSpine.comm, map_add, map_sub]
  rw [hcyc b f, hcyc e c]
  simp

theorem cyclic_superTrace_even_commutator (a d e f : R) :
    tau (superTrace (PeirceSpine.comm (evenBlock a d) (evenBlock e f))) = 0 := by
  rw [superTrace_even_commutator]
  simp only [PeirceSpine.comm, map_sub]
  rw [hcyc a e, hcyc d f]
  simp

end CyclicFunctional

/-- Powers of a diagonal block preserve the order internal to each entry. -/
theorem evenBlock_pow (a d : R) (n : ℕ) :
    evenBlock a d ^ n = evenBlock (a ^ n) (d ^ n) := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [evenBlock]
  | succ n ih => rw [pow_succ, ih, evenBlock_mul_evenBlock, pow_succ, pow_succ]

/-- Positive even powers of an odd block have zero cyclic supertrace.
The proof reuses the existing cyclic product-moment theorem. -/
theorem cyclic_superTrace_odd_even_power {G : Type*} [AddCommGroup G]
    (tau : R →+ G) (hcyc : ∀ a b : R, tau (a * b) = tau (b * a))
    (b c : R) (k : ℕ) :
    tau (superTrace (oddBlock b c ^ (2 * (k + 1)))) = 0 := by
  rw [pow_mul, pow_two, oddBlock_mul_oddBlock, evenBlock_pow,
    superTrace_evenBlock, map_sub,
    cyclic_product_positive_power tau hcyc b c k, sub_self]

/-- Standard matrix coordinates for the existing Peirce even projection. -/
theorem evenGrade_standard (M : Matrix (Fin 2) (Fin 2) R) :
    evenGrade (evenBlock 1 0) M = evenBlock (M 0 0) (M 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [evenGrade, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [evenBlock]

/-- Standard matrix coordinates for the existing Peirce odd projection. -/
theorem oddGrade_standard (M : Matrix (Fin 2) (Fin 2) R) :
    oddGrade (evenBlock 1 0) M = oddBlock (M 0 1) (M 1 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [oddGrade, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [evenBlock, oddBlock]

theorem superTrace_oddGrade (M : Matrix (Fin 2) (Fin 2) R) :
    superTrace (oddGrade (evenBlock 1 0) M) = 0 := by
  rw [oddGrade_standard, superTrace_oddBlock]

/-- Ordered even/odd decomposition of the square of a block operator. -/
theorem block_square (a d b c : R) :
    (evenBlock a d + oddBlock b c) ^ 2 =
      evenBlock (a * a + b * c) (d * d + c * b) +
        oddBlock (a * b + b * d) (c * a + d * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, evenBlock, oddBlock, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem block_square_even (a d b c : R) :
    evenGrade (evenBlock 1 0) ((evenBlock a d + oddBlock b c) ^ 2) =
      evenBlock (a * a + b * c) (d * d + c * b) := by
  rw [evenGrade_standard, block_square]
  simp

theorem block_square_odd (a d b c : R) :
    oddGrade (evenBlock 1 0) ((evenBlock a d + oddBlock b c) ^ 2) =
      anticomm (evenBlock a d) (oddBlock b c) := by
  rw [oddGrade_standard, block_square]
  simp only [Matrix.add_apply, evenBlock_apply01, oddBlock_apply01,
    evenBlock_apply10, oddBlock_apply10, zero_add, anticomm,
    evenBlock_mul_oddBlock, oddBlock_mul_evenBlock]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddBlock, add_comm]

section UniversalRingIdentities

variable {B : Type*} [Ring B]

/-- Associativity implies that every element commutes with its square. -/
theorem comm_square_zero (X : B) : PeirceSpine.comm X (X * X) = 0 := by
  simp [PeirceSpine.comm, mul_assoc]

/-- The quadratic polynomial used by the submitted algebraic identity. -/
def curvaturePolynomial (Phi D : B) : B := Phi + D * D

/-- An ordered cubic polynomial; no differential or characteristic class is
implicit in this definition. -/
def cubicMixedPolynomial (Phi D : B) : B := Phi * D + D * Phi + D * D * D

/-- Exact universal cubic/quartic identity over any associative ring.
The nested commutator records the noncommutative remainder explicitly. -/
theorem cubic_curvature_identity (Phi D : B) :
    anticomm D (cubicMixedPolynomial Phi D) - PeirceSpine.comm (PeirceSpine.comm D Phi) D +
      2 * (Phi * Phi) = 2 * (curvaturePolynomial Phi D * curvaturePolynomial Phi D) := by
  unfold anticomm PeirceSpine.comm cubicMixedPolynomial curvaturePolynomial
  noncomm_ring

/-- Under an actual commutation hypothesis the remainder vanishes. -/
theorem cubic_curvature_identity_of_commute (Phi D : B) (h : Commute D Phi) :
    anticomm D (cubicMixedPolynomial Phi D) + 2 * (Phi * Phi) =
      2 * (curvaturePolynomial Phi D * curvaturePolynomial Phi D) := by
  have hz : PeirceSpine.comm D Phi = 0 := sub_eq_zero.mpr h.eq
  have hid := cubic_curvature_identity Phi D
  rw [hz] at hid
  simpa only [PeirceSpine.comm, zero_mul, mul_zero, sub_self, sub_zero] using hid

end UniversalRingIdentities
end InfoGeometry.OperatorAlgebra.FreedGradedCalculus
