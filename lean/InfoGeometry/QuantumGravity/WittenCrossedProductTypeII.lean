/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Section 112: Finite Matrix-Trace Identities

This module formalizes identities for a four-entry matrix-coordinate record over
an arbitrary commutative ring. It does not define a crossed product, a von
Neumann algebra, a Type II factor, a renormalized semifinite trace, a unitary
evolution, or Bekenstein–Hawking/Witten generalized entropy. Those operator-
algebraic and physical claims remain open closure debt. The proved content is
restricted to finite matrix multiplication, trace identities, and scalar
readouts of explicitly constructed entries.
-/

namespace InfoGeometry.QuantumGravity.WittenCrossedProduct

variable {R : Type*} [CommRing R]

/-! ### 1. Four-Entry Matrix Coordinate Carrier -/

/-- Four-entry matrix-coordinate record over a commutative ring. -/
@[ext]
structure MatrixCoord2 (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R
  deriving DecidableEq, Repr, Inhabited

namespace MatrixCoord2

variable {R : Type*} [CommRing R]

def zeroOp : MatrixCoord2 R := ⟨0, 0, 0, 0⟩

def oneOp : MatrixCoord2 R := ⟨1, 0, 0, 1⟩

def sampleMatrixCoord2Int : MatrixCoord2 ℤ := ⟨3, 1, 0, 2⟩

theorem sampleMatrixCoord2Int_ne_zero :
    sampleMatrixCoord2Int ≠ zeroOp := by
  decide

def add (A B : MatrixCoord2 R) : MatrixCoord2 R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

def sub (A B : MatrixCoord2 R) : MatrixCoord2 R :=
  ⟨A.m11 - B.m11, A.m12 - B.m12, A.m21 - B.m21, A.m22 - B.m22⟩

def mul (A B : MatrixCoord2 R) : MatrixCoord2 R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21,
   A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21,
   A.m21 * B.m12 + A.m22 * B.m22⟩

def trace (A : MatrixCoord2 R) : R :=
  A.m11 + A.m22

/-- Non-commutativity of `MatrixCoord2.mul` over `ℤ`. -/
theorem matrixCoord2_mul_noncommutative :
    let A : MatrixCoord2 ℤ := ⟨1, 1, 0, 1⟩
    let B : MatrixCoord2 ℤ := ⟨1, 0, 1, 1⟩
    mul A B ≠ mul B A := by
  decide

/-- Cyclic invariance of the ordinary matrix trace: `Tr(A · B) = Tr(B · A)`. -/
theorem trace_mul_comm (A B : MatrixCoord2 R) :
    trace (mul A B) = trace (mul B A) := by
  dsimp [trace, mul]
  ring

/-- Additive linearity of the ordinary matrix trace: `Tr(A + B) = Tr(A) + Tr(B)`. -/
theorem trace_add (A B : MatrixCoord2 R) :
    trace (add A B) = trace A + trace B := by
  dsimp [trace, add]
  ring

end MatrixCoord2

/-! ### 2. Finite Matrix Hamiltonian Data -/

/-- Four scalar coordinates used to construct a finite matrix readout. This is
not a crossed-product algebra or operator-algebraic Hamiltonian. -/
@[ext]
structure MatrixHamiltonianData (R : Type*) [CommRing R] where
  H_grav   : R
  K_mod    : R
  offDiag1 : R
  offDiag2 : R
  deriving DecidableEq, Repr, Inhabited

def zeroMatrixHamiltonianData : MatrixHamiltonianData R := ⟨0, 0, 0, 0⟩

def sampleMatrixHamiltonianDataInt : MatrixHamiltonianData ℤ := ⟨10, 5, 1, -1⟩

theorem sampleMatrixHamiltonianDataInt_ne_zero :
    sampleMatrixHamiltonianDataInt ≠ zeroMatrixHamiltonianData := by
  decide

/-- Matrix record with `H_grav` in the upper-left and the supplied off-diagonal entries. -/
def gravOp (W : MatrixHamiltonianData R) : MatrixCoord2 R :=
  ⟨W.H_grav, W.offDiag1, W.offDiag2, 0⟩

/-- Matrix record with `K_mod` in the lower-right and the negated off-diagonal entries. -/
def modOp (W : MatrixHamiltonianData R) : MatrixCoord2 R :=
  ⟨0, -W.offDiag1, -W.offDiag2, W.K_mod⟩

/-- Entrywise matrix sum of the two constructed records. -/
def totalOp (W : MatrixHamiltonianData R) : MatrixCoord2 R :=
  MatrixCoord2.add (gravOp W) (modOp W)

/-! ### 3. Finite Matrix-Trace Readout -/

/-- Ordinary matrix trace of the finite coordinate record. -/
def matrixTrace (X : MatrixCoord2 R) : R :=
  MatrixCoord2.trace X

/-- Trace readout of the explicitly constructed finite matrix `totalOp W`. -/
def finiteTraceReadout (W : MatrixHamiltonianData R) : R :=
  matrixTrace (totalOp W)

/-! ### 4. Finite Matrix Identity -/

/-- The trace of this constructed matrix is the sum of its two diagonal parameters. -/
theorem finiteTraceReadout_eq_parameter_sum (W : MatrixHamiltonianData R) :
    finiteTraceReadout W = W.H_grav + W.K_mod := by
  dsimp [finiteTraceReadout, matrixTrace, totalOp, gravOp, modOp,
         MatrixCoord2.add, MatrixCoord2.trace]
  ring


end InfoGeometry.QuantumGravity.WittenCrossedProduct
