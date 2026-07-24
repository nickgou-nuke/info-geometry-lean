import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Concrete finite supermatrix parity laws

Finite `1|1` supermatrix parity is represented directly by `2 × 2` matrices.
Even matrices are diagonal and odd matrices are off-diagonal.  The proved
content is the finite block multiplication table:

* even times even is even;
* even times odd is odd;
* odd times even is odd;
* odd times odd is even.
-/

namespace InfoGeometry.Algebra.SupermatrixKoszul

open Matrix

/-- Concrete even `1|1` block matrix. -/
def evenBlock {R : Type*} [Zero R] (a d : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, 0; 0, d]

/-- Concrete odd `1|1` block matrix. -/
def oddBlock {R : Type*} [Zero R] (b c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, b; c, 0]

/-- The concrete `1|1` parity operator: `+1` on the even line, `-1` on the odd line. -/
def parityBlock {R : Type*} [Zero R] [One R] [Neg R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

@[simp] theorem evenBlock_apply00 {R : Type*} [Zero R] (a d : R) :
    evenBlock a d 0 0 = a := by
  rfl

@[simp] theorem evenBlock_apply01 {R : Type*} [Zero R] (a d : R) :
    evenBlock a d 0 1 = 0 := by
  rfl

@[simp] theorem evenBlock_apply10 {R : Type*} [Zero R] (a d : R) :
    evenBlock a d 1 0 = 0 := by
  rfl

@[simp] theorem evenBlock_apply11 {R : Type*} [Zero R] (a d : R) :
    evenBlock a d 1 1 = d := by
  rfl

@[simp] theorem oddBlock_apply00 {R : Type*} [Zero R] (b c : R) :
    oddBlock b c 0 0 = 0 := by
  rfl

@[simp] theorem oddBlock_apply01 {R : Type*} [Zero R] (b c : R) :
    oddBlock b c 0 1 = b := by
  rfl

@[simp] theorem oddBlock_apply10 {R : Type*} [Zero R] (b c : R) :
    oddBlock b c 1 0 = c := by
  rfl

@[simp] theorem oddBlock_apply11 {R : Type*} [Zero R] (b c : R) :
    oddBlock b c 1 1 = 0 := by
  rfl

/-- Even block matrices are closed under matrix multiplication. -/
theorem evenBlock_mul_evenBlock
    {R : Type*} [CommSemiring R] (a d e f : R) :
    evenBlock a d * evenBlock e f = evenBlock (a * e) (d * f) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [evenBlock, Matrix.mul_apply]
    · simp [evenBlock, Matrix.mul_apply]
  · fin_cases j
    · simp [evenBlock, Matrix.mul_apply]
    · simp [evenBlock, Matrix.mul_apply]

/-- Even times odd is odd. -/
theorem evenBlock_mul_oddBlock
    {R : Type*} [CommSemiring R] (a d b c : R) :
    evenBlock a d * oddBlock b c = oddBlock (a * b) (d * c) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
  · fin_cases j
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
    · simp [evenBlock, oddBlock, Matrix.mul_apply]

/-- Odd times even is odd. -/
theorem oddBlock_mul_evenBlock
    {R : Type*} [CommSemiring R] (b c a d : R) :
    oddBlock b c * evenBlock a d = oddBlock (b * d) (c * a) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
  · fin_cases j
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
    · simp [evenBlock, oddBlock, Matrix.mul_apply]

/-- Odd block matrices multiply to an even block matrix. -/
theorem oddBlock_mul_oddBlock
    {R : Type*} [CommSemiring R] (b c e f : R) :
    oddBlock b c * oddBlock e f = evenBlock (b * f) (c * e) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
  · fin_cases j
    · simp [evenBlock, oddBlock, Matrix.mul_apply]
    · simp [evenBlock, oddBlock, Matrix.mul_apply]

/-- The concrete Koszul sign on the odd-odd channel. -/
theorem oddOdd_koszul_neg_square
    {R : Type*} [Ring R] (x : R) :
    -((-x) * x) = x * x := by
  noncomm_ring

/-! ## Parity conjugation -/

/-- Conjugation by the finite parity operator fixes even `1|1` matrices. -/
theorem parityBlock_mul_evenBlock_mul_parityBlock
    {R : Type*} [CommRing R] (a d : R) :
    parityBlock * evenBlock a d * parityBlock = evenBlock a d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityBlock, evenBlock, Matrix.mul_apply]

/-- Conjugation by the finite parity operator negates odd `1|1` matrices. -/
theorem parityBlock_mul_oddBlock_mul_parityBlock
    {R : Type*} [CommRing R] (b c : R) :
    parityBlock * oddBlock b c * parityBlock = -oddBlock b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityBlock, oddBlock, Matrix.mul_apply]

end InfoGeometry.Algebra.SupermatrixKoszul
