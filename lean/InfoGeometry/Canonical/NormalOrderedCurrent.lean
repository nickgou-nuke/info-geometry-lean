import Mathlib.Data.Matrix.Basis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Normal-Ordered Matrix Units

This file deliberately does not introduce raw CAR mode records, assumed
current laws, or theorem sockets.

The owner theorem here is the canonical finite matrix-unit calculation supported
directly by mathlib's `Matrix.single` API:

* matrix units obey the ordinary `gl` commutator;
* subtracting diagonal scalar multiples of the identity does not change the
  commutator;
* rewriting the ordinary commutator in the normal-ordered basis produces the
  finite Wick correction term.

This is not the completed current theorem
`[J_m, J_n] = m δ_{m+n,0} K`.  That theorem still requires a genuine
mode-indexed Fock completion and normal ordering construction.
-/

namespace InfoGeometry.Canonical.NormalOrderedCurrent

open scoped BigOperators

section CanonicalMatrixUnits

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Ordinary associative commutator in the square matrix algebra. -/
def algebraCommutator (X Y : Matrix ι ι R) : Matrix ι ι R :=
  X * Y - Y * X

/-- Canonical matrix unit `E_ab`. -/
def matrixUnit (a b : ι) : Matrix ι ι R :=
  Matrix.single a b (1 : R)

/-- Integer occupation coefficient attached to a diagonal matrix unit. -/
def diagonalVacuumScalar (occ : ι → ℤ) (a b : ι) : ℤ :=
  if a = b then occ a else 0

/-- Normal-ordered finite matrix unit: subtract the occupied diagonal scalar. -/
def normalOrderedMatrixUnit (occ : ι → ℤ) (a b : ι) : Matrix ι ι R :=
  matrixUnit (R := R) a b - diagonalVacuumScalar occ a b • (1 : Matrix ι ι R)

/-- Multiplication law for canonical matrix units. -/
@[simp]
theorem matrixUnit_mul (a b c d : ι) :
    matrixUnit (R := R) a b * matrixUnit (R := R) c d =
      if b = c then matrixUnit (R := R) a d else 0 := by
  by_cases hbc : b = c
  · subst c
    simp [matrixUnit]
  · rw [if_neg hbc]
    change Matrix.single a b (1 : R) * Matrix.single c d (1 : R) = 0
    exact Matrix.single_mul_single_of_ne (c := (1 : R)) a b c hbc (1 : R)

/-- Canonical matrix units obey the ordinary `gl` commutator. -/
theorem matrixUnit_commutator (a b c d : ι) :
    algebraCommutator (matrixUnit (R := R) a b) (matrixUnit (R := R) c d) =
      (if b = c then matrixUnit (R := R) a d else 0)
        - (if a = d then matrixUnit (R := R) c b else 0) := by
  unfold algebraCommutator
  rw [matrixUnit_mul, matrixUnit_mul]
  by_cases had : a = d <;> simp [had, eq_comm]

/--
Subtracting integer scalar multiples of the identity from both inputs leaves
the matrix commutator unchanged.
-/
theorem algebraCommutator_sub_zsmul_one_sub_zsmul_one
    (X Y : Matrix ι ι R) (m n : ℤ) :
    algebraCommutator (X - m • (1 : Matrix ι ι R)) (Y - n • (1 : Matrix ι ι R)) =
      algebraCommutator X Y := by
  unfold algebraCommutator
  simp only [zsmul_one]
  noncomm_ring [Int.cast_comm m X, Int.cast_comm m Y, Int.cast_comm n X, Int.cast_comm n Y,
    Int.cast_comm m (n : Matrix ι ι R)]

/-- The finite normal-ordering/Wick correction term in the matrix-unit basis. -/
def wickCorrection (occ : ι → ℤ) (a b c d : ι) : Matrix ι ι R :=
  if b = c ∧ a = d then (occ a - occ c) • (1 : Matrix ι ι R) else 0

/--
Canonical owner theorem: finite normal-ordered matrix units obey the
Wick-corrected matrix-unit commutator.

This is a theorem about mathlib matrix units.  It does not assume CAR modes and
does not construct infinite currents.
-/
theorem normalOrdered_matrixUnit_commutator (occ : ι → ℤ) (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) occ a b)
        (normalOrderedMatrixUnit (R := R) occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) occ c b else 0)
        + wickCorrection (R := R) occ a b c d := by
  calc
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) occ a b)
        (normalOrderedMatrixUnit (R := R) occ c d)
        =
      algebraCommutator (matrixUnit (R := R) a b) (matrixUnit (R := R) c d) := by
        rw [normalOrderedMatrixUnit, normalOrderedMatrixUnit]
        exact algebraCommutator_sub_zsmul_one_sub_zsmul_one
          (matrixUnit (R := R) a b) (matrixUnit (R := R) c d)
          (diagonalVacuumScalar occ a b) (diagonalVacuumScalar occ c d)
    _ =
      (if b = c then normalOrderedMatrixUnit (R := R) occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) occ c b else 0)
        + wickCorrection (R := R) occ a b c d := by
        rw [matrixUnit_commutator]
        by_cases hbc : b = c
        · subst c
          by_cases had : a = d
          · subst d
            simp [normalOrderedMatrixUnit, diagonalVacuumScalar, wickCorrection]
            abel
          · simp [normalOrderedMatrixUnit, diagonalVacuumScalar, wickCorrection, had]
        · by_cases had : a = d
          · subst d
            have hcb : c ≠ b := fun h => hbc h.symm
            simp [normalOrderedMatrixUnit, diagonalVacuumScalar, wickCorrection, hbc, hcb]
          · simp [wickCorrection, hbc, had]

/-- Symmetric integer cutoff window `{-N, ..., N}` for later current sums. -/
def integerWindow (N : ℕ) : Finset ℤ :=
  (Finset.range (2 * N + 1)).image fun k : ℕ => (k : ℤ) - (N : ℤ)

end CanonicalMatrixUnits

end InfoGeometry.Canonical.NormalOrderedCurrent
