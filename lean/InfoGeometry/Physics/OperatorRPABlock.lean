/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization

/-!
# Operator RPA blocks and chiral parity

The signed RPA block is expressed through the existing operator-valued
`blockHamiltonian`. Its coefficients belong to an arbitrary associative ring.
The square retains the commutator of the two coefficients.

An unnormalised Hadamard intertwiner changes the block to an off-diagonal
chiral operator with independent ordered factors `a - b` and `a + b`. Its
square has the two ordered products on its diagonal. The intertwining
identities require neither coefficient commutation nor division by two.
-/

namespace InfoGeometry.Physics.OperatorRPABlock

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization

variable {A : Type*} [Ring A]

/-- The full signed RPA square retains both copies of the coefficient
commutator. -/
theorem rpa_square (a b : A) :
    blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) =
      blockHamiltonian (a * a - b * b) (a * a - b * b)
        (a * b - b * a) (a * b - b * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- The square loses its off-diagonal term exactly when the two coefficient
operators commute. -/
theorem rpa_square_offDiagonal_eq_zero_iff (a b : A) :
    (blockHamiltonian a (-a) b (-b) *
      blockHamiltonian a (-a) b (-b)) 0 1 = 0 ↔ a * b = b * a := by
  rw [rpa_square]
  simp [blockHamiltonian, sub_eq_zero]

/-- The unnormalised Hadamard block squares to twice the identity; an inverse
is not required for any result below. -/
theorem hadamard_square :
    blockHamiltonian (1 : A) (-1) 1 1 * blockHamiltonian 1 (-1) 1 1 =
      (2 : ℕ) • (1 : Block2 A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]

/-- The signed RPA block intertwines with a chiral off-diagonal operator.
The two factors keep their original multiplication order. -/
theorem hadamard_intertwines_rpa (a b : A) :
    blockHamiltonian 1 (-1) 1 1 * blockHamiltonian a (-a) b (-b) =
      blockHamiltonian 0 0 (a - b) (a + b) *
        blockHamiltonian 1 (-1) 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] <;>
    abel

/-- Multiplication on both sides gives twice the chiral block, with no
assumption that two is invertible. -/
theorem hadamard_rpa_hadamard (a b : A) :
    blockHamiltonian 1 (-1) 1 1 * blockHamiltonian a (-a) b (-b) *
        blockHamiltonian 1 (-1) 1 1 =
      (2 : ℕ) • blockHamiltonian 0 0 (a - b) (a + b) := by
  rw [hadamard_intertwines_rpa, mul_assoc, hadamard_square]
  simp only [two_nsmul, mul_add, mul_one]

/-- Before the change of block coordinates, exchanging the two sheets is
the chiral sign reversal of the signed RPA block. -/
theorem exchange_conjugation_rpa (a b : A) :
    blockHamiltonian 0 0 1 1 * blockHamiltonian a (-a) b (-b) *
        blockHamiltonian 0 0 1 1 =
      -blockHamiltonian a (-a) b (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

/-- The transformed RPA operator is odd under the existing external Fock
parity involution. -/
theorem chiral_rpa_parity (a b : A) :
    externalFockParity * blockHamiltonian 0 0 (a - b) (a + b) *
        externalFockParity =
      -blockHamiltonian 0 0 (a - b) (a + b) := by
  rw [externalFockParity_reflection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectOffDiagonal, blockHamiltonian]

/-- Squaring the chiral form produces two ordered operator products, one on
each sheet. They are not identified with one common scalar. -/
theorem chiral_rpa_square (a b : A) :
    blockHamiltonian 0 0 (a - b) (a + b) *
        blockHamiltonian 0 0 (a - b) (a + b) =
      blockHamiltonian ((a - b) * (a + b)) ((a + b) * (a - b)) 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two square sectors differ by the sign of the retained coefficient
commutator. -/
theorem ordered_rpa_products (a b : A) :
    (a - b) * (a + b) = a * a - b * b + (a * b - b * a) ∧
      (a + b) * (a - b) = a * a - b * b - (a * b - b * a) := by
  constructor <;> noncomm_ring

/-- The same Hadamard map intertwines the complete squared RPA operator
with the two ordered square sectors. -/
theorem hadamard_intertwines_rpa_square (a b : A) :
    blockHamiltonian 1 (-1) 1 1 *
        (blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b)) =
      blockHamiltonian ((a - b) * (a + b)) ((a + b) * (a - b)) 0 0 *
        blockHamiltonian 1 (-1) 1 1 := by
  calc
    _ = (blockHamiltonian 1 (-1) 1 1 *
          blockHamiltonian a (-a) b (-b)) *
          blockHamiltonian a (-a) b (-b) := (mul_assoc _ _ _).symm
    _ = (blockHamiltonian 0 0 (a - b) (a + b) *
          blockHamiltonian 1 (-1) 1 1) *
          blockHamiltonian a (-a) b (-b) := by
            rw [hadamard_intertwines_rpa]
    _ = blockHamiltonian 0 0 (a - b) (a + b) *
          (blockHamiltonian 1 (-1) 1 1 *
            blockHamiltonian a (-a) b (-b)) := mul_assoc _ _ _
    _ = blockHamiltonian 0 0 (a - b) (a + b) *
          (blockHamiltonian 0 0 (a - b) (a + b) *
            blockHamiltonian 1 (-1) 1 1) := by
              rw [hadamard_intertwines_rpa]
    _ = (blockHamiltonian 0 0 (a - b) (a + b) *
          blockHamiltonian 0 0 (a - b) (a + b)) *
          blockHamiltonian 1 (-1) 1 1 := (mul_assoc _ _ _).symm
    _ = _ := by rw [chiral_rpa_square]

/-- Chiral parity preserves the full ordered square even when its two
diagonal operators are different. -/
theorem chiral_rpa_square_parity (a b : A) :
    externalFockParity *
        (blockHamiltonian 0 0 (a - b) (a + b) *
          blockHamiltonian 0 0 (a - b) (a + b)) * externalFockParity =
      blockHamiltonian 0 0 (a - b) (a + b) *
        blockHamiltonian 0 0 (a - b) (a + b) := by
  simp only [chiral_rpa_square]
  rw [externalFockParity_reflection]
  simp only [reflectOffDiagonal, neg_zero]

end InfoGeometry.Physics.OperatorRPABlock
