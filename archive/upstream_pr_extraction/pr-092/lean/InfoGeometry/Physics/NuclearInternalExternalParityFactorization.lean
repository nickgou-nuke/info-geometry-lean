import Mathlib
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev

/-!
# Internal versus external parity for operator-valued Soloviev blocks

The operator super-Soloviev lane contains two independent `ℤ₂` involutions.
They must not be conflated:

* `internalParity = diag(Γ,Γ)` applies the internal grading to every block.
  For even diagonal coefficients and odd transition coefficients it produces
  the genuine Soloviev reflection `V,W ↦ -V,-W`.
* `externalFockParity = diag(1,-1)` changes only the two-sector Fock sign and
  therefore reflects every off-diagonal block independently of its internal
  grade.
* `totalParity = diag(Γ,-Γ)` is their product.  Hence on internally odd
  transition channels the two sign changes cancel and the full
  super-Hamiltonian is invariant.

All statements are identities over an arbitrary associative ring.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearInternalExternalParityFactorization

open Matrix
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev

variable {A : Type*} [Ring A]

/-- Pure internal grading on the two-sector carrier: `diag(Γ,Γ)`. -/
def internalParity (P : InternalParity A) : Block2 A :=
  !![P.gamma, 0; 0, P.gamma]

/-- Pure outer/Fock grading: `diag(1,-1)`. -/
def externalFockParity : Block2 A :=
  !![(1 : A), 0; 0, -1]

/-- Internal parity is an involution. -/
theorem internalParity_sq (P : InternalParity A) :
    internalParity P * internalParity P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, Matrix.mul_apply, Fin.sum_univ_two, P.gamma_sq]

/-- External Fock parity is an involution. -/
theorem externalFockParity_sq :
    (externalFockParity : Block2 A) * externalFockParity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [externalFockParity, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pure internal conjugation applies `P.act` independently to all four blocks. -/
theorem internalParity_conjugation_formula
    (P : InternalParity A) (E0 E1 V W : A) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
      blockHamiltonian (P.act E0) (P.act E1) (P.act V) (P.act W) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, blockHamiltonian, InternalParity.act,
      Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- Pure internal grading gives the Soloviev reflection when the diagonal
coefficients are internally even and the transition channels are internally
odd. -/
theorem internalParity_reflection_of_even_diagonal_odd_offDiagonal
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
      reflectOffDiagonal E0 E1 V W := by
  rw [internalParity_conjugation_formula]
  unfold InternalParity.IsEven InternalParity.IsOdd at hE0 hE1 hV hW
  rw [hE0, hE1, hV, hW]
  rfl

/-- Pure external/Fock parity always reflects the off-diagonal channels. -/
theorem externalFockParity_reflection
    (E0 E1 V W : A) :
    externalFockParity * blockHamiltonian E0 E1 V W * externalFockParity =
      reflectOffDiagonal E0 E1 V W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [externalFockParity, blockHamiltonian, reflectOffDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- Internal and external parity commute. -/
theorem internalParity_mul_externalFockParity
    (P : InternalParity A) :
    internalParity P * externalFockParity = totalParity P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, externalFockParity, totalParity,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The opposite multiplication order gives the same total parity. -/
theorem externalFockParity_mul_internalParity
    (P : InternalParity A) :
    externalFockParity * internalParity P = totalParity P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, externalFockParity, totalParity,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact factorization of the total grading into commuting internal and outer
Fock involutions. -/
theorem parity_factorization_packet (P : InternalParity A) :
    internalParity P * externalFockParity = totalParity P ∧
      externalFockParity * internalParity P = totalParity P ∧
      internalParity P * externalFockParity =
        externalFockParity * internalParity P :=
  ⟨internalParity_mul_externalFockParity P,
    externalFockParity_mul_internalParity P,
    (internalParity_mul_externalFockParity P).trans
      (externalFockParity_mul_internalParity P).symm⟩

/-- On an internally odd transition channel the internal reflection and outer
Fock reflection cancel in the product grading, giving total super-invariance. -/
theorem totalParity_invariance_from_double_reflection
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
      blockHamiltonian E0 E1 V W := by
  exact invariant_of_even_diagonal_odd_offDiagonal P E0 E1 V W
    hE0 hE1 hV hW

/-- Consolidated distinction between the three parity actions. -/
theorem internal_external_total_parity_packet
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
        reflectOffDiagonal E0 E1 V W ∧
      externalFockParity * blockHamiltonian E0 E1 V W * externalFockParity =
        reflectOffDiagonal E0 E1 V W ∧
      totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
        blockHamiltonian E0 E1 V W :=
  ⟨internalParity_reflection_of_even_diagonal_odd_offDiagonal
      P E0 E1 V W hE0 hE1 hV hW,
    externalFockParity_reflection E0 E1 V W,
    totalParity_invariance_from_double_reflection
      P E0 E1 V W hE0 hE1 hV hW⟩

end InfoGeometry.Physics.NuclearInternalExternalParityFactorization

end noncomputable section
