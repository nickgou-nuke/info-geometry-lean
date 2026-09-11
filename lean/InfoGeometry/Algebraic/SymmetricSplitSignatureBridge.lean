import InfoGeometry.Algebraic.SplitQuadraticForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Symmetric split-signature registry

The external `geoalg` calculators expose several sign conventions for split
Cayley--Dickson bases.  The repo-native Clifford lane uses the convention
`Cl(n,n)`: equal positive and negative sectors.  This file records that
convention explicitly and connects it to the existing diagonal split form.
It does not identify an external basis ordering with a native Zorn basis.
-/

namespace InfoGeometry.Algebraic.SymmetricSplitSignature

open InfoGeometry.Algebraic.SplitSignature

abbrev SignatureCount := Nat × Nat

def symmetricSplit (n : ℕ) : SignatureCount := (n, n)

@[simp] theorem symmetricSplit_positive (n : ℕ) :
    (symmetricSplit n).1 = n := rfl

@[simp] theorem symmetricSplit_negative (n : ℕ) :
    (symmetricSplit n).2 = n := rfl

@[simp] theorem symmetricSplit_total (n : ℕ) :
    (symmetricSplit n).1 + (symmetricSplit n).2 = 2 * n := by
  simp [symmetricSplit, two_mul]

@[simp] theorem symmetricSplit_index (n : ℕ) :
    (symmetricSplit n).1 - (symmetricSplit n).2 = 0 := by
  simp [symmetricSplit]

def split44 : SignatureCount := symmetricSplit 4

def split55 : SignatureCount := symmetricSplit 5

@[simp] theorem split44_eq : split44 = (4, 4) := rfl

@[simp] theorem split55_eq : split55 = (5, 5) := rfl

theorem splitBasisVector_square_sign {n : ℕ} (i : SplitIndex n) :
    splitQuadraticForm n (splitBasisVector i) = splitWeight n i :=
  splitQuadraticForm_basisVector i

theorem split_signature_is_symmetric (n : ℕ) :
    (symmetricSplit n).1 = (symmetricSplit n).2 := rfl

end InfoGeometry.Algebraic.SymmetricSplitSignature
