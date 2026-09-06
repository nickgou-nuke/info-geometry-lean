import Mathlib.Data.Matrix.Block

/-!
# The associative quadrant corner

The four quadrant operators are the matrix units of `M₂(R)` tensored with an
identity block.  This owner deliberately does not claim a Clifford `Cl(5,5)`
representation: that requires five creation and five contraction operators on
an exterior-algebra spinor module.
-/

namespace InfoGeometry.Algebra.ColeFury

variable {R : Type*} [Ring R] {n : ℕ}

abbrev QuadrantMatrix := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R
abbrev BlockMatrix := Matrix (Fin n) (Fin n) R

def upperLeft : QuadrantMatrix (R := R) (n := n) :=
  Matrix.fromBlocks (1 : BlockMatrix (R := R) (n := n)) 0 0 0

def lowerRight : QuadrantMatrix (R := R) (n := n) :=
  Matrix.fromBlocks 0 0 0 (1 : BlockMatrix (R := R) (n := n))

def horizonUp : QuadrantMatrix (R := R) (n := n) :=
  Matrix.fromBlocks 0 (1 : BlockMatrix (R := R) (n := n)) 0 0

def horizonDown : QuadrantMatrix (R := R) (n := n) :=
  Matrix.fromBlocks 0 0 (1 : BlockMatrix (R := R) (n := n)) 0

private theorem fromBlocks_mul
    (A B C D E F G H : BlockMatrix (R := R) (n := n)) :
    Matrix.fromBlocks A B C D * Matrix.fromBlocks E F G H =
      Matrix.fromBlocks (A * E + B * G) (A * F + B * H)
        (C * E + D * G) (C * F + D * H) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply]

@[simp] theorem upperLeft_sq :
    upperLeft * upperLeft = (upperLeft : QuadrantMatrix (R := R) (n := n)) := by
  simp only [upperLeft, fromBlocks_mul]
  simp

@[simp] theorem lowerRight_sq :
    lowerRight * lowerRight = (lowerRight : QuadrantMatrix (R := R) (n := n)) := by
  simp only [lowerRight, fromBlocks_mul]
  simp

@[simp] theorem horizonUp_sq :
    horizonUp * horizonUp = (0 : QuadrantMatrix (R := R) (n := n)) := by
  simp only [horizonUp, fromBlocks_mul]
  simp

@[simp] theorem horizonDown_sq :
    horizonDown * horizonDown = (0 : QuadrantMatrix (R := R) (n := n)) := by
  simp only [horizonDown, fromBlocks_mul]
  simp

@[simp] theorem horizonUp_mul_horizonDown :
    horizonUp * horizonDown = (upperLeft : QuadrantMatrix (R := R) (n := n)) := by
  simp only [horizonUp, horizonDown, fromBlocks_mul, upperLeft]
  simp

@[simp] theorem horizonDown_mul_horizonUp :
    horizonDown * horizonUp = (lowerRight : QuadrantMatrix (R := R) (n := n)) := by
  simp only [horizonDown, horizonUp, fromBlocks_mul, lowerRight]
  simp

theorem quadrant_identity_decomposition :
    (upperLeft : QuadrantMatrix (R := R) (n := n)) + lowerRight = 1 := by
  ext i j
  cases i <;> cases j <;> simp [upperLeft, lowerRight, Matrix.one_apply]

theorem quadrant_commutator :
    (((horizonDown : QuadrantMatrix (R := R) (n := n)) *
          (horizonUp : QuadrantMatrix (R := R) (n := n)) -
        (horizonUp : QuadrantMatrix (R := R) (n := n)) *
          (horizonDown : QuadrantMatrix (R := R) (n := n))) :
      QuadrantMatrix (R := R) (n := n)) =
      ((lowerRight : QuadrantMatrix (R := R) (n := n)) -
        (upperLeft : QuadrantMatrix (R := R) (n := n))) := by
  rw [horizonDown_mul_horizonUp, horizonUp_mul_horizonDown]

end InfoGeometry.Algebra.ColeFury
