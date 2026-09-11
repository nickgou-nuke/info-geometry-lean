import InfoGeometry.Algebra.Zorn.CanonicalConjugation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical polynomial operators for the Zorn carrier

This owner defines the standard polynomial `V` operator from the actual
canonical Zorn multiplication and conjugation, and derives the corresponding
`K` operator by antisymmetrization.  It does not assume or assert the
structurable identity or either Kantor identity.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.CanonicalKantorOperators

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

/-- The concrete polynomial operator
`V_{x,y}(z) = (x * conj y) * z + (z * conj y) * x - (z * conj x) * y`. -/
def V (x y z : CZ) : CZ :=
  (x * canonicalConj y) * z +
    (z * canonicalConj y) * x -
      (z * canonicalConj x) * y

/-- The concrete `K` operator derived from `V`, with the argument convention
`K(x,y)z = V(x,z,y) - V(y,z,x)`. -/
def K (x y z : CZ) : CZ :=
  V x z y - V y z x

theorem V_add_right (x y z w : CZ) :
    V x y (z + w) = V x y z + V x y w := by
  unfold V
  simp only [mul_add, add_mul]
  abel

theorem V_smul_right (r : ℝ) (x y z : CZ) :
    V x y (r • z) = r • V x y z := by
  unfold V
  simp only [mul_smul, smul_mul]
  module

theorem V_add_middle (x y z w : CZ) :
    V x (y + z) w = V x y w + V x z w := by
  unfold V
  simp only [canonicalConj_add, mul_add, add_mul]
  abel

theorem V_smul_middle (r : ℝ) (x y z : CZ) :
    V x (r • y) z = r • V x y z := by
  unfold V
  simp only [canonicalConj_smul, mul_smul, smul_mul]
  module

theorem K_add_right (x y z w : CZ) :
    K x y (z + w) = K x y z + K x y w := by
  unfold K
  rw [V_add_middle, V_add_middle]
  abel

theorem K_smul_right (r : ℝ) (x y z : CZ) :
    K x y (r • z) = r • K x y z := by
  unfold K
  rw [V_smul_middle, V_smul_middle]
  module

@[simp] theorem K_self (x z : CZ) : K x x z = 0 := by
  simp [K]

theorem K_swap (x y z : CZ) : K y x z = -K x y z := by
  simp [K]

/-- Direct expansion of `K` into the native multiplication and conjugation.
This theorem fixes the argument convention for downstream coordinate checks. -/
theorem K_explicit (x y z : CZ) :
    K x y z =
      ((x * canonicalConj z) * y + (y * canonicalConj z) * x -
          (y * canonicalConj x) * z) -
        ((y * canonicalConj z) * x + (x * canonicalConj z) * y -
          (x * canonicalConj y) * z) := by
  rfl

end InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
