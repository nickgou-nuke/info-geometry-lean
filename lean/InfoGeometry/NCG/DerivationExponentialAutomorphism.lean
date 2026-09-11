import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic
import InfoGeometry.NCG.NoncommutativeCyclicCocycle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.NCG

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

namespace CyclicAlgebraDerivation

variable (D : CyclicAlgebraDerivation R A)

/-- The Second-Order Derivation Operator: D²(x) = D(D(x)) -/
def D2 (x : A) : A := D (D x)

/-- 🏆 THEOREM 1: Second-Order Leibniz Product Rule:
    D²(x * y) = D²(x) * y + 2 • (D(x) * D(y)) + x * D²(y) -/
theorem leibniz_order_two (x y : A) :
    D.D2 (x * y) = D.D2 x * y + (2 : R) • (D x * D y) + x * D.D2 y := by
  dsimp [D2]
  rw [D.leibniz, D.map_add, D.leibniz, D.leibniz]
  have h_two : (2 : R) • (D x * D y) = D x * D y + D x * D y := by
    rw [two_smul]
  rw [h_two]
  abel

/-- First-order Taylor flow expansion map: U₁(t)(x) = x + t • D(x) -/
def flowOrderOne (t : R) (x : A) : A :=
  x + t • D x

/-- 🏆 THEOREM 2: First-Order Product Preservation (Automorphism to O(t²)):
    U₁(t)(x) * U₁(t)(y) = U₁(t)(x * y) + t² • (D(x) * D(y)) -/
theorem flowOrderOne_mul (t : R) (x y : A) :
    flowOrderOne D t x * flowOrderOne D t y =
      flowOrderOne D t (x * y) + (t * t) • (D x * D y) := by
  dsimp [flowOrderOne]
  rw [D.leibniz, smul_add]
  have h_expand :
    (x + t • D x) * (y + t • D y) =
      x * y + x * (t • D y) + (t • D x) * y + (t • D x) * (t • D y) := by
    simp only [add_mul, mul_add]
    abel
  have h_comm1 : x * (t • D y) = t • (x * D y) := by simp only [mul_smul_comm]
  have h_comm2 : (t • D x) * y = t • (D x * y) := by simp only [smul_mul_assoc]
  have h_comm3 : (t • D x) * (t • D y) = (t * t) • (D x * D y) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h_expand, h_comm1, h_comm2, h_comm3]
  abel

end CyclicAlgebraDerivation

end InfoGeometry.NCG
