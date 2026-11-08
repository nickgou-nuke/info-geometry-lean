import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerPullback
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman

/-!
# Ordered pullback combinations and the associative Jordan triple identity

The triple identity is universal in an associative ring. No claim of a
five-graded Kantor Lie algebra follows merely from this identity.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B]

/-- Fundamental identity for the associative Jordan triple product. -/
theorem jordanTriple_fundamental (a b x y z : B) :
    jordanTriple a b (jordanTriple x y z) =
      jordanTriple (jordanTriple a b x) y z -
      jordanTriple x (jordanTriple b a y) z +
      jordanTriple x y (jordanTriple a b z) := by
  simp only [jordanTriple, mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  abel

variable {P : B} (hP : P * P = P) (A C : B)
include hP

theorem two_cone_pullback_sum :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) +
      ((1 + coneMinus P C) * (1 - conePlus P A)) *
        comm P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      (2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C := by
  peirce_nf hP

theorem two_cone_pullback_difference :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) -
      ((1 + coneMinus P C) * (1 - conePlus P A)) *
        comm P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      (2 : ℤ) • genSig P A C - genV P A C * genJ P A C := by
  peirce_nf hP

theorem jordanTriple_j_self :
    jordanTriple (genJ P A C) (genJ P A C) (genJ P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) := by
  unfold jordanTriple
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
