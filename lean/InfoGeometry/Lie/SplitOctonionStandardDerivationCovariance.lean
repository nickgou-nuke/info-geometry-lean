import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Covariance of the standard alternative-algebra derivation

The standard derivation `D_{a,b}` is built from left and right
multiplications.  Its commutator with an arbitrary derivation is therefore
again a standard derivation, with the parameters differentiated.  This is
the structural replacement for expanding nested Zorn-matrix commutators.
-/

namespace InfoGeometry.Algebra

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

theorem NonAssocDerivation.stanDerMap_covariant
    (D : NonAssocDerivation R A) (a b x : A) :
    D (stanDerMap (R := R) a b x) -
        stanDerMap (R := R) a b (D x) =
      stanDerMap (R := R) (D a) b x + stanDerMap (R := R) a (D b) x := by
  change D.toLinearMap (a * (b * x) - b * (a * x) +
      (a * (x * b) - (a * x) * b) +
      ((x * b) * a - (x * a) * b)) -
    (a * (b * D x) - b * (a * D x) +
      (a * (D x * b) - (a * D x) * b) +
      ((D x * b) * a - (D x * a) * b)) =
    ((D a) * (b * x) - b * ((D a) * x) +
      ((D a) * (x * b) - ((D a) * x) * b) +
      ((x * b) * (D a) - (x * (D a)) * b)) +
    (a * ((D b) * x) - (D b) * (a * x) +
      (a * (x * (D b)) - (a * x) * (D b)) +
      ((x * (D b)) * a - (x * a) * (D b)))
  rw [D.toLinearMap.map_add, D.toLinearMap.map_add, D.toLinearMap.map_sub,
    D.toLinearMap.map_sub, D.toLinearMap.map_sub]
  simp only [D.leibniz']
  simp only [← NonAssocDerivation.toLinearMap_apply, sub_eq_add_neg,
    add_mul, mul_add]
  abel

end InfoGeometry.Algebra
