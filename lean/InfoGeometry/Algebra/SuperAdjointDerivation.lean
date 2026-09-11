import InfoGeometry.Algebra.SupergradedJordanLieSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Homogeneous super-adjoint transport

For homogeneous elements, `superAdjoint p Q x` is the inner superbracket
`[Q,x]ₛ`.  The only assertion made here is the associative-algebraic
super-Jacobi transport identity.  No `LieSuperalgebra` instance or analytic
flow is introduced.
-/

namespace InfoGeometry.Algebra.SuperAdjointDerivation

open InfoGeometry.Algebra.SupergradedBracket

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  [NeZero (2 : R)]

/-- Inner homogeneous super-adjoint action. -/
def superAdjoint (p q : Bool) (Q x : A) : A :=
  superBracket p q Q x

@[simp] theorem superAdjoint_apply (p q : Bool) (Q x : A) :
    superAdjoint p q Q x = superBracket p q Q x := rfl

/-- The super-Jacobi identity written as transport of a homogeneous
super-adjoint action through a homogeneous bracket. -/
theorem superAdjoint_superJacobi (p q r : Bool) (Q x y : A) :
    gradedSign (R := R) p r •
          superAdjoint p (q ^^ r) Q
            (superBracket q r x y) +
        gradedSign (R := R) q p •
          superAdjoint q (r ^^ p) x
            (superAdjoint r p y Q) +
        gradedSign (R := R) r q •
          superAdjoint r (p ^^ q) y
            (superAdjoint p q Q x) = 0 := by
  exact superBracket_superJacobi p q r Q x y

end InfoGeometry.Algebra.SuperAdjointDerivation
