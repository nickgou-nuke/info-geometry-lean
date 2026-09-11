import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace InfoGeometry.Arithmetic.MobiusClassical

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/--
Duality Theorem: The number-theoretic Möbius function $\mu(d)$ on a squarefree 
integer $d$ is isomorphic to the boolean poset Möbius sign $(-1)^k$, where $k$ is 
the number of prime factors of $d$ (given by `cardFactors d`).
-/
theorem moebius_squarefree_eq_boolean_sign
    {d : ℕ} (hsq : Squarefree d) :
    μ d = (-1) ^ (cardFactors d) := by
  rw [moebius_apply_of_squarefree hsq]

end InfoGeometry.Arithmetic.MobiusClassical
