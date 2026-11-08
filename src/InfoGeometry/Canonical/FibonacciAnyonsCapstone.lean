import InfoGeometry.Topological.FibonacciAnyons
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.FibonacciAnyonsCapstone

open InfoGeometry.Topological.FibonacciAnyons

/-!
This capstone is parameterized by the finite raw matrix data owned by
`Topological.FibonacciAnyons`.  Older upstream versions referred to a
different, closed numerical model; the local owner deliberately exposes the
honest hypothesis-bearing interface instead.
-/

theorem fibonacci_matrix_capstone
    {K : Type*} [CommRing K]
    (τ sqrtτ : K) (hτ : τ ^ 2 + τ = 1)
    (hsqrtτ : sqrtτ ^ 2 = τ) :
    F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ = 1 := by
  exact F_involution τ sqrtτ hτ hsqrtτ

end InfoGeometry.Canonical.FibonacciAnyonsCapstone
