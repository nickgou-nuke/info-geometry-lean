import InfoGeometry.Canonical.FiniteCompassBraidedChain
import InfoGeometry.Canonical.FiniteFibonacciAnyonRegister

/-!
# InfoGeometry.Canonical.FiniteFibonacciCompassBridge

Finite Fibonacci braid transport on local compass packets.

This file only specializes the already-proved finite braid transport layer to
the Fibonacci braid-word surface.

It does not add a new anyon theory.
It does not claim an infinite limit.
It does not claim conformal blocks or monodromy matrices.
-/

namespace FiniteFibonacciCompassBridge

open InfoGeometry.Canonical.FiniteCompassBraidedChain
open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Canonical.FiniteFibonacciAnyonRegister

/--
Finite Fibonacci braid transport on a local compass chain.

The transport is the generic braid transport already proved for compass
chains, specialized to the Fibonacci braid-word surface.
-/
def fibonacciCompassTransport {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) : CompassChain ℕ Op :=
  braidTransport w C

@[simp]
theorem fibonacciCompassTransport_apply {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    fibonacciCompassTransport w C i = C ((evalBraidWord w).symm i) := by
  rfl

/-- Fibonacci braid transport preserves the local elliptic law. -/
theorem fibonacciCompassTransport_elliptic_sq
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (fibonacciCompassTransport w C i).elliptic *
        (fibonacciCompassTransport w C i).elliptic = -1 :=
  braidTransport_elliptic_sq w C i

/-- Fibonacci braid transport preserves the local hyperbolic law. -/
theorem fibonacciCompassTransport_hyperbolic_sq
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (fibonacciCompassTransport w C i).hyperbolic *
        (fibonacciCompassTransport w C i).hyperbolic = 1 :=
  braidTransport_hyperbolic_sq w C i

/-- Fibonacci braid transport preserves the local parabolic law. -/
theorem fibonacciCompassTransport_parabolic_sq
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (fibonacciCompassTransport w C i).parabolic *
        (fibonacciCompassTransport w C i).parabolic = 0 :=
  braidTransport_parabolic_sq w C i

/-- Fibonacci braid transport is invariant under the adjacent braid rewrite. -/
theorem fibonacciCompassTransport_braid_rewrite
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (i : ℕ) (left right : FibonacciBraidWord) (C : CompassChain ℕ Op) :
    fibonacciCompassTransport (left ++ [i, i + 1, i] ++ right) C =
      fibonacciCompassTransport (left ++ [i + 1, i, i + 1] ++ right) C := by
  exact braidTransport_braid_rewrite i left right C

/-- Fibonacci braid transport is invariant under separated-commutation rewrites. -/
theorem fibonacciCompassTransport_commute_rewrite
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    {i j : ℕ} (hsep : i + 1 < j) (left right : FibonacciBraidWord)
    (C : CompassChain ℕ Op) :
    fibonacciCompassTransport (left ++ [i, j] ++ right) C =
      fibonacciCompassTransport (left ++ [j, i] ++ right) C := by
  exact braidTransport_commute_rewrite hsep left right C

end FiniteFibonacciCompassBridge
