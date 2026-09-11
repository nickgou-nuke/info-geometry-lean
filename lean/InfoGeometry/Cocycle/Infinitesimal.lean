import Mathlib.RingTheory.Derivation.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Infinitesimal Cocycle Calculus

This file owns the algebraic infinitesimal endpoint of the cocycle chain:
logarithmic cocycles differentiate to derivations.

The modular/operator-algebraic specialization lives in
`InfoGeometry.Volume.ConnesInfinitesimal`; this file only proves the generic
associative-algebra commutator Leibniz rule and records the corresponding
mathlib `Derivation` multiplication law.
-/

namespace InfoGeometry.Cocycle.Infinitesimal

/-- Inner commutator generator `[K,-]` in an associative ring. -/
def innerCommutatorDerivation {A : Type*} [Ring A] (K X : A) : A :=
  K * X - X * K

/-- The inner commutator generator satisfies the Leibniz rule. -/
theorem innerCommutatorDerivation_mul {A : Type*} [Ring A] (K X Y : A) :
    innerCommutatorDerivation K (X * Y) =
      innerCommutatorDerivation K X * Y + X * innerCommutatorDerivation K Y := by
  unfold innerCommutatorDerivation
  noncomm_ring

/-- Mathlib derivations expose the same infinitesimal chain rule. -/
theorem mathlib_derivation_leibniz {R A : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Derivation R A A) (a b : A) :
    D (a * b) = a * D b + b * D a := by
  simp [D.leibniz a b]

end InfoGeometry.Cocycle.Infinitesimal
