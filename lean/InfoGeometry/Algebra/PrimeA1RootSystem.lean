import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime A1 Root System

Defines the $A_1^P$ root system where each prime $p$ provides an independent 
$SU(2)$ sector. This is the algebraic foundation of the Primon gas.
-/

namespace InfoGeometry.Algebra

/--
A finite set of primes defining a cutoff $A_1^P$ root system.
-/
structure PrimeA1RootSystem where
  P : Finset ℕ
  all_prime : ∀ p ∈ P, Nat.Prime p

namespace PrimeA1RootSystem

/--
The Weyl group of the finite $A_1^P$ system is the Boolean group of subsets of $P$.
Each element $w \in W$ corresponds to a reflection in the $SU(2)_p$ sectors.
-/
def WeylGroup (S : PrimeA1RootSystem) := Finset (S.P)

/--
The signature of a Weyl group element is $(-1)^{|w|}$.
In the prime gas, this corresponds to the Möbius function $\mu(n)$.
-/
def signature {S : PrimeA1RootSystem} (w : S.WeylGroup) : ℤ :=
  if w.card % 2 = 0 then 1 else -1

end PrimeA1RootSystem

end InfoGeometry.Algebra
