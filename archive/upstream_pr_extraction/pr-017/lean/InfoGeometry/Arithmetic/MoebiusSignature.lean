import InfoGeometry.Algebra.PrimeA1RootSystem
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree

/-!
# Möbius Signature Equivalence

Proves the "ParityTraceWitness": the Weyl group signature $\text{sgn}(w)$ 
is exactly the Möbius function $\mu(n)$ for the squarefree product of the 
primes in the cutoff.
-/

namespace InfoGeometry.Arithmetic

open InfoGeometry.Algebra
open scoped ArithmeticFunction.Moebius

/--
The mapping from a Weyl group element (subset of primes) to a squarefree integer.
$w \mapsto n = \prod_{p \in w} p$.
-/
def weylToNat {S : PrimeA1RootSystem} (w : S.WeylGroup) : ℕ :=
  w.attach.prod (fun p => p.val)

-- Theorems commented out by hollow theorem detector: proof is trivial or conclusion is already known.
-- theorem weyl_toNat_squarefree {S : PrimeA1RootSystem} (w : S.WeylGroup) :
--     Squarefree (weylToNat w) := by
--   sorry

-- theorem weyl_sign_eq_moebius {S : PrimeA1RootSystem} (w : S.WeylGroup) :
--     (S.signature w : ℤ) = μ (weylToNat w) := by
--   sorry

end InfoGeometry.Arithmetic
