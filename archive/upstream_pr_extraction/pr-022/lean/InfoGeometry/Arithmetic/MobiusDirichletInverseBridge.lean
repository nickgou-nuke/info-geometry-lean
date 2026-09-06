import Mathlib
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

Finite Möbius/Witten inverse bridge.

This file is the finite arithmetic bridge between the prime-bit Witten index
and the Euler-product corridor:

* the finite Möbius Dirichlet polynomial over squarefree prime-bit states;
* the finite fermionic Euler/Witten product `∏ (1 - x_p)`;
* the theorem that the two are equal.

No infinite Dirichlet series, convergence theorem, reciprocal zeta identity, or
analytic continuation claim is made here.
-/

namespace InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/--
Finite Möbius Dirichlet polynomial over the squarefree states of a prime
register.

For `x p = p^{-s}`, this is the finite cutoff of the fermionic inverse-zeta
Dirichlet series.
-/
@[rep_depth thermo]
noncomputable def finiteMobiusDirichletPolynomial
    (P : PrimeRegister) (x : ℕ → ℂ) : ℂ :=
  ∑ S ∈ P.primes.powerset,
    (ArithmeticFunction.moebius (∏ p ∈ S, p) : ℂ) * ∏ p ∈ S, x p

/--
Finite fermionic Euler/Witten product.

For `x p = p^{-s}`, this is the finite cutoff of `1 / ζ(s)`.
-/
@[rep_depth thermo]
noncomputable def finiteFermionicEulerProduct
    (P : PrimeRegister) (x : ℕ → ℂ) : ℂ :=
  ∏ p ∈ P.primes, (1 - x p)

/--
Finite Möbius Dirichlet polynomial equals the finite fermionic Euler product.

This is the finite Spector bridge from prime-bit parity to the inverse
Euler-product side.
-/
@[rep_depth thermo]
theorem finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct
    (P : PrimeRegister) (x : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial P x =
      finiteFermionicEulerProduct P x := by
  classical
  unfold finiteMobiusDirichletPolynomial finiteFermionicEulerProduct
  calc
    (∑ S ∈ P.primes.powerset,
      (ArithmeticFunction.moebius (∏ p ∈ S, p) : ℂ) * ∏ p ∈ S, x p)
        =
      ∑ S ∈ P.primes.powerset,
        (-1 : ℂ) ^ S.card * ∏ p ∈ S, x p := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
        have hμ :
            ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card :=
          mobius_prime_product_eq_parity S (fun p hp => P.prime_mem p (hSub hp))
        simp [hμ]
    _ =
      ∑ S ∈ P.primes.powerset,
        (-1 : ℂ) ^ S.card * (∏ p ∈ P.primes \ S, (1 : ℂ)) * ∏ p ∈ S, x p := by
        refine Finset.sum_congr rfl ?_
        intro S _hS
        simp [mul_assoc]
    _ = ∏ p ∈ P.primes, (1 - x p) := by
        exact (Finset.prod_sub (fun _ : ℕ => (1 : ℂ)) x P.primes).symm

/-- Empty prime register gives the unit inverse-zeta cutoff. -/
@[simp, rep_depth thermo]
theorem finiteMobiusDirichletPolynomial_empty
    (x : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial
      ({ primes := ∅, prime_mem := by simp } : PrimeRegister) x = 1 := by
  simp [finiteMobiusDirichletPolynomial]

/-- Empty prime register gives the unit fermionic Euler product. -/
@[simp, rep_depth thermo]
theorem finiteFermionicEulerProduct_empty
    (x : ℕ → ℂ) :
    finiteFermionicEulerProduct
      ({ primes := ∅, prime_mem := by simp } : PrimeRegister) x = 1 := by
  simp [finiteFermionicEulerProduct]

end InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
