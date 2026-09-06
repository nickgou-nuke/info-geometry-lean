import Mathlib.Tactic
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

/-!
# Möbius Witten Weyl Denominator

The finite theorem-owned bridge between three already-formalized surfaces:

* the Möbius Dirichlet polynomial over a finite prime register;
* the fermionic/Witten signed supertrace `STrF`;
* the finite Weyl/Euler denominator `∏ p, (1 - q p)`.

#### BUCKET 1: CLOSED FINITE THEOREMS
`finiteMobiusPolynomial_eq_weylDenominator`,
`finiteMobiusPolynomial_eq_wittenSupertrace`, and
`finiteBoson_mul_mobiusPolynomial_cancel` are closed finite algebraic
theorems.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`finiteBoson_mul_mobiusPolynomial_cancel` requires the explicit nonvanishing
premise `∀ p ∈ P.primes, 1 - q p ≠ 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove the infinite Dirichlet-series identity
`∑ μ(n)n^{-s} = 1 / ζ(s)`, analytic convergence for `Re(s) > 1`,
McKean-Singer theory, a Weyl-Kac denominator identity, Riemann-zero
localization, or the Riemann Hypothesis.  It is the finite cutoff algebraic
spine needed before those analytic statements.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MobiusWittenWeylDenominator

open scoped BigOperators
open InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/--
Finite Möbius polynomial equals the finite Weyl/Euler denominator.

This is the finite cutoff form of the slogan
`Σ μ(n) q(n) = ∏ p (1 - q p)`.
-/
theorem finiteMobiusPolynomial_eq_weylDenominator
    (P : PrimeRegister) (q : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial P q =
      InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P.primes q := by
  calc
    finiteMobiusDirichletPolynomial P q =
        finiteFermionicEulerProduct P q :=
          finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct P q
    _ =
        InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P.primes q := by
          rfl

/--
Finite Möbius polynomial equals the finite Witten/fermionic supertrace.

Here `STrF` is the signed finite Fock supertrace
`Σ_{S ⊆ P} (-1)^|S| ∏_{p∈S} q p`.
-/
theorem finiteMobiusPolynomial_eq_wittenSupertrace
    (P : PrimeRegister) (q : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial P q =
      InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q := by
  calc
    finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P.primes q :=
          finiteMobiusPolynomial_eq_weylDenominator P q
    _ = InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q :=
          InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator_eq_finiteSupertrace P.primes q

/--
Finite boson × Möbius/Witten denominator cancellation.

This is the finite algebraic core of
`ζ(s) * (1 / ζ(s)) = 1`, with nonzero local factors supplied explicitly.
-/
theorem finiteBoson_mul_mobiusPolynomial_cancel
    (P : PrimeRegister) (q : ℕ → ℂ)
    (h : ∀ p ∈ P.primes, (1 : ℂ) - q p ≠ 0) :
    InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator P.primes q *
      finiteMobiusDirichletPolynomial P q = 1 := by
  rw [finiteMobiusPolynomial_eq_weylDenominator P q]
  exact InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.bosonicInverse_mul_weylDenominator_cancel P.primes q h

/-- Finite master packet tying together Möbius parity, Witten supertrace, and Weyl denominator. -/
theorem finite_mobius_witten_weyl_packet
    (P : PrimeRegister) (q : ℕ → ℂ)
    (h : ∀ p ∈ P.primes, (1 : ℂ) - q p ≠ 0) :
    finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P.primes q ∧
      finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q ∧
      InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator P.primes q *
        finiteMobiusDirichletPolynomial P q = 1 :=
  ⟨finiteMobiusPolynomial_eq_weylDenominator P q,
    finiteMobiusPolynomial_eq_wittenSupertrace P q,
    finiteBoson_mul_mobiusPolynomial_cancel P q h⟩

end InfoGeometry.Arithmetic.MobiusWittenWeylDenominator

