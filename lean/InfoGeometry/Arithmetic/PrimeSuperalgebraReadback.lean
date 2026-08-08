import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

/-!
# InfoGeometry.Arithmetic.PrimeSuperalgebraReadback

Finite supergraded readback for prime-bit arithmetic.

This file does not prove an infinite zeta theorem, analytic continuation, the
Riemann property, or a full DG-superalgebra of primes.

It exposes the existing finite Möbius/Witten arithmetic layer using
superalgebra terminology:

* prime register = finite set of fermionic prime modes;
* prime-bit state = finite square-free fermionic state;
* fermion number = occupied-prime cardinality;
* fermion parity = `(-1)^F`;
* Möbius value on represented square-free states equals fermion parity;
* finite supertrace Dirichlet polynomial equals finite fermionic Euler product.

Full bosonic sectors, DG differentials, Hecke actions, and infinite zeta
identifications require separate witnesses.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeSuperalgebraReadback

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open PrimeBitWittenIndex
open MobiusDirichletInverseBridge

/-! ## 1. Fermionic prime-bit supersector -/

/-- A finite fermionic prime-sector register. -/
abbrev FermionicPrimeRegister :=
  PrimeRegister

/-- A finite fermionic prime-bit state. -/
abbrev FermionicPrimeState
    (P : FermionicPrimeRegister) :=
  PrimeBitState P

/-- The square-free natural number represented by a fermionic prime-bit state. -/
def representedSquarefreeNat
    (P : FermionicPrimeRegister)
    (ψ : FermionicPrimeState P) : ℕ :=
  representedNatOfState P ψ

/-- Fermion number of a finite prime-bit state. -/
def fermionDegree
    (P : FermionicPrimeRegister)
    (ψ : FermionicPrimeState P) : ℕ :=
  fermionNumberOfState P ψ

/-- Fermion parity `(-1)^F` of a finite prime-bit state. -/
def fermionParity
    (P : FermionicPrimeRegister)
    (ψ : FermionicPrimeState P) : ℤ :=
  fermionParityOfState P ψ

/-- Möbius equals fermion parity on represented square-free prime-bit states. -/
theorem mobius_eq_fermionParity
    (P : FermionicPrimeRegister)
    (ψ : FermionicPrimeState P) :
    ArithmeticFunction.moebius (representedSquarefreeNat P ψ) =
      fermionParity P ψ := by
  exact mobius_representedNatOfState_eq_fermionParity P ψ

/--
Nonsquare-free states have zero Möbius coefficient.

This is the arithmetic exclusion clause corresponding to repeated prime modes
in the fermionic sector.
-/
theorem mobius_zero_of_nonsquarefree
    {n : ℕ}
    (hn : ¬ Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  mobius_eq_zero_of_not_squarefree hn

/-! ## 2. Finite supertrace / inverse Euler product readback -/

/--
Finite supertrace Dirichlet polynomial.

For `x p = p^{-β}`, this is the finite cutoff of the supersymmetric fermionic
inverse-zeta Dirichlet series.
-/
def finiteSupertraceDirichlet
    (P : FermionicPrimeRegister)
    (x : ℕ → ℂ) : ℂ :=
  finiteMobiusDirichletPolynomial P x

/-- Finite fermionic Euler product. -/
def finiteInverseEulerProduct
    (P : FermionicPrimeRegister)
    (x : ℕ → ℂ) : ℂ :=
  finiteFermionicEulerProduct P x

/-- Finite supertrace equals the finite fermionic Euler product. -/
theorem finiteSupertraceDirichlet_eq_inverseEulerProduct
    (P : FermionicPrimeRegister)
    (x : ℕ → ℂ) :
    finiteSupertraceDirichlet P x =
      finiteInverseEulerProduct P x := by
  exact finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct P x

/-- Finite Boolean Witten-index cancellation over a nonempty prime register. -/
theorem finiteBooleanWittenIndex_cancel
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finite_witten_index_cancel P hP

/-- Finite divisor Möbius cancellation over a nonempty prime register. -/
theorem finiteDivisorMobius_cancel
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p)) = 0 :=
  finite_divisor_mobius_sum_cancel P hP

/-! ## 3. Thermal finite cutoff readout -/

/--
Thermal single-prime factor `exp(-β log p)`.

This avoids committing to real powers in the readback layer.
-/
def thermalPrimeFactor
    (β : ℝ)
    (p : ℕ) : ℂ :=
  (Real.exp (-β * Real.log (p : ℝ)) : ℂ)

lemma thermalPrimeFactor_ne_zero (β : ℝ) (p : ℕ) :
    thermalPrimeFactor β p ≠ 0 := by
  unfold thermalPrimeFactor
  exact_mod_cast (Real.exp_ne_zero _)

/-- Finite thermal supertrace over a prime register. -/
def finiteThermalSupertrace
    (P : FermionicPrimeRegister)
    (β : ℝ) : ℂ :=
  finiteSupertraceDirichlet P (thermalPrimeFactor β)

/-- Finite thermal inverse Euler product over a prime register. -/
def finiteThermalInverseEulerProduct
    (P : FermionicPrimeRegister)
    (β : ℝ) : ℂ :=
  finiteInverseEulerProduct P (thermalPrimeFactor β)

/-- Finite thermal supertrace equals the finite thermal inverse Euler product. -/
theorem finiteThermalSupertrace_eq_inverseEulerProduct
    (P : FermionicPrimeRegister)
    (β : ℝ) :
    finiteThermalSupertrace P β =
      finiteThermalInverseEulerProduct P β := by
  exact finiteSupertraceDirichlet_eq_inverseEulerProduct P (thermalPrimeFactor β)

/-! ## 4. Native theorem content only -/

-- Möbius parity on represented square-free states.
-- Finite supertrace equals finite inverse Euler product.
-- Thermal finite cutoffs.

end InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
