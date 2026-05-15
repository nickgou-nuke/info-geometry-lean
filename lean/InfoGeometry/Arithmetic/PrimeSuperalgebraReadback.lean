import Mathlib
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

/-!
# InfoGeometry.Arithmetic.PrimeSuperalgebraReadback

Finite supergraded readback for prime-bit arithmetic.

This file does not prove an infinite zeta theorem, analytic continuation, the
Riemann hypothesis, or a full DG-superalgebra of primes.

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

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

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

/-! ## 4. Witness sockets for richer superalgebra structure -/

/--
A witness-gated prime superalgebra socket.

This is deliberately abstract. It records a superalgebra interpretation without
asserting that the finite prime-bit arithmetic layer itself has already built a
full free supercommutative algebra or DG-superalgebra.
-/
structure PrimeSuperalgebraWitness
    (Carrier : Type*) where
  /-- Multiplication/readout on the carrier. -/
  mul : Carrier → Carrier → Carrier
  /-- Degree or fermion-number readout. -/
  degree : Carrier → ℕ
  /-- Parity readout. -/
  parity : Carrier → ℤ
  /-- Supercommutativity law, supplied by a concrete model. -/
  supercommutativity_law : Prop
  /-- Proof/certificate of supercommutativity. -/
  supercommutativity_certificate :
    supercommutativity_law

namespace PrimeSuperalgebraWitness

variable {Carrier : Type*}
variable (A : PrimeSuperalgebraWitness Carrier)

/-- The supplied supercommutativity law is available. -/
theorem supercommutativity_valid :
    A.supercommutativity_law :=
  A.supercommutativity_certificate

end PrimeSuperalgebraWitness

/--
A witness-gated differential graded prime superalgebra socket.

The differential laws are explicit fields. This prevents smuggling an
arithmetic derivative, von Mangoldt operator, or Hecke differential into the
theory without proof.
-/
structure PrimeDGSuperalgebraWitness
    (Carrier : Type*) extends PrimeSuperalgebraWitness Carrier where
  /-- Differential/odd derivation candidate. -/
  d : Carrier → Carrier
  /-- Nilpotence law. -/
  d_sq_zero_law : Prop
  /-- Proof/certificate of nilpotence. -/
  d_sq_zero_certificate :
    d_sq_zero_law
  /-- Graded Leibniz law. -/
  graded_leibniz_law : Prop
  /-- Proof/certificate of the graded Leibniz law. -/
  graded_leibniz_certificate :
    graded_leibniz_law

namespace PrimeDGSuperalgebraWitness

variable {Carrier : Type*}
variable (D : PrimeDGSuperalgebraWitness Carrier)

/-- The supplied nilpotence law is available. -/
theorem d_sq_zero_valid :
    D.d_sq_zero_law :=
  D.d_sq_zero_certificate

/-- The supplied graded Leibniz law is available. -/
theorem graded_leibniz_valid :
    D.graded_leibniz_law :=
  D.graded_leibniz_certificate

end PrimeDGSuperalgebraWitness

/-! ## 5. Owner target -/

/--
Owner target for the finite prime-superalgebra readback.

The existing finite arithmetic layer supplies:

* Möbius as fermion parity on represented square-free states;
* finite supertrace equals finite inverse Euler product.
-/
def PrimeSuperalgebraReadbackOwnerTarget : Prop :=
  ∀ P : FermionicPrimeRegister,
  ∀ ψ : FermionicPrimeState P,
  ∀ x : ℕ → ℂ,
    ArithmeticFunction.moebius (representedSquarefreeNat P ψ) =
      fermionParity P ψ
    ∧
    finiteSupertraceDirichlet P x =
      finiteInverseEulerProduct P x

/-- The owner target follows by processing the installed finite arithmetic theorems. -/
theorem primeSuperalgebraReadbackOwnerTarget :
    PrimeSuperalgebraReadbackOwnerTarget := by
  intro P ψ x
  exact
    ⟨mobius_eq_fermionParity P ψ,
      finiteSupertraceDirichlet_eq_inverseEulerProduct P x⟩

end InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
