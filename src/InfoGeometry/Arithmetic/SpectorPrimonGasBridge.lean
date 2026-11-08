import InfoGeometry.Arithmetic.MobiusPrimonParity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.PrimonGasSupertrace
import InfoGeometry.Arithmetic.SupersymmetricPrimonGas

/-!
# Spector primon gas bridge, finite owner surface

This module names the finite theorem corridor corresponding to Donald
Spector's primon-gas observation:

* square-free prime-bit states carry the Mobius value `(-1)^F`;
* nonsquare-free states are killed by the Mobius coefficient;
* a nonempty finite prime register has cancelling Boolean Witten supertrace;
* regulated finite bosonic and signed-fermionic Euler factors cancel.

#### BUCKET 1: CLOSED FINITE THEOREMS
The theorem surface below is fully finite.  It reuses the existing arithmetic
owners for prime-bit state labeling, Mobius parity, nonsquare-free
annihilation, finite Witten cancellation, and finite Euler-factor
cancellation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The finite Euler-factor identities require the explicit local regulator
premise `1 - x p != 0`, and the square-energy ratio also requires
`1 - x p * x p != 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
No infinite Euler product, analytic continuation, Hagedorn transition,
KMS phase theorem, Bethe-state counting theorem, unorientable parity anomaly,
zeta-zero statement, GUE asymptotics, or Riemann Hypothesis consequence is
proved here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SpectorPrimonGasBridge

open scoped BigOperators

open InfoGeometry.Arithmetic.MobiusPrimonParity
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBosonFermionGas
open InfoGeometry.Arithmetic.PrimonGasSupertrace

/-! ## Prime-bit Fock labeling and Mobius parity -/

/--
Spector state labeling, finite prime-bit form.

The integer represented by an occupied finite prime-bit state has Mobius value
equal to its fermion parity.
-/
theorem spector_state_mobius_eq_fermionParity
    (P : PrimeRegister) (psi : PrimeBitState P) :
    ArithmeticFunction.moebius (representedNatOfState P psi) =
      fermionParityOfState P psi :=
  mobius_representedNatOfState_eq_fermionParity P psi

/--
Subset-register form of the same finite theorem.

The represented square-free primon state has Mobius readout `(-1)^F`.
-/
theorem spector_squarefree_state_mobius_eq_fermionParity
    (P : PrimeRegister) (S : SquareFreePrimonState P) :
    S.mobiusReadout = S.fermionParity :=
  SquareFreePrimonState.mobiusReadout_eq_fermionParity S

/--
Pauli/exterior exclusion in the arithmetic layer.

Nonsquare-free integers have zero Mobius coefficient.
-/
theorem spector_repeated_prime_sector_killed
    {n : Nat} (hn : ¬ Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  mobius_zero_of_not_squarefree hn

/--
Finite Boolean Witten-index cancellation for a nonempty prime register.
-/
theorem spector_finite_witten_index_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : Int) ^ S.card) = 0 :=
  finite_witten_index_cancel P hP

/-! ## Finite Euler-factor closure -/

variable {ι R : Type*} [Field R]

/--
Finite Spector boson/signed-fermion closure.

This is the finite algebraic theorem behind the formal slogan
`Z_boson * Z_signed = 1`.
-/
theorem spector_finite_boson_signed_closure
    (S : Finset ι) (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x * signedFermionPartition S x = 1 :=
  boson_mul_signedFermion_cancel S x h

/--
Finite positive-fermion ratio form.

This is the finite theorem-root of the square-free positive fermion product,
not an infinite zeta quotient.
-/
theorem spector_finite_positive_fermion_ratio
    (S : Finset ι) (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0)
    (h_sq : ∀ p ∈ S, 1 - x p * x p ≠ 0) :
    positiveFermionPartition S x * bosonPartition S (fun p => x p * x p) =
      bosonPartition S x :=
  positiveFermion_mul_squareBoson_eq_boson S x h h_sq

/--
Finite second-order exterior factorization:
`(1+x_p)(1-x_p)=1-x_p^2` primewise, multiplied over a finite register.
-/
theorem spector_finite_fermion_signed_secondOrder
    (S : Finset ι) (x : ι → R) :
    SupersymmetricPrimonGas.fermionPartition S x *
        signedFermionPartition S x =
      SupersymmetricPrimonGas.secondOrderSignedPartition S x :=
  SupersymmetricPrimonGas.fermion_mul_signed_eq_secondOrder S x

/-! ## Finite supertrace support -/

/--
The finite Mobius supertrace only sees square-free states.
-/
theorem spector_finite_supertrace_supported_on_squarefree
    (mu : MobiusCoefficient) (A : Finset Nat) (beta : Real) :
    mu.finiteSupertrace A beta =
      ∑ n ∈ A.filter IsSquarefreeState,
        mu.coeff n * primonBoltzmannWeight beta n :=
  mu.finiteSupertrace_eq_squarefree_filter A beta

end InfoGeometry.Arithmetic.SpectorPrimonGasBridge
