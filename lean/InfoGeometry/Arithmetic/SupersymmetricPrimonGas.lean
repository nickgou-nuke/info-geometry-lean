import InfoGeometry.Arithmetic.MobiusPrimonParity
import InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Supersymmetric primon gas, finite theorem surface

This module collects the finite algebraic corridor behind the primon-gas
readout:

* bosonic Euler factors use unrestricted occupation: `(1 - x_p)⁻¹`;
* fermionic Euler factors use exterior occupation: `1 + x_p`;
* the signed Witten/Möbius factor is `1 - x_p`;
* the second-order correction is `1 - x_p^2`.
* the `{+1,-1,0}` readout is the existing tripotent trifactor split,
  interpreted here as square-free even / square-free odd / repeated-prime
  annihilation.

#### BUCKET 1: CLOSED FINITE THEOREMS
We prove the finite identities
`∏(1+x_p) * ∏(1-x_p) = ∏(1-x_p^2)` and, when every
`1-x_p` is nonzero, `Z_boson * ∏(1-x_p^2) = Z_fermion`.
We also reuse the existing square-free Möbius parity theorem and the existing
tripotent trifactor projector theorem.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The statement `Q² = H` is represented as the explicit predicate
`SuperchargeSquaresToHamiltonian Q H`.  Any physical supersymmetric
Hamiltonian model must supply that equality.
The statement "RH is stable unbroken supersymmetry at the boundary" is kept as
the explicit predicate `RHSupersymmetricBoundaryScenario`.

#### BUCKET 3: OPEN CLOSURE DEBT
No infinite Euler product, analytic continuation, CAR/CCR C*-completion,
mass-gap theorem, spectral interpretation of zeta zeros, or Riemann Hypothesis
claim is proved here.
-/

noncomputable section

namespace SupersymmetricPrimonGas

open scoped BigOperators

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBosonFermionGas
open InfoGeometry.Arithmetic.MobiusPrimonParity
open InfoGeometry.Canonical.TrifactorDecomposition

variable {ι R : Type*} [Field R]

/-- Ordinary fermionic primon Euler product: exterior occupation `0` or `1`. -/
def fermionPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 + x p)

/-- Second-order signed Euler correction, the finite shadow of `1 / ζ(2s)`. -/
def secondOrderSignedPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 - (x p) ^ 2)

/--
Finite fermion/signed-Witten factorization.

Per prime this is `(1+x_p)(1-x_p)=1-x_p^2`; globally it is the finite
Euler-factor skeleton behind `Z_fermion = ζ(s)/ζ(2s)`.
-/
theorem fermion_mul_signed_eq_secondOrder
    (S : Finset ι) (x : ι → R) :
    fermionPartition S x * signedFermionPartition S x =
      secondOrderSignedPartition S x := by
  unfold fermionPartition signedFermionPartition secondOrderSignedPartition
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro p hp
  ring

/--
Finite bosonic-to-fermionic conversion with the second-order correction.

This is the finite theorem-root of
`ζ(s) * (1 / ζ(2s)) = ∏_p (1+p^{-s})`, not an infinite-product theorem.
-/
theorem boson_mul_secondOrder_eq_fermion
    (S : Finset ι) (x : ι → R) (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x * secondOrderSignedPartition S x =
      fermionPartition S x := by
  unfold bosonPartition secondOrderSignedPartition fermionPartition
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hp_nonzero : 1 - x p ≠ 0 := h p hp
  calc
    (1 - x p)⁻¹ * (1 - (x p) ^ 2)
        = (1 - x p)⁻¹ * ((1 - x p) * (1 + x p)) := by
          ring
    _ = ((1 - x p)⁻¹ * (1 - x p)) * (1 + x p) := by
          ring
    _ = 1 + x p := by
          rw [inv_mul_cancel₀ hp_nonzero]
          simp

/-! ## Square-free Möbius / Witten grading readbacks -/

/-- Möbius readout is exactly fermion parity on finite square-free primon states. -/
theorem mobius_is_squarefree_fermionParity
    (P : PrimeRegister) (S : SquareFreePrimonState P) :
    S.mobiusReadout = S.fermionParity :=
  SquareFreePrimonState.mobiusReadout_eq_fermionParity S

/-- Non-square-free sectors are killed by the Möbius/Witten grading. -/
theorem mobius_kills_repeated_prime_sector
    {n : ℕ} (hn : ¬ Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  MobiusPrimonParity.mobius_zero_of_not_squarefree hn

/-- The finite Boolean Witten index of a nonempty prime register vanishes. -/
theorem finite_wittenIndex_vanishes_on_nonempty_register
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    PrimonSupergradedGasAlgebra.finitePrimonWittenIndex P = 0 :=
  PrimonSupergradedGasAlgebra.finitePrimonWittenIndex_cancel P hP

/-! ## `{+1,-1,0}` trifactor sector readout -/

variable {A : Type*} [CommRing A] [Invertible (2 : A)]

/-- The `+1` bosonic/square-free-even sector of a tripotent readout. -/
abbrev bosonicTrifactorProjector (T : A) : A :=
  P_plus T

/-- The `-1` fermionic/square-free-odd sector of a tripotent readout. -/
abbrev fermionicTrifactorProjector (T : A) : A :=
  P_minus T

/-- The `0` repeated-prime/null-boundary sector of a tripotent readout. -/
abbrev ghostTrifactorProjector (T : A) : A :=
  P_zero T

/--
Finite trifactor projector packet for the primon `{+1,-1,0}` grading.

This is just the existing tripotent projector theorem with primon-sector names.
-/
theorem primon_trifactor_projector_packet (T : A) (hT : T ^ 3 = T) :
    (ghostTrifactorProjector T * ghostTrifactorProjector T = ghostTrifactorProjector T ∧
      bosonicTrifactorProjector T * bosonicTrifactorProjector T = bosonicTrifactorProjector T ∧
      fermionicTrifactorProjector T * fermionicTrifactorProjector T = fermionicTrifactorProjector T) ∧
    (bosonicTrifactorProjector T * fermionicTrifactorProjector T = 0 ∧
      ghostTrifactorProjector T * bosonicTrifactorProjector T = 0 ∧
      ghostTrifactorProjector T * fermionicTrifactorProjector T = 0) ∧
    ghostTrifactorProjector T + bosonicTrifactorProjector T + fermionicTrifactorProjector T = 1 ∧
    (T * ghostTrifactorProjector T = 0 ∧
      T * bosonicTrifactorProjector T = bosonicTrifactorProjector T ∧
      T * fermionicTrifactorProjector T = -fermionicTrifactorProjector T) ∧
    bosonicTrifactorProjector T - fermionicTrifactorProjector T = T :=
  trifactor_capstone T hT

/-! ## Explicit conjectural/spectral boundary predicate -/

/--
An explicit proposition-level socket for the informal phrase
"RH is stable, unbroken supersymmetry at the boundary".

The components are deliberately named assumptions.  This definition does not
prove any of them.
-/
def RHSupersymmetricBoundaryScenario
    (stableMassGap wittenBalanceOnCriticalLine boundarySUSYUnbroken
      zerosOnCriticalLine : Prop) : Prop :=
  stableMassGap ∧ wittenBalanceOnCriticalLine ∧ boundarySUSYUnbroken ∧ zerosOnCriticalLine

/-! ## Conditional supercharge socket -/

section Supercharge

variable {V : Type*} [AddCommMonoid V]

/--
Explicit socket for the supersymmetric quantum-mechanics relation `Q² = H`.

It is intentionally a predicate: this file does not construct the analytic
Hamiltonian or prove a mass gap.
-/
def SuperchargeSquaresToHamiltonian (Q H : V →+ V) : Prop :=
  Q.comp Q = H

/-- If the supplied supercharge squares to the Hamiltonian, then its square is `H`. -/
theorem supercharge_square_readout
    {Q H : V →+ V} (hQ : SuperchargeSquaresToHamiltonian Q H) :
    Q.comp Q = H :=
  hQ

end Supercharge

end SupersymmetricPrimonGas
