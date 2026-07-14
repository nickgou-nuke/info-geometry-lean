import InfoGeometry.Holography.BekensteinHawkingDyadicEntropy

/-!
# Witten--Möbius / Cuntz horizon / Bekenstein--Hawking complement

This module is a theorem-safe finite complement to the holographic/dyadic
entropy bridge.  It packages only already-owned, kernel-checked facts:

* finite prime-bit Möbius parity;
* finite Witten/Möbius cancellation over a nonempty prime register;
* Cuntz-horizon nilpotence and Laplacian reconstruction from the UHF carrier;
* scalar Bekenstein--Hawking area calibration to the two-branch dyadic Massieu
  entropy `log 2`.

No thermodynamic-limit theorem, black-hole information theorem, KMS
classification, or `O(5,5)` theorem is asserted here.
-/

noncomputable section

namespace WittenMobiusBekensteinComplement

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.GrandUnification.UHF
open InfoGeometry.Holography.AdSCFT
open InfoGeometry.Holography.BekensteinHawkingDyadicEntropy
open InfoGeometry.Thermodynamics.FiniteGibbsRelative

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
variable [UHF : UHFAlgebra A]

/--
Finite complement certificate combining the arithmetic and holographic scalar
readouts.

For a nonempty finite prime register and an explicit prime-bit state, we have:

1. Möbius value equals fermion parity;
2. finite Witten supertrace cancellation;
3. Cuntz event-horizon nilpotence;
4. Cuntz Laplacian reconstruction on an arbitrary operator/state `X`;
5. under `area = 4G log 2`, scalar Bekenstein--Hawking entropy equals the
   symmetric two-branch finite Gibbs/Massieu readout.
-/
theorem finite_wittenMobius_cuntzHorizon_bekensteinDyadic
    (P : PrimeRegister) (hP : P.primes.Nonempty) (ψ : PrimeBitState P)
    (X : A) {area G : ℝ} (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyQuantum) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) = fermionParityOfState P ψ ∧
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
    event_horizon (A := A) * event_horizon (A := A) = 0 ∧
    (event_horizon (A := A) * star (event_horizon (A := A)) +
      star (event_horizon (A := A)) * event_horizon (A := A)) * X = X ∧
    bekensteinHawkingEntropy area G =
      massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  exact ⟨
    mobius_representedNatOfState_eq_fermionParity P ψ,
    finite_witten_index_cancel P hP,
    horizon_nilpotence (A := A),
    information_preservation (A := A) X,
    bekensteinHawkingEntropy_eq_twoBranch_massieu hG harea⟩

/--
The same finite complement, with the scalar entropy target written as the dyadic
entropy quantum `log 2`.
-/
theorem finite_wittenMobius_cuntzHorizon_bekensteinLogTwo
    (P : PrimeRegister) (hP : P.primes.Nonempty) (ψ : PrimeBitState P)
    (X : A) {area G : ℝ} (hG : G ≠ 0)
    (harea : area = 4 * G * dyadicEntropyQuantum) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) = fermionParityOfState P ψ ∧
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
    event_horizon (A := A) * event_horizon (A := A) = 0 ∧
    (event_horizon (A := A) * star (event_horizon (A := A)) +
      star (event_horizon (A := A)) * event_horizon (A := A)) * X = X ∧
    bekensteinHawkingEntropy area G = dyadicEntropyQuantum := by
  exact ⟨
    mobius_representedNatOfState_eq_fermionParity P ψ,
    finite_witten_index_cancel P hP,
    horizon_nilpotence (A := A),
    information_preservation (A := A) X,
    bekensteinHawkingEntropy_eq_dyadicEntropyQuantum hG harea⟩

end WittenMobiusBekensteinComplement

end noncomputable section
