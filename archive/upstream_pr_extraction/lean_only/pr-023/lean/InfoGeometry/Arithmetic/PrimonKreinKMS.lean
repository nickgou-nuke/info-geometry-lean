import Mathlib
import InfoGeometry.Arithmetic.ArithmeticKMS
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Krein.Thermal

/-!
# Primon Krein/KMS Bridge

This module is a compatibility/readout layer for the primon KMS/Krein
dictionary.

It separates:

* finite exterior prime/Fermi partition identities;
* Möbius as square-free fermion parity;
* the positive KMS normalizability guard `1 < β`;
* the direct-sum real doubled Krein carrier;
* a witness-gated KMS boundary law on the doubled Krein operator algebra.

It does not claim a Type III completion, a Tomita--Takesaki theorem for the
finite model, an infinite zeta theorem, or that the Krein supertrace is a
positive state.
-/

noncomputable section

open scoped BigOperators
open scoped InnerProductSpace

namespace InfoGeometry.Arithmetic.PrimonKreinKMS

open InfoGeometry.Arithmetic.ArithmeticKMS
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeSuperalgebra

/-! ## 1. Finite fermionic primon readouts -/

/-- Finite prime cutoff used by the primon/Krein bridge. -/
abbrev PrimeCutoff :=
  PrimeSuperalgebra.PrimeCutoff

/-- Local prime-mode Boltzmann weight `exp(-β log p)`. -/
def primeModeWeight (β : ℝ) (p : ℕ) : ℝ :=
  PrimeSuperalgebra.primeWeight β p

/-- Finite ordinary fermionic square-free partition. -/
def finiteFermionPartition (P : PrimeCutoff) (β : ℝ) : ℝ :=
  PrimeSuperalgebra.finiteFermionicSquarefreePartition P β

/-- Finite signed fermionic/Möbius supertrace. -/
def finiteFermionSupertrace (P : PrimeCutoff) (β : ℝ) : ℝ :=
  PrimeSuperalgebra.finitePrimeSupertrace P β

/--
Finite ordinary fermionic Euler-product identity.

This is the finite square-free precursor of `ζ(s) / ζ(2s)`.
-/
theorem finiteFermionPartition_eq_eulerProduct
    (P : PrimeCutoff) (β : ℝ) :
    finiteFermionPartition P β =
      ∏ p ∈ P.primes, (1 + primeModeWeight β p) := by
  simpa [finiteFermionPartition, primeModeWeight,
    PrimeSuperalgebra.finiteSquarefreeProduct]
    using PrimeSuperalgebra.finiteFermionicSquarefreePartition_eq_product P β

/--
Finite signed fermionic Euler-product identity.

This is the finite square-free/Möbius precursor of `1 / ζ(s)`.
-/
theorem finiteFermionSupertrace_eq_eulerProduct
    (P : PrimeCutoff) (β : ℝ) :
    finiteFermionSupertrace P β =
      ∏ p ∈ P.primes, (1 - primeModeWeight β p) := by
  simpa [finiteFermionSupertrace, primeModeWeight,
    PrimeSuperalgebra.finitePrimeDenominator]
    using PrimeSuperalgebra.finitePrimeSupertrace_eq_denominator P β

/-! ## 2. Möbius as finite Krein/Fock signature -/

/-- Möbius/Krein signature of a finite square-free prime set. -/
def mobiusKreinSignature (S : Finset ℕ) : ℤ :=
  (-1 : ℤ) ^ S.card

/--
Möbius equals fermion/Krein parity on a finite product of distinct prime modes.

The zero clause for nonsquare-free integers is not part of this theorem; it is
owned separately by `PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree`.
-/
theorem mobiusKreinSignature_eq_mobius_primeProduct
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    mobiusKreinSignature S =
      ArithmeticFunction.moebius (∏ p ∈ S, p) := by
  simpa [mobiusKreinSignature] using
    (PrimeBitWittenIndex.mobius_prime_product_eq_parity S hprime).symm

/-! ## 3. Positive KMS normalizability guard -/

/--
Normalizability/convergence guard for the primon Gibbs state.

This is not itself the KMS condition; it is the trace-class/summability gate
for the positive Gibbs state.
-/
def NormalizableBeta (β : ℝ) : Prop :=
  1 < β

/--
Finite arithmetic KMS socket with an explicit primon normalizability guard.

The KMS law is supplied by the existing `ArithmeticKMSWitness` interface.
-/
structure NormalizableArithmeticKMSSocket
    (State : Type*) where
  /-- Finite arithmetic KMS witness. -/
  witness : ArithmeticKMSWitness State
  /-- Finite arithmetic support. -/
  support : Finset ℕ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive Gibbs normalizability guard. -/
  normalizable : NormalizableBeta beta

namespace NormalizableArithmeticKMSSocket

variable {State : Type*}

/-- Encoded finite arithmetic state. -/
def encodedState (S : NormalizableArithmeticKMSSocket State) : State :=
  S.witness.stateOfFinset S.support

end NormalizableArithmeticKMSSocket

/-! ## 4. KMS strip readout -/

/-- The open KMS analytic strip in imaginary-time height coordinates. -/
def KMSAnalyticStrip (β : ℝ) : Set ℝ :=
  Set.Ioo (0 : ℝ) β

/-- The KMS strip has positive height under the primon normalizability guard. -/
theorem KMSAnalyticStrip_nonempty
    {β : ℝ} (hβ : NormalizableBeta β) :
    (KMSAnalyticStrip β).Nonempty := by
  have hβ' : 1 < β := hβ
  refine ⟨β / 2, ?_⟩
  constructor <;> nlinarith [hβ']

/-! ## 5. Real doubled Krein form -/

namespace DoubledKrein

open InfoGeometry.Krein

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real doubled Krein carrier. -/
abbrev H₂ :=
  InfoGeometry.Krein.DoubledSpace E

/-- Real doubled operator algebra. -/
abbrev EndH₂ :=
  H₂ (E := E) →L[ℝ] H₂ (E := E)

/-- Split direct-sum Krein form `[x⊕ξ, y⊕η] = ⟪x,y⟫ - ⟪ξ,η⟫`. -/
def splitDoubledKreinForm
    (u v : H₂ (E := E)) : ℝ :=
  inner ℝ (WithLp.fst u) (WithLp.fst v) -
    inner ℝ (WithLp.snd u) (WithLp.snd v)

omit [CompleteSpace E] in
/-- Coordinate formula for the split doubled Krein form. -/
theorem splitDoubledKreinForm_to_doubled
    (x ξ y η : E) :
    splitDoubledKreinForm
        (InfoGeometry.Krein.to_doubled x ξ : H₂ (E := E))
        (InfoGeometry.Krein.to_doubled y η : H₂ (E := E)) =
      inner ℝ x y - inner ℝ ξ η := by
  rfl

omit [CompleteSpace E] in
/-- The spectral sign flip preserves the split doubled Krein form. -/
theorem spectral_epsilon_preserves_splitDoubledKreinForm
    (u v : H₂ (E := E)) :
    splitDoubledKreinForm
        (InfoGeometry.Krein.spectral_epsilon (E := E) u)
        (InfoGeometry.Krein.spectral_epsilon (E := E) v) =
      splitDoubledKreinForm u v := by
  simp [splitDoubledKreinForm, InfoGeometry.Krein.spectral_epsilon]

omit [CompleteSpace E] in
/-- The modular swap reverses the split doubled Krein form. -/
theorem modular_j_reverses_splitDoubledKreinForm
    (u v : H₂ (E := E)) :
    splitDoubledKreinForm
        (InfoGeometry.Krein.modular_j (E := E) u)
        (InfoGeometry.Krein.modular_j (E := E) v) =
      - splitDoubledKreinForm u v := by
  simp [splitDoubledKreinForm, InfoGeometry.Krein.modular_j,
    sub_eq_add_neg, add_comm]

end DoubledKrein

/-! ## 6. Real doubled Krein/KMS socket -/

open InfoGeometry.Krein

/--
Real doubled Krein/KMS socket.

The KMS-like boundary law is the repository's finite Krein thermal predicate,
not a global Tomita--Takesaki theorem.
-/
structure RealDoubledKreinKMSSocket
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive Gibbs normalizability guard. -/
  normalizable : NormalizableBeta beta
  /-- Doubled modular generator. -/
  generator : DoubledKrein.EndH₂ (E := E)
  /-- Linear readout/state on doubled observables. -/
  state : DoubledKrein.EndH₂ (E := E) →L[ℝ] ℝ
  /-- Repository KMS-like boundary law. -/
  kms : InfoGeometry.Krein.satisfies_kms generator state beta

namespace RealDoubledKreinKMSSocket

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end RealDoubledKreinKMSSocket

/-! ## 7. Combined primon doubled Krein/KMS bridge -/

/--
Combined bridge packet.

The arithmetic KMS socket and doubled Krein socket share the same inverse
temperature, while keeping positive KMS state data separate from indefinite
Krein/supertrace bookkeeping.
-/
structure PrimonDoubledKreinKMSSocket
    (State E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Positive finite arithmetic KMS side. -/
  arithmetic : NormalizableArithmeticKMSSocket State
  /-- Direct-sum doubled Krein/KMS side. -/
  krein : RealDoubledKreinKMSSocket E
  /-- Shared inverse-temperature readout. -/
  beta_agrees : krein.beta = arithmetic.beta

namespace PrimonDoubledKreinKMSSocket

variable
    {State E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The common inverse temperature is in the normalizable primon region. -/
theorem arithmetic_beta_normalizable
    (S : PrimonDoubledKreinKMSSocket State E) :
    NormalizableBeta S.arithmetic.beta :=
  S.arithmetic.normalizable

end PrimonDoubledKreinKMSSocket

end InfoGeometry.Arithmetic.PrimonKreinKMS
