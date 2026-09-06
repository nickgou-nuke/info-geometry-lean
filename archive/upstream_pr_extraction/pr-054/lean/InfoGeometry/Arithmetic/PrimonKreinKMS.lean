import Mathlib.Tactic
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
* a property-gated KMS boundary law on the doubled Krein operator algebra.

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

lemma primeModeWeight_pos (β : ℝ) (p : ℕ) :
    0 < primeModeWeight β p := by
  unfold primeModeWeight PrimeSuperalgebra.primeWeight
  exact Real.exp_pos _

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

/--
The finite signed Krein/Möbius readout cancels the finite bosonic partition.

This is the finite algebraic counterpart of the Möbius inverse identity.  It
does not assert an infinite Euler product or identify a signed supertrace
with a positive KMS state.
-/
theorem finiteFermionSupertrace_mul_finiteBosonicPrimePartition_eq_one
    (P : PrimeCutoff) (β : ℝ)
    (hdenom : PrimeSuperalgebra.finitePrimeDenominator P β ≠ 0) :
    finiteFermionSupertrace P β *
        PrimeSuperalgebra.finiteBosonicPrimePartition P β = 1 := by
  simpa [finiteFermionSupertrace] using
    PrimeSuperalgebra.finitePrimeSupertrace_mul_finiteBosonicPrimePartition_eq_one
      P β hdenom

lemma finiteFermionPartition_pos (P : PrimeCutoff) (β : ℝ) :
    0 < finiteFermionPartition P β := by
  rw [finiteFermionPartition_eq_eulerProduct]
  exact Finset.prod_pos (fun p _hp => by
    exact add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (primeModeWeight_pos β p)))

lemma finiteFermionPartition_ne_zero (P : PrimeCutoff) (β : ℝ) :
    finiteFermionPartition P β ≠ 0 :=
  (finiteFermionPartition_pos P β).ne'

lemma finiteFermionSupertrace_ne_zero
    (P : PrimeCutoff) (β : ℝ)
    (h : ∀ p ∈ P.primes, (1 - primeModeWeight β p) ≠ 0) :
    finiteFermionSupertrace P β ≠ 0 := by
  rw [finiteFermionSupertrace_eq_eulerProduct]
  exact Finset.prod_ne_zero_iff.mpr h

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

/-- The normalizable region places every prime-mode weight strictly below one. -/
lemma primeModeWeight_lt_one_of_normalizable
    {β : ℝ} (hβ : NormalizableBeta β)
    {p : ℕ} (hp : Nat.Prime p) :
    primeModeWeight β p < 1 := by
  have hβ0 : 1 < β := hβ
  have hβ' : 0 < β := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  unfold primeModeWeight PrimeSuperalgebra.primeWeight
  apply Real.exp_lt_one_iff.mpr
  have hprod : 0 < β * Real.log (p : ℝ) := mul_pos hβ' hlogp
  have hneg : -(β * Real.log (p : ℝ)) < 0 := neg_lt_zero.mpr hprod
  simpa [PrimeSuperalgebra.primeEnergy] using hneg

/-- The signed finite supertrace is positive in the normalizable region. -/
lemma finiteFermionSupertrace_pos_of_normalizable
    (P : PrimeCutoff) {β : ℝ} (hβ : NormalizableBeta β) :
    0 < finiteFermionSupertrace P β := by
  rw [finiteFermionSupertrace_eq_eulerProduct]
  apply Finset.prod_pos
  intro p hp
  exact sub_pos.mpr
    (primeModeWeight_lt_one_of_normalizable hβ (P.prime_mem p hp))

/-- The finite boson/signed-supertrace cancellation needs no extra
nonvanishing hypothesis once the normalizable region is supplied. -/
theorem finiteFermionSupertrace_mul_finiteBosonicPrimePartition_eq_one_of_normalizable
    (P : PrimeCutoff) {β : ℝ} (hβ : NormalizableBeta β) :
    finiteFermionSupertrace P β *
        PrimeSuperalgebra.finiteBosonicPrimePartition P β = 1 := by
  have htrace : 0 < finiteFermionSupertrace P β :=
    finiteFermionSupertrace_pos_of_normalizable P hβ
  have hdenom : PrimeSuperalgebra.finitePrimeDenominator P β ≠ 0 := by
    have hdenom_eq :
        PrimeSuperalgebra.finitePrimeDenominator P β =
          finiteFermionSupertrace P β := by
      symm
      simpa [finiteFermionSupertrace] using
        PrimeSuperalgebra.finitePrimeSupertrace_eq_denominator P β
    rw [hdenom_eq]
    exact htrace.ne'
  exact finiteFermionSupertrace_mul_finiteBosonicPrimePartition_eq_one P β
    hdenom

/--
Finite arithmetic KMS interface with an explicit primon normalizability guard.

The KMS law is supplied by the existing `ArithmeticKMSData` interface.
-/
structure NormalizableArithmeticKMSData
    (State : Type*) where
  /-- Finite arithmetic KMS property. -/
  property : ArithmeticKMSData State
  /-- Finite arithmetic support. -/
  support : Finset ℕ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive Gibbs normalizability guard. -/
  normalizable : NormalizableBeta beta

namespace NormalizableArithmeticKMSData

variable {State : Type*}

/-- Encoded finite arithmetic state. -/
def encodedState (S : NormalizableArithmeticKMSData State) : State :=
  S.property.stateOfFinset S.support

end NormalizableArithmeticKMSData

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

/-! ## 6. Real doubled Krein/KMS interface -/

open InfoGeometry.Krein

/--
Real doubled Krein/KMS interface.

The KMS-like boundary law is the repository's finite Krein thermal predicate,
not a global Tomita--Takesaki theorem.
-/
structure RealDoubledKreinKMSData
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

namespace RealDoubledKreinKMSData

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end RealDoubledKreinKMSData

/-! ## 7. Combined primon doubled Krein/KMS bridge -/

/--
Combined bridge packet.

The arithmetic KMS interface and doubled Krein interface share the same inverse
temperature, while keeping positive KMS state data separate from indefinite
Krein/supertrace bookkeeping.
-/
structure PrimonDoubledKreinKMSData
    (State E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Positive finite arithmetic KMS side. -/
  arithmetic : NormalizableArithmeticKMSData State
  /-- Direct-sum doubled Krein/KMS side. -/
  krein : RealDoubledKreinKMSData E
  /-- Shared inverse-temperature readout. -/
  beta_agrees : krein.beta = arithmetic.beta

namespace PrimonDoubledKreinKMSData

variable
    {State E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The common inverse temperature is in the normalizable primon region. -/
theorem arithmetic_beta_normalizable
    (S : PrimonDoubledKreinKMSData State E) :
    NormalizableBeta S.arithmetic.beta :=
  S.arithmetic.normalizable

end PrimonDoubledKreinKMSData

end InfoGeometry.Arithmetic.PrimonKreinKMS
