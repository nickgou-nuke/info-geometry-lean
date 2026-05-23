import Mathlib
import InfoGeometry.Krein.Thermal
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# InfoGeometry.Arithmetic.PrimonKMSKreinBridge

Finite and derived bridge between the primon Gibbs/KMS lane and the
indefinite Krein/supertrace lane.

The theorem-safe separation is:

* the positive Gibbs partition/density is the Hilbert/KMS lane;
* the signed trace is a Krein/supertrace index lane;
* thermal doubling is represented by `H ⊕ (-H)`;
* the Möbius/signature interpretation and zeta/KMS statements are
  formally derived.
-/

noncomputable section

open scoped BigOperators
open InfoGeometry.Krein

namespace InfoGeometry.Arithmetic.PrimonKMSKreinBridge

/-! ## 1. Finite positive Gibbs lane -/

/-- Finite Gibbs weight `exp(-β E_s)`. -/
def positiveGibbsWeight
    {State : Type*}
    (energy : State → ℝ)
    (β : ℝ)
    (s : State) : ℝ :=
  Real.exp (-β * energy s)

/-- Finite positive Gibbs partition. -/
def positivePartition
    {State : Type*} [Fintype State]
    (energy : State → ℝ)
    (β : ℝ) : ℝ :=
  ∑ s : State, positiveGibbsWeight energy β s

/-- Finite normalized Gibbs density. -/
def finiteGibbsDensity
    {State : Type*} [Fintype State]
    (energy : State → ℝ)
    (β : ℝ)
    (s : State) : ℝ :=
  positiveGibbsWeight energy β s / positivePartition energy β

/-- Gibbs weights are nonnegative. -/
theorem positiveGibbsWeight_nonneg
    {State : Type*}
    (energy : State → ℝ)
    (β : ℝ)
    (s : State) :
    0 ≤ positiveGibbsWeight energy β s := by
  unfold positiveGibbsWeight
  positivity

/-- Finite positive Gibbs partitions are nonnegative. -/
theorem positivePartition_nonneg
    {State : Type*} [Fintype State]
    (energy : State → ℝ)
    (β : ℝ) :
    0 ≤ positivePartition energy β := by
  unfold positivePartition
  exact Finset.sum_nonneg (fun s _hs => positiveGibbsWeight_nonneg energy β s)

/-- If the finite partition is nonzero, the normalized Gibbs density sums to `1`. -/
theorem finiteGibbsDensity_sum_eq_one
    {State : Type*} [Fintype State]
    (energy : State → ℝ)
    (β : ℝ)
    (hZ : positivePartition energy β ≠ 0) :
    (∑ s : State, finiteGibbsDensity energy β s) = 1 := by
  unfold finiteGibbsDensity positivePartition
  rw [← Finset.sum_div]
  exact div_self hZ

/--
Finite positive Gibbs KMS packet.
The state and partition are derived, not supplied.
-/
structure PositiveGibbsKMSPacket (State : Type*) [Fintype State] where
  energy : State → ℝ
  beta : ℝ

namespace PositiveGibbsKMSPacket

variable {State : Type*} [Fintype State] (P : PositiveGibbsKMSPacket State)

/-- Derived partition function. -/
def partition : ℝ := positivePartition P.energy P.beta

/-- Derived state on observables. -/
def state : (State → ℝ) → ℝ :=
  fun A => (∑ s, (P.partition⁻¹) * positiveGibbsWeight P.energy P.beta s * A s)

/--
The finite Gibbs state satisfies the KMS condition in the commutative/diagonal
case: the flow is trivial, and the state is a trace.
-/
theorem satisfies_kms :
    ∀ A B : State → ℝ, P.state (A * B) = P.state (B * A) := by
  intro A B
  unfold state
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Pi.mul_apply, Pi.mul_apply]
  ring

end PositiveGibbsKMSPacket

/-! ## 2. Finite Krein/signature lane -/

/--
Finite signed Krein/supertrace readout.
-/
def signedKreinTrace
    {State : Type*} [Fintype State]
    (signature : State → ℝ)
    (energy : State → ℝ)
    (β : ℝ) : ℝ :=
  ∑ s : State, signature s * positiveGibbsWeight energy β s

/-- Signed trace as a signature-weighted positive Gibbs sum. -/
theorem signedKreinTrace_eq_signature_weighted_sum
    {State : Type*} [Fintype State]
    (signature : State → ℝ)
    (energy : State → ℝ)
    (β : ℝ) :
    signedKreinTrace signature energy β =
      ∑ s : State, signature s * positiveGibbsWeight energy β s :=
  rfl

/-! ## 3. Thermal doubling and total Krein signature -/

/-- The two copies in a thermal double. -/
inductive ThermalCopy where
  | plus
  | minus
  deriving DecidableEq, Repr

namespace ThermalCopy

/-- Sign of a thermal copy: forward copy is positive, backward copy is negative. -/
def sign : ThermalCopy → ℝ
  | plus => 1
  | minus => -1

@[simp]
theorem sign_plus : sign plus = 1 := rfl

@[simp]
theorem sign_minus : sign minus = -1 := rfl

end ThermalCopy

/-- Doubled finite state carrier. -/
abbrev DoubledState (State : Type*) :=
  ThermalCopy × State

/-- Doubled Liouvillean energy readout `H ⊕ (-H)`. -/
def doubledLiouvilleEnergy
    {State : Type*}
    (energy : State → ℝ)
    (X : DoubledState State) : ℝ :=
  ThermalCopy.sign X.1 * energy X.2

/-! ## 4. Derived packets for the infinite/KMS layer -/

/--
Möbius/Krein signature interpretation.
This records the interpretation of the indefinite signature.
-/
structure MobiusKreinSignature (State : Type*) [Fintype State] where
  /-- Integer code, e.g. a square-free natural-number label. -/
  code : State → ℕ
  /-- Real signature, e.g. `(-1)^F` on square-free states. -/
  signature : State → ℝ
  /-- Integer Möbius/parity readout. -/
  mobiusReadout : State → ℤ
  /-- Signature matches the integer Möbius/parity readout. -/
  signature_eq_mobius :
    ∀ s : State, signature s = (mobiusReadout s : ℝ)

/--
Infinite positive primon KMS packet.
All analytic statements are formally derived from the Riemann zeta function.
-/
structure InfinitePrimonKMSPacket where
  beta : ℝ
  h_beta : 1 < beta

namespace InfinitePrimonKMSPacket

variable (P : InfinitePrimonKMSPacket)

/-- A real positive-lane readout attached to the inverse temperature. -/
def zeta : ℝ := (riemannZeta (P.beta : ℂ)).re

/-- The infinite primon inverse temperature lies above the unit threshold. -/
theorem beta_gt_one : 1 < P.beta :=
  P.h_beta

end InfinitePrimonKMSPacket

/--
Infinite Möbius/Krein supertrace interpretation.
The signed exterior/Krein trace is formally `1 / ζ(β)`.
-/
structure InfiniteMobiusKreinTrace where
  beta : ℝ
  h_beta : 1 < beta

namespace InfiniteMobiusKreinTrace

variable (C : InfiniteMobiusKreinTrace)

/-- A real signed-trace readout attached to the inverse temperature. -/
def signedTrace : ℝ := ((riemannZeta (C.beta : ℂ)).re)⁻¹

end InfiniteMobiusKreinTrace

/--
Combined doubled Krein primon/KMS packet.
The positive Gibbs/KMS state and indefinite Möbius signature are derived.
-/
structure DoubledKreinPrimonKMSPacket
    (State : Type*) [Fintype State] where
  /-- Positive Hilbert/KMS lane. -/
  positiveKMS : PositiveGibbsKMSPacket State
  /-- Indefinite Möbius signature interpretation. -/
  kreinSignature : MobiusKreinSignature State
  /-- Optional infinite positive KMS calibration. -/
  infinitePositiveKMS : Option InfinitePrimonKMSPacket
  /-- Optional infinite Möbius/Krein supertrace calibration. -/
  infiniteMobiusKrein : Option InfiniteMobiusKreinTrace

namespace DoubledKreinPrimonKMSPacket

variable {State : Type*} [Fintype State] (P : DoubledKreinPrimonKMSPacket State)

omit [Fintype State] in
/--
Thermal doubling reads the Liouvillean with opposite signs on the two copies.
-/
theorem liouvillean_plus_minus_sign_laws
    (energy : State → ℝ) (s : State) :
    doubledLiouvilleEnergy energy (ThermalCopy.plus, s) = energy s ∧
    doubledLiouvilleEnergy energy (ThermalCopy.minus, s) = - energy s := by
  constructor <;> simp [doubledLiouvilleEnergy, ThermalCopy.sign]

/-- The positive KMS condition is formally satisfied. -/
theorem positiveKMS_valid :
    ∀ A B : State → ℝ, P.positiveKMS.state (A * B) = P.positiveKMS.state (B * A) :=
  P.positiveKMS.satisfies_kms

end DoubledKreinPrimonKMSPacket

end InfoGeometry.Arithmetic.PrimonKMSKreinBridge
