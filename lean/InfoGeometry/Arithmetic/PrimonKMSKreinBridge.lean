import Mathlib.Tactic
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
* the Möbius/signature interpretation is represented by finite or scalar
  readouts; no infinite supertrace, Euler-product, or KMS theorem is derived
  by this file.
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

lemma positiveGibbsWeight_pos
    {State : Type*} (energy : State → ℝ) (β : ℝ) (s : State) :
    0 < positiveGibbsWeight energy β s := by
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

lemma positivePartition_pos
    {State : Type*} [Fintype State] [Nonempty State]
    (energy : State → ℝ) (β : ℝ) :
    0 < positivePartition energy β := by
  unfold positivePartition
  exact Finset.sum_pos (fun s _hs => positiveGibbsWeight_pos energy β s)
    (Finset.univ_nonempty)

lemma finiteGibbsDensity_nonneg
    {State : Type*} [Fintype State]
    (energy : State → ℝ) (β : ℝ) (s : State)
    (hZ : 0 ≤ positivePartition energy β) :
    0 ≤ finiteGibbsDensity energy β s := by
  unfold finiteGibbsDensity
  exact div_nonneg (positiveGibbsWeight_nonneg energy β s) hZ

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

/-
Finite positive Gibbs trace data.
The state and partition are derived, not supplied. In this finite commutative
model the available symmetry is the trace law below; no noncommutative KMS
theorem is asserted here.
-/
abbrev PositiveGibbsTraceData (State : Type*) [Fintype State] :=
  (State → ℝ) × ℝ

/-- Compatibility accessor for the finite Gibbs energy function. -/
abbrev PositiveGibbsTraceData.energy
    {State : Type*} [Fintype State]
    (P : PositiveGibbsTraceData State) : State → ℝ := P.1

/-- Compatibility accessor for the inverse temperature. -/
abbrev PositiveGibbsTraceData.beta
    {State : Type*} [Fintype State]
    (P : PositiveGibbsTraceData State) : ℝ := P.2

namespace PositiveGibbsTraceData

variable {State : Type*} [Fintype State] (P : PositiveGibbsTraceData State)

/-- Derived partition function. -/
def partition : ℝ := positivePartition (energy P) (beta P)

lemma partition_pos [Nonempty State] :
    0 < P.partition := by
  exact positivePartition_pos (energy P) (beta P)

/-- Derived state on observables. -/
def state : (State → ℝ) → ℝ :=
  fun A => (∑ s, (partition P)⁻¹ * positiveGibbsWeight (energy P) (beta P) s * A s)

/--
The finite Gibbs state satisfies the KMS condition in the commutative/diagonal
case: the flow is trivial, and the state is a trace.
-/
theorem commutative_trace_law :
    ∀ A B : State → ℝ, state P (A * B) = state P (B * A) := by
  intro A B
  unfold state
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Pi.mul_apply, Pi.mul_apply]
  ring

end PositiveGibbsTraceData

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

/-! ## 4. Derived data for the infinite/readout layer -/

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

/-
Infinite primon temperature data: only the scalar guard `1 < beta` is stored.
No infinite-volume KMS state is constructed by this file.
-/
abbrev InfinitePrimonTemperatureData := {beta : ℝ // 1 < beta}

namespace InfinitePrimonTemperatureData

/-- Compatibility accessor for the inverse-temperature parameter. -/
abbrev beta (P : InfinitePrimonTemperatureData) : ℝ := P.1

/-- Compatibility accessor for the genuine low-temperature property. -/
abbrev h_beta (P : InfinitePrimonTemperatureData) : 1 < P.beta := P.2


variable (P : InfinitePrimonTemperatureData)

/-- A real positive-lane readout attached to the inverse temperature. -/
def zeta : ℝ := (riemannZeta (P.beta : ℂ)).re

/-- The infinite primon inverse temperature lies above the unit threshold. -/
theorem beta_gt_one : 1 < P.beta :=
  P.h_beta

end InfinitePrimonTemperatureData

/--
Scalar inverse-zeta-labelled readout.  This is not an operator trace or an
infinite supertrace construction.
-/
abbrev InfiniteMobiusKreinReadoutData := {beta : ℝ // 1 < beta}

namespace InfiniteMobiusKreinReadoutData

/-- Compatibility accessor for the inverse-temperature parameter. -/
abbrev beta (C : InfiniteMobiusKreinReadoutData) : ℝ := C.1

/-- Compatibility accessor for the genuine low-temperature property. -/
abbrev h_beta (C : InfiniteMobiusKreinReadoutData) : 1 < C.beta := C.2


variable (C : InfiniteMobiusKreinReadoutData)

/-- A real scalar inverse-zeta readout attached to the inverse temperature;
    it is not identified with a complex reciprocal or a trace. -/
def signedTrace : ℝ := ((riemannZeta (C.beta : ℂ)).re)⁻¹

end InfiniteMobiusKreinReadoutData

/--
Combined doubled Krein primon readout data.
The positive Gibbs trace and indefinite Möbius signature are derived.
-/
structure DoubledKreinPrimonKMSData
    (State : Type*) [Fintype State] where
  /-- Positive finite Gibbs trace lane. -/
  positiveTrace : PositiveGibbsTraceData State
  /-- Indefinite Möbius signature interpretation. -/
  kreinSignature : MobiusKreinSignature State
  /-- Optional inverse-temperature calibration. -/
  infiniteTemperature : Option InfinitePrimonTemperatureData
  /-- Optional infinite Möbius/Krein supertrace calibration. -/
  infiniteMobiusKrein : Option InfiniteMobiusKreinReadoutData

namespace DoubledKreinPrimonKMSData

variable {State : Type*} [Fintype State] (P : DoubledKreinPrimonKMSData State)

omit [Fintype State] in
/--
Thermal doubling reads the Liouvillean with opposite signs on the two copies.
-/
theorem liouvillean_plus_minus_sign_laws
    (energy : State → ℝ) (s : State) :
    doubledLiouvilleEnergy energy (ThermalCopy.plus, s) = energy s ∧
    doubledLiouvilleEnergy energy (ThermalCopy.minus, s) = - energy s := by
  constructor <;> simp [doubledLiouvilleEnergy, ThermalCopy.sign]

end DoubledKreinPrimonKMSData

end InfoGeometry.Arithmetic.PrimonKMSKreinBridge
