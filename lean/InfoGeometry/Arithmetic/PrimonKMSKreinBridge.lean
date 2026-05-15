import Mathlib

/-!
# InfoGeometry.Arithmetic.PrimonKMSKreinBridge

Finite and witness-gated bridge between the primon Gibbs/KMS lane and the
indefinite Krein/supertrace lane.

The theorem-safe separation is:

* the positive Gibbs partition/density is the Hilbert/KMS lane;
* the signed trace is a Krein/supertrace index lane;
* thermal doubling is represented by `H ⊕ (-H)`;
* the Möbius/signature interpretation and infinite zeta/KMS statements are
  supplied by witnesses.

This file does not prove an infinite trace-class theorem, a Tomita--Takesaki
theorem, an Euler product, analytic continuation, or a zeta-zero statement.
-/

noncomputable section

open scoped BigOperators

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

/-! ## 2. Finite Krein/signature lane -/

/--
Finite signed Krein/supertrace readout.

The `signature` may encode a fermion parity, a Möbius sign on square-free
states, or another supplied indefinite metric signature.  It is not required
to be positive.
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

/-- Finite thermofield norm-square readout equals the positive partition. -/
def finiteThermofieldNormSq
    {State : Type*} [Fintype State]
    (energy : State → ℝ)
    (β : ℝ) : ℝ :=
  positivePartition energy β

/-- The finite thermofield norm-square readout is the finite Gibbs partition. -/
theorem finiteThermofieldNormSq_eq_positivePartition
    {State : Type*} [Fintype State]
    (energy : State → ℝ)
    (β : ℝ) :
    finiteThermofieldNormSq energy β = positivePartition energy β :=
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

/-- Total doubled signature `Γ ⊕ (-Γ)`. -/
def doubledKreinSignature
    {State : Type*}
    (signature : State → ℝ)
    (X : DoubledState State) : ℝ :=
  ThermalCopy.sign X.1 * signature X.2

@[simp]
theorem doubledLiouvilleEnergy_plus
    {State : Type*}
    (energy : State → ℝ)
    (s : State) :
    doubledLiouvilleEnergy energy (ThermalCopy.plus, s) = energy s := by
  simp [doubledLiouvilleEnergy]

@[simp]
theorem doubledLiouvilleEnergy_minus
    {State : Type*}
    (energy : State → ℝ)
    (s : State) :
    doubledLiouvilleEnergy energy (ThermalCopy.minus, s) = -energy s := by
  simp [doubledLiouvilleEnergy]

@[simp]
theorem doubledKreinSignature_plus
    {State : Type*}
    (signature : State → ℝ)
    (s : State) :
    doubledKreinSignature signature (ThermalCopy.plus, s) = signature s := by
  simp [doubledKreinSignature]

@[simp]
theorem doubledKreinSignature_minus
    {State : Type*}
    (signature : State → ℝ)
    (s : State) :
    doubledKreinSignature signature (ThermalCopy.minus, s) = -signature s := by
  simp [doubledKreinSignature]

/-! ## 4. Witness sockets for the infinite/KMS/Möbius layer -/

/--
Positive Gibbs/KMS witness.

The KMS law is supplied as a certificate.  The positivity lane is intentionally
separate from the Krein signature lane.
-/
structure PositiveGibbsKMSWitness
    (State : Type*) [Fintype State] where
  /-- Energy readout. -/
  energy : State → ℝ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Partition readout. -/
  partition : ℝ
  /-- Partition calibration. -/
  partition_eq : partition = positivePartition energy beta
  /-- Normalizability/nonzero partition certificate. -/
  partition_ne_zero : partition ≠ 0
  /-- Model-specific KMS condition. -/
  IsKMSState : Prop
  /-- Certificate for the supplied KMS condition. -/
  kmsCertificate : IsKMSState

namespace PositiveGibbsKMSWitness

variable {State : Type*} [Fintype State]

/-- The supplied KMS condition is available. -/
theorem kms_valid
    (W : PositiveGibbsKMSWitness State) :
    W.IsKMSState :=
  W.kmsCertificate

/-- The finite Gibbs density of the supplied positive state sums to `1`. -/
theorem density_sum_eq_one
    (W : PositiveGibbsKMSWitness State) :
    (∑ s : State, finiteGibbsDensity W.energy W.beta s) = 1 := by
  exact finiteGibbsDensity_sum_eq_one W.energy W.beta
    (by
      intro h
      exact W.partition_ne_zero (by
        rw [W.partition_eq]
        exact h))

end PositiveGibbsKMSWitness

/--
Möbius/Krein signature witness.

This records the interpretation of the indefinite signature as a supplied
Möbius/parity readout.  It does not turn the signed trace into a positive KMS
state.
-/
structure MobiusKreinSignatureWitness
    (State : Type*) [Fintype State] where
  /-- Integer code, e.g. a square-free natural-number label. -/
  code : State → ℕ
  /-- Real signature, e.g. `(-1)^F` on square-free states. -/
  signature : State → ℝ
  /-- Integer Möbius/parity readout supplied by the finite arithmetic owner. -/
  mobiusReadout : State → ℤ
  /-- Signature calibration to the integer Möbius/parity readout. -/
  signature_eq_mobiusReadout :
    ∀ s : State, signature s = (mobiusReadout s : ℝ)
  /-- Guardrail: the signed trace is not a positive state. -/
  notPositiveKMSStateWitness : Type*

namespace MobiusKreinSignatureWitness

variable {State : Type*} [Fintype State]

/-- Re-export the supplied signature/Möbius calibration. -/
theorem signature_eq_mobius
    (W : MobiusKreinSignatureWitness State)
    (s : State) :
    W.signature s = (W.mobiusReadout s : ℝ) :=
  W.signature_eq_mobiusReadout s

end MobiusKreinSignatureWitness

/--
Infinite primon Gibbs/KMS calibration socket.

This is the analytic lane behind the slogan
`β > 1 ↔ ζ(β) < ∞ ↔ thermofield normalizable ↔ Gibbs density trace-class`.
All analytic statements are supplied as laws/certificates.
-/
structure InfinitePrimonKMSCalibration where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Zeta/partition readout. -/
  zeta : ℝ
  /-- Unnormalized thermofield norm-square readout. -/
  thermofieldNormSq : ℝ
  /-- Trace-class / normalizability domain, e.g. `1 < beta`. -/
  BetaAdmissible : Prop
  /-- Certificate for the admissible half-plane/temperature domain. -/
  betaAdmissibleCertificate : BetaAdmissible
  /-- Supplied equality `Z(β) = ζ(β)` for the positive Gibbs lane. -/
  partition_eq_zeta : Prop
  /-- Certificate of the positive partition/zeta calibration. -/
  partition_eq_zeta_certificate : partition_eq_zeta
  /-- Supplied thermofield norm-square/zeta calibration. -/
  thermofieldNormSq_eq_zeta : thermofieldNormSq = zeta
  /-- Supplied trace-class normalizability law for the Gibbs density. -/
  traceClassGibbsLaw : Prop
  /-- Certificate for the trace-class normalizability law. -/
  traceClassGibbsCertificate : traceClassGibbsLaw
  /-- Supplied KMS law for the positive Gibbs state. -/
  positiveKMSLaw : Prop
  /-- Certificate for the positive KMS law. -/
  positiveKMSCertificate : positiveKMSLaw
  /-- Guardrail: this calibration is not a signed/Krein state. -/
  signedTraceNotPositiveStateWitness : Type*
  /-- Guardrail: no zeta-zero statement is proved here. -/
  noZetaZeroClaim : Type*

namespace InfinitePrimonKMSCalibration

/-- Re-export the supplied admissible domain certificate. -/
theorem beta_admissible
    (C : InfinitePrimonKMSCalibration) :
    C.BetaAdmissible :=
  C.betaAdmissibleCertificate

/-- Re-export the supplied partition/zeta calibration. -/
theorem partition_eq_zeta_valid
    (C : InfinitePrimonKMSCalibration) :
    C.partition_eq_zeta :=
  C.partition_eq_zeta_certificate

/-- Re-export the supplied thermofield norm-square/zeta calibration. -/
theorem thermofieldNormSq_eq_zeta_valid
    (C : InfinitePrimonKMSCalibration) :
    C.thermofieldNormSq = C.zeta :=
  C.thermofieldNormSq_eq_zeta

/-- Re-export the supplied trace-class Gibbs law. -/
theorem traceClassGibbs_valid
    (C : InfinitePrimonKMSCalibration) :
    C.traceClassGibbsLaw :=
  C.traceClassGibbsCertificate

/-- Re-export the supplied positive KMS law. -/
theorem positiveKMS_valid
    (C : InfinitePrimonKMSCalibration) :
    C.positiveKMSLaw :=
  C.positiveKMSCertificate

end InfinitePrimonKMSCalibration

/--
Infinite Möbius/Krein supertrace calibration socket.

This is the analytic lane behind the slogan that the signed exterior/Krein
trace is `1 / ζ(β)`. It is not a positive Gibbs/KMS state.
-/
structure InfiniteMobiusKreinTraceCalibration where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Zeta/positive partition readout. -/
  zeta : ℝ
  /-- Signed Krein/supertrace readout. -/
  signedTrace : ℝ
  /-- Supplied inverse-zeta calibration for the signed trace. -/
  signedTrace_eq_inv_zeta : signedTrace = zeta⁻¹
  /-- Supplied nonzero zeta certificate for the reciprocal expression. -/
  zeta_ne_zero : zeta ≠ 0
  /-- Guardrail: signed trace is an index/supertrace, not a positive state. -/
  signedTraceNotPositiveStateWitness : Type*
  /-- Guardrail: no analytic continuation or zero-location theorem is proved here. -/
  noZeroLocationClaim : Type*

namespace InfiniteMobiusKreinTraceCalibration

/-- Re-export the supplied inverse-zeta signed-trace calibration. -/
theorem signedTrace_eq_inv_zeta_valid
    (C : InfiniteMobiusKreinTraceCalibration) :
    C.signedTrace = C.zeta⁻¹ :=
  C.signedTrace_eq_inv_zeta

/-- Re-export the supplied nonzero-zeta certificate. -/
theorem zeta_ne_zero_valid
    (C : InfiniteMobiusKreinTraceCalibration) :
    C.zeta ≠ 0 :=
  C.zeta_ne_zero

end InfiniteMobiusKreinTraceCalibration

/--
Combined doubled Krein primon/KMS packet.

The positive Gibbs/KMS state and indefinite Möbius signature are kept as
separate fields.
-/
structure DoubledKreinPrimonKMSPacket
    (State : Type*) [Fintype State] where
  /-- Positive Hilbert/KMS lane. -/
  positiveKMS : PositiveGibbsKMSWitness State
  /-- Indefinite Möbius/Krein lane. -/
  kreinSignature : MobiusKreinSignatureWitness State
  /-- Supplied law that the doubled Liouvillean preserves the intended Krein form. -/
  liouvilleanKreinSelfAdjointLaw : Prop
  /-- Certificate for Krein self-adjointness/preservation. -/
  liouvilleanKreinSelfAdjointCertificate :
    liouvilleanKreinSelfAdjointLaw
  /-- Optional infinite positive Gibbs/KMS calibration. -/
  infinitePositiveKMS : Option InfinitePrimonKMSCalibration
  /-- Optional infinite signed Möbius/Krein trace calibration. -/
  infiniteSignedKreinTrace : Option InfiniteMobiusKreinTraceCalibration
  /-- Guardrail: no infinite trace-class theorem is proved here. -/
  noInfiniteTraceClassClaim : Type*
  /-- Guardrail: no Euler-product theorem is proved here. -/
  noEulerProductClaim : Type*
  /-- Guardrail: no zeta-zero statement is proved here. -/
  noZetaZeroClaim : Type*

namespace DoubledKreinPrimonKMSPacket

variable {State : Type*} [Fintype State]

/-- The supplied Krein self-adjointness/preservation law is available. -/
theorem liouvilleanKreinSelfAdjoint_valid
    (P : DoubledKreinPrimonKMSPacket State) :
    P.liouvilleanKreinSelfAdjointLaw :=
  P.liouvilleanKreinSelfAdjointCertificate

/-- Positive KMS certificate from the positive Hilbert lane. -/
theorem positiveKMS_valid
    (P : DoubledKreinPrimonKMSPacket State) :
    P.positiveKMS.IsKMSState :=
  P.positiveKMS.kms_valid

end DoubledKreinPrimonKMSPacket

end InfoGeometry.Arithmetic.PrimonKMSKreinBridge
