import InfoGeometry.Core.Entropy
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.LogDetRadonNikodymMechanism
import InfoGeometry.Geometry.LegendreHessianInverse
import InfoGeometry.LLM.KMSSoftmaxBridge
import InfoGeometry.Meta.Architecture

/-!
# Modular Surprisal Thermodynamic Packet

Conservative theorem packet for the prose bridge:

* classical surprisal is negative log-density;
* projective relative modular potential is negative relative log-density;
* finite KMS/router thermodynamics has a Massieu/free-energy surface;
* smooth Legendre inverse-Hessian claims are exposed only through the existing
  proof-carrying `LegendreHessianInverseContext`;
* Type III modular Hamiltonian language is represented by an explicit context,
  not by an unsupported global logarithm theorem.

This file deliberately does not prove a cosmological-constant theorem, a full
Tomita logarithm theorem, or an infinite-dimensional Hessian theorem.
-/

namespace InfoGeometry.Canonical.ModularSurprisalThermoPacket

open scoped BigOperators

section ClassicalSurprisal

variable {α : Type*}

/-- Classical surprisal is the negative logarithmic density. -/
@[rep_depth thermo]
theorem classical_surprisal_eq_neg_logDensity
    (P : ProbabilityDist α) (x : α) :
    InfoGeometry.surprisal P x = -InfoGeometry.logDensity P x :=
  InfoGeometry.Core.surprisal_def P x

end ClassicalSurprisal

section RelativeModularPotential

variable {α : Type*}

/-- Representative modular potential is the negative relative logarithmic density. -/
@[rep_depth projective]
theorem representativeModularPotential_eq_negative_relativeLogDensity
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential μ ν a =
      -InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity μ ν a :=
  InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_eq_neg_representativeRelativeLogDensity
    μ ν a

variable [Fintype α] [Nonempty α]

/-- Projective modular potential is the negative relative logarithmic density. -/
@[rep_depth projective]
theorem relativeModularPotential_eq_negative_relativeLogDensity
    (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α) (a : α) :
    InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential q q0 a =
      -InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity q q0 a :=
  InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_eq_neg_relativeLogDensity
    q q0 a

end RelativeModularPotential

section FiniteKMSMassieu

variable {Tok V : Type*}
variable [NormedAddCommGroup V]

/-- Finite KMS/router log-partition is the Massieu potential on the router slice. -/
@[rep_depth thermo]
theorem kmsLogPartition_eq_routerMassieu
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) :
    InfoGeometry.LLM.KMSSoftmaxBridge.kmsLogPartition n β x i =
      InfoGeometry.LLM.RouterFreeEnergyBridge.routerMassieu n β x i :=
  rfl

/-- Finite KMS/free-energy relation `βF = -ψ` for nonzero inverse temperature. -/
@[rep_depth thermo]
theorem finiteKMS_beta_mul_freeEnergy_eq_neg_massieu
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * InfoGeometry.LLM.RouterFreeEnergyBridge.routerFreeEnergy n β x i =
      -InfoGeometry.LLM.RouterFreeEnergyBridge.routerMassieu n β x i :=
  InfoGeometry.LLM.RouterFreeEnergyBridge.beta_mul_routerFreeEnergy_eq_neg_routerMassieu
    (n := n) (β := β) (x := x) (i := i) hβ

/-- Finite KMS/free-energy relation using the KMS log-partition name. -/
@[rep_depth thermo]
theorem finiteKMS_beta_mul_freeEnergy_eq_neg_logPartition
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * InfoGeometry.LLM.RouterFreeEnergyBridge.routerFreeEnergy n β x i =
      -InfoGeometry.LLM.KMSSoftmaxBridge.kmsLogPartition n β x i :=
  InfoGeometry.LLM.KMSSoftmaxBridge.beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition
    (n := n) (β := β) (x := x) (i := i) hβ

end FiniteKMSMassieu

section LegendreInverse

variable {Θ : Type _}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Smooth Legendre/Fisher inverse-Hessian packet, delegated to the existing
proof-carrying context. This is not an inverse-function theorem.
-/
@[rep_depth thermo]
theorem legendre_fisher_entropy_inverse_packet
    (C : InfoGeometry.Geometry.LegendreHessianInverseContext Θ) :
    C.moment = InfoGeometry.Geometry.dualCoord C.massieu C.beta
      ∧ C.entropyGradient C.moment = C.beta
      ∧ C.fisherHessian = InfoGeometry.Geometry.hessian C.massieu C.beta
      ∧ C.entropyHessian = fderiv ℝ C.entropyGradient C.moment
      ∧ C.entropyHessian.comp C.fisherHessian = ContinuousLinearMap.id ℝ Θ
      ∧ C.fisherHessian.comp C.entropyHessian =
          ContinuousLinearMap.id ℝ (InfoGeometry.Geometry.MomentCoord Θ) :=
  C.legendre_hessian_inverse_packet

end LegendreInverse

section OperatorialModularHamiltonian

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/--
Explicit Type III / Tomita modular-Hamiltonian interface.

`negativeLogModularOperator` is supplied as data because this repo does not
own a global unbounded functional calculus theorem for `-log Δ` on a Type III
factor. Concrete Tomita/KMS models should instantiate this context.
-/
@[rep_depth operator]
abbrev ModularHamiltonianSurprisalContext
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  (H →L[ℝ] H) × (H →L[ℝ] H)

namespace ModularHamiltonianSurprisalContext

variable (C : ModularHamiltonianSurprisalContext (H := H))

/-- Supplied modular operator. -/
def modularOperator : H →L[ℝ] H :=
  C.1

/--
Supplied negative-log operator.  Its functional-calculus relation to
`modularOperator` remains an explicit analytic obligation of concrete models.
-/
def negativeLogModularOperator : H →L[ℝ] H :=
  C.2

/--
Historical modular-Hamiltonian name for the operator-valued negative logarithm.
The negative-log operator is the unique stored owner.
-/
@[rep_depth operator]
abbrev modularHamiltonian : H →L[ℝ] H :=
  C.negativeLogModularOperator

/-- State-surprisal operator attached to the supplied modular operator. -/
@[rep_depth operator]
def stateSurprisalOperator : H →L[ℝ] H :=
  C.negativeLogModularOperator

@[simp]
theorem stateSurprisalOperator_eq_negativeLogModularOperator :
    C.stateSurprisalOperator = C.negativeLogModularOperator :=
  rfl

/-- The historical modular-Hamiltonian alias is definitionally the negative log. -/
@[simp, rep_depth operator]
theorem modularHamiltonian_eq_negativeLog :
    C.modularHamiltonian = C.negativeLogModularOperator :=
  rfl

/-- The modular Hamiltonian is the supplied negative-log modular operator. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_supplied_negativeLog :
    C.modularHamiltonian = C.negativeLogModularOperator :=
  C.modularHamiltonian_eq_negativeLog

/-- The historical modular-Hamiltonian name is exactly the state-surprisal operator. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_stateSurprisalOperator :
    C.modularHamiltonian = C.stateSurprisalOperator := by
  rw [stateSurprisalOperator_eq_negativeLogModularOperator,
    modularHamiltonian_eq_supplied_negativeLog]

end ModularHamiltonianSurprisalContext

end OperatorialModularHamiltonian

section OperatorialDrazinCentralSplit

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/--
The operatorial central channel is the repo-owned Drazin defect extraction,
not a scalar phase or scalar central charge.
-/
@[rep_depth operator]
theorem canonicalDefectCentral_is_operatorial_drazin_lane_central
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentral
      CIK
      (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral CIK) :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral_isDrazinLaneCentral
    (CIK := CIK)

/--
The same canonical central channel is supported on the Drazin defect block.
-/
@[rep_depth operator]
theorem canonicalDefectCentral_is_operatorial_defect_supported
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupported
      CIK
      (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral CIK) :=
  InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral_isDefectSupported
    (CIK := CIK)

end OperatorialDrazinCentralSplit

section DefectiveLogRadonNikodym

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/--
Defective logarithmic Radon-Nikodym descent is already owned as an additive
potential plus additive anomaly. This keeps the prose "negative log RN"
mechanism in the multiplicative-to-additive corridor instead of inventing a
trace-density formula.
-/
@[rep_depth transport]
theorem defectiveLogPotential_chain_rule_packet
    (B : InfoGeometry.Canonical.DefectiveMultiplicativeToAdditiveBridge
      M S A)
    (x y : M) :
    InfoGeometry.Canonical.LogDetRadonNikodymMechanism.DefectiveLogPotential B (x * y)
      =
      InfoGeometry.Canonical.LogDetRadonNikodymMechanism.DefectiveAnomaly B x y
        + (InfoGeometry.Canonical.LogDetRadonNikodymMechanism.DefectiveLogPotential B x
          + InfoGeometry.Canonical.LogDetRadonNikodymMechanism.DefectiveLogPotential B y) :=
  InfoGeometry.Canonical.LogDetRadonNikodymMechanism.defectiveLogPotential_mul
    B x y

end DefectiveLogRadonNikodym

end InfoGeometry.Canonical.ModularSurprisalThermoPacket
