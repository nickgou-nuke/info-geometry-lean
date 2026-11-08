import InfoGeometry.SuperMetriplectic.OperatorKLBKM
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Canonical.RelativeModularBerezinianBridge

/-!
# Souriau/Tomita/BKM Dictionary

Trace-free reconciliation packet for Souriau Lie thermodynamics and
Tomita-Takesaki modular thermodynamics.

The point of this file is a precise Lean surface for the dictionary:

* Souriau geometric temperature/moment pairing becomes the modular Hamiltonian;
* Souriau Massieu Hessian becomes the BKM/Kubo-Mori Hessian after operator lift;
* coadjoint leaves become modular-spectrum leaves;
* transverse motion is Araki/operatorial-KL entropy production;
* the Type III super-volume is carried by expectation ratios, not traces.

The analytic construction of a Type III von Neumann algebra, modular operator
or Duhamel integral is not claimed here.  This module connects compiled
readout packets and keeps those analytic obligations explicit as fields.
-/

namespace InfoGeometry.SuperMetriplectic

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeModularBerezinianBridge
open InfoGeometry.Geometry

/--
Souriau geometric-temperature to Tomita modular-Hamiltonian dictionary.

The intended formula is
`K_Ω = -log Δ_Ω = <β, Ĵ>`.
-/
structure SouriauTomitaTemperatureDictionary where
  geometricTemperaturePairing : ℝ
  souriauMomentPairing : ℝ
  modularDeltaLog : ℝ
  modularHamiltonian : ℝ
  thermalTimeGenerator : ℝ
  momentPairing_eq_beta_J :
    souriauMomentPairing = geometricTemperaturePairing
  modularHamiltonian_eq_momentPairing :
    modularHamiltonian = souriauMomentPairing
  modularDeltaLog_eq_modularHamiltonian :
    modularDeltaLog = modularHamiltonian
  thermalTime_eq_modularHamiltonian :
    thermalTimeGenerator = modularHamiltonian

namespace SouriauTomitaTemperatureDictionary

/-- Souriau `<β,J>` is the modular Hamiltonian readout. -/
theorem modularHamiltonian_eq_betaJ
    (D : SouriauTomitaTemperatureDictionary) :
    D.modularHamiltonian = D.geometricTemperaturePairing := by
  rw [D.modularHamiltonian_eq_momentPairing, D.momentPairing_eq_beta_J]

/-- The Tomita logarithmic datum is the thermal-time generator. -/
theorem modularDeltaLog_eq_thermalTime
    (D : SouriauTomitaTemperatureDictionary) :
    D.modularDeltaLog = D.thermalTimeGenerator := by
  rw [D.modularDeltaLog_eq_modularHamiltonian,
    ← D.thermalTime_eq_modularHamiltonian]

end SouriauTomitaTemperatureDictionary

/--
Souriau Hessian/BKM reconciliation.

Classically the Hessian is the covariance of moment-map components.  After the
operator lift, the noncommutative second derivative is the modular-flow-smeared
BKM bilinear form.
-/
structure SouriauBKMHessianDictionary (Op : Type*) where
  souriauMassieuHessian : Op → Op → ℝ
  classicalCovarianceReadout : Op → Op → ℝ
  bkmHessian : OperatorBKMHessianPacket Op
  souriauHessian_eq_classicalCovariance :
    ∀ A B : Op, souriauMassieuHessian A B = classicalCovarianceReadout A B
  operatorLift_eq_bkm :
    ∀ A B : Op, souriauMassieuHessian A B = bkmHessian.hessian A B

namespace SouriauBKMHessianDictionary

/-- The Souriau Massieu Hessian is the classical covariance readout. -/
theorem souriauHessian_eq_covariance
    {Op : Type*} (D : SouriauBKMHessianDictionary Op) (A B : Op) :
    D.souriauMassieuHessian A B = D.classicalCovarianceReadout A B :=
  D.souriauHessian_eq_classicalCovariance A B

/-- The operatorial lift of the Souriau Hessian is BKM. -/
theorem souriauHessian_eq_bkm
    {Op : Type*} (D : SouriauBKMHessianDictionary Op) (A B : Op) :
    D.souriauMassieuHessian A B = D.bkmHessian.bkm A B := by
  rw [D.operatorLift_eq_bkm A B]
  exact D.bkmHessian.hessian_eq_bkm_form A B

/-- The lifted Souriau Hessian is nonnegative on diagonal generators. -/
theorem souriauHessian_nonneg
    {Op : Type*} (D : SouriauBKMHessianDictionary Op) (A : Op) :
    0 ≤ D.souriauMassieuHessian A A := by
  rw [D.souriauHessian_eq_bkm]
  exact D.bkmHessian.bkm_nonneg A

end SouriauBKMHessianDictionary

/--
Souriau coadjoint foliation as modular-spectrum foliation.

The conservative/along-leaf channel carries zero Araki/operatorial-KL
production.  The transverse channel is exactly the relative-entropy production
readout supplied by the packet.
-/
structure SouriauModularFoliationDictionary where
  coadjointLeafMotion : ℝ
  modularSpectrumLeafMotion : ℝ
  transverseMotion : ℝ
  arakiRelativeEntropyProduction : ℝ
  alongLeafEntropyProduction : ℝ
  coadjoint_eq_modularSpectrum :
    coadjointLeafMotion = modularSpectrumLeafMotion
  alongLeafEntropyProduction_zero :
    alongLeafEntropyProduction = 0
  transverseMotion_eq_arakiProduction :
    transverseMotion = arakiRelativeEntropyProduction

namespace SouriauModularFoliationDictionary

/-- Along a Souriau/modular leaf, entropy production vanishes. -/
theorem alongLeaf_entropy_zero
    (F : SouriauModularFoliationDictionary) :
    F.alongLeafEntropyProduction = 0 :=
  F.alongLeafEntropyProduction_zero

/-- Transverse motion is measured by Araki/operatorial-KL production. -/
theorem transverse_eq_araki
    (F : SouriauModularFoliationDictionary) :
    F.transverseMotion = F.arakiRelativeEntropyProduction :=
  F.transverseMotion_eq_arakiProduction

end SouriauModularFoliationDictionary

/--
Souriau/Tomita/BKM capstone over the operator KL/BKM route.
-/
structure SouriauTomitaBKMCapstone (Op : Type*) where
  operatorKL : OperatorKLBKMCapstone Op
  temperature : SouriauTomitaTemperatureDictionary
  hessian : SouriauBKMHessianDictionary Op
  foliation : SouriauModularFoliationDictionary
  typeIIIExpectation : TypeIIIExpectationCarrier Op
  bkm_matches_operatorKL :
    hessian.bkmHessian = operatorKL.bkmHessian
  supervolume_expectation_matches :
    operatorKL.superVolume.expectation = typeIIIExpectation

namespace SouriauTomitaBKMCapstone

/-- Souriau temperature pairing is the Tomita modular Hamiltonian. -/
theorem betaJ_eq_modularHamiltonian
    {Op : Type*} (C : SouriauTomitaBKMCapstone Op) :
    C.temperature.modularHamiltonian = C.temperature.geometricTemperaturePairing :=
  C.temperature.modularHamiltonian_eq_betaJ

/-- Souriau Hessian lifts to the BKM bilinear form. -/
theorem souriauHessian_eq_bkm
    {Op : Type*} (C : SouriauTomitaBKMCapstone Op) (A B : Op) :
    C.hessian.souriauMassieuHessian A B = C.operatorKL.bkmHessian.bkm A B := by
  rw [C.hessian.souriauHessian_eq_bkm A B]
  rw [C.bkm_matches_operatorKL]

/-- Coadjoint-leaf entropy production is zero in the modular foliation dictionary. -/
theorem alongLeaf_entropy_zero
    {Op : Type*} (C : SouriauTomitaBKMCapstone Op) :
    C.foliation.alongLeafEntropyProduction = 0 :=
  C.foliation.alongLeaf_entropy_zero

/-- The transverse modular/Souriau motion is Araki relative-entropy production. -/
theorem transverseMotion_eq_arakiProduction
    {Op : Type*} (C : SouriauTomitaBKMCapstone Op) :
    C.foliation.transverseMotion =
      C.foliation.arakiRelativeEntropyProduction :=
  C.foliation.transverse_eq_araki

/-- The Type III super-volume uses the supplied expectation carrier. -/
theorem superVolume_uses_expectationCarrier
    {Op : Type*} (C : SouriauTomitaBKMCapstone Op) :
    C.operatorKL.superVolume.expectation = C.typeIIIExpectation :=
  C.supervolume_expectation_matches

/--
Final reconciliation theorem:
Souriau `<β,J>` is the modular Hamiltonian, the Souriau Hessian is BKM, the
conservative leaf has zero entropy production, transverse flow is Araki/KL
production, and the Type III super-volume is expectation-carried.
-/
theorem souriau_tomita_bkm_reconciliation
    {Op : Type*} (C : SouriauTomitaBKMCapstone Op) (A B : Op) :
    C.temperature.modularHamiltonian = C.temperature.geometricTemperaturePairing
      ∧ C.hessian.souriauMassieuHessian A B = C.operatorKL.bkmHessian.bkm A B
      ∧ C.foliation.alongLeafEntropyProduction = 0
      ∧ C.foliation.transverseMotion =
          C.foliation.arakiRelativeEntropyProduction
      ∧ C.operatorKL.superVolume.expectation = C.typeIIIExpectation := by
  exact ⟨C.betaJ_eq_modularHamiltonian,
    C.souriauHessian_eq_bkm A B,
    C.alongLeaf_entropy_zero,
    C.transverseMotion_eq_arakiProduction,
    C.superVolume_uses_expectationCarrier⟩

end SouriauTomitaBKMCapstone

/--
Modular derivation dictionary.

This is the infinitesimal version of the Souriau/Tomita bridge: Lie
derivations generated by geometric temperature are identified with modular
derivations generated by the Tomita Hamiltonian.
-/
structure SouriauTomitaDerivationDictionary (Op : Type*) where
  souriauLieDerivation : Op → Op
  tomitaModularDerivation : Op → Op
  thermalTimeDerivation : Op → Op
  souriau_eq_tomita :
    ∀ A : Op, souriauLieDerivation A = tomitaModularDerivation A
  thermalTime_eq_tomita :
    ∀ A : Op, thermalTimeDerivation A = tomitaModularDerivation A

namespace SouriauTomitaDerivationDictionary

/-- Souriau Lie derivation is the Tomita modular derivation. -/
theorem souriauDerivation_eq_tomita
    {Op : Type*} (D : SouriauTomitaDerivationDictionary Op) (A : Op) :
    D.souriauLieDerivation A = D.tomitaModularDerivation A :=
  D.souriau_eq_tomita A

/-- Thermal-time derivation is the Tomita modular derivation. -/
theorem thermalTimeDerivation_eq_tomita
    {Op : Type*} (D : SouriauTomitaDerivationDictionary Op) (A : Op) :
    D.thermalTimeDerivation A = D.tomitaModularDerivation A :=
  D.thermalTime_eq_tomita A

/-- Souriau derivation is the thermal-time derivation. -/
theorem souriauDerivation_eq_thermalTime
    {Op : Type*} (D : SouriauTomitaDerivationDictionary Op) (A : Op) :
    D.souriauLieDerivation A = D.thermalTimeDerivation A := by
  rw [D.souriauDerivation_eq_tomita, D.thermalTimeDerivation_eq_tomita]

end SouriauTomitaDerivationDictionary

/--
Thermal-time flow dictionary.

The Connes-Rovelli thermal-time reading is represented as equality between the
Souriau thermodynamic flow and the Tomita modular flow on every operator lane.
-/
structure ThermalTimeHypothesisPacket (Op : Type*) where
  souriauThermalFlow : ℝ → Op → Op
  tomitaModularFlow : ℝ → Op → Op
  thermalTimeFlow : ℝ → Op → Op
  souriauFlow_eq_tomita :
    ∀ t A, souriauThermalFlow t A = tomitaModularFlow t A
  thermalTimeFlow_eq_tomita :
    ∀ t A, thermalTimeFlow t A = tomitaModularFlow t A

namespace ThermalTimeHypothesisPacket

/-- Souriau thermodynamic flow is Tomita modular flow. -/
theorem souriauFlow_eq_modularFlow
    {Op : Type*} (T : ThermalTimeHypothesisPacket Op) (t : ℝ) (A : Op) :
    T.souriauThermalFlow t A = T.tomitaModularFlow t A :=
  T.souriauFlow_eq_tomita t A

/-- Thermal time is represented by the Tomita modular flow. -/
theorem thermalTime_eq_modularFlow
    {Op : Type*} (T : ThermalTimeHypothesisPacket Op) (t : ℝ) (A : Op) :
    T.thermalTimeFlow t A = T.tomitaModularFlow t A :=
  T.thermalTimeFlow_eq_tomita t A

/-- Souriau flow is the thermal-time flow. -/
theorem souriauFlow_eq_thermalTimeFlow
    {Op : Type*} (T : ThermalTimeHypothesisPacket Op) (t : ℝ) (A : Op) :
    T.souriauThermalFlow t A = T.thermalTimeFlow t A := by
  rw [T.souriauFlow_eq_modularFlow, T.thermalTime_eq_modularFlow]

end ThermalTimeHypothesisPacket

/--
Gradient-flow reading of linearized gravity.

The spin-2 Fierz channel is identified with the gradient-flow potential of the
operatorial Souriau/BKM relative-entropy geometry.
-/
structure OperatorGradientGravityPacket (Op : Type*) where
  relativeEntropyGradientFlow : Op → Op → ℝ
  souriauBKMGradientFlow : Op → Op → ℝ
  linearizedGravityPotential : Op → Op → ℝ
  spinTwoFierzChannel : Op → Op → ℝ
  relativeEntropyGradient_eq_souriauBKM :
    ∀ A B, relativeEntropyGradientFlow A B = souriauBKMGradientFlow A B
  souriauBKMGradient_eq_gravityPotential :
    ∀ A B, souriauBKMGradientFlow A B = linearizedGravityPotential A B
  gravityPotential_eq_spinTwo :
    ∀ A B, linearizedGravityPotential A B = spinTwoFierzChannel A B

namespace OperatorGradientGravityPacket

/-- Relative-entropy gradient flow is the Souriau/BKM gradient flow. -/
theorem relativeEntropyGradient_eq_souriauBKMGradient
    {Op : Type*} (G : OperatorGradientGravityPacket Op) (A B : Op) :
    G.relativeEntropyGradientFlow A B = G.souriauBKMGradientFlow A B :=
  G.relativeEntropyGradient_eq_souriauBKM A B

/-- The Souriau/BKM gradient flow is the linearized gravity potential. -/
theorem souriauBKMGradient_eq_gravity
    {Op : Type*} (G : OperatorGradientGravityPacket Op) (A B : Op) :
    G.souriauBKMGradientFlow A B = G.linearizedGravityPotential A B :=
  G.souriauBKMGradient_eq_gravityPotential A B

/-- The relative-entropy gradient extracts the Fierz spin-2 channel. -/
theorem relativeEntropyGradient_eq_spinTwo
    {Op : Type*} (G : OperatorGradientGravityPacket Op) (A B : Op) :
    G.relativeEntropyGradientFlow A B = G.spinTwoFierzChannel A B := by
  rw [G.relativeEntropyGradient_eq_souriauBKMGradient,
    G.souriauBKMGradient_eq_gravity,
    G.gravityPotential_eq_spinTwo]

end OperatorGradientGravityPacket

/--
Thermal-time capstone extending the Souriau/Tomita/BKM reconciliation.
-/
structure SouriauTomitaThermalTimeCapstone (Op : Type*) where
  reconciliation : SouriauTomitaBKMCapstone Op
  derivation : SouriauTomitaDerivationDictionary Op
  thermalTime : ThermalTimeHypothesisPacket Op
  gravityGradient : OperatorGradientGravityPacket Op

namespace SouriauTomitaThermalTimeCapstone

/-- The infinitesimal Souriau derivation is the thermal-time derivation. -/
theorem souriauDerivation_eq_thermalTime
    {Op : Type*} (C : SouriauTomitaThermalTimeCapstone Op) (A : Op) :
    C.derivation.souriauLieDerivation A =
      C.derivation.thermalTimeDerivation A :=
  C.derivation.souriauDerivation_eq_thermalTime A

/-- The Souriau thermodynamic flow is the thermal-time flow. -/
theorem souriauFlow_eq_thermalTime
    {Op : Type*} (C : SouriauTomitaThermalTimeCapstone Op) (t : ℝ) (A : Op) :
    C.thermalTime.souriauThermalFlow t A =
      C.thermalTime.thermalTimeFlow t A :=
  C.thermalTime.souriauFlow_eq_thermalTimeFlow t A

/-- Linearized gravity is the spin-2 channel of the relative-entropy gradient. -/
theorem relativeEntropyGradient_eq_spinTwo
    {Op : Type*} (C : SouriauTomitaThermalTimeCapstone Op) (A B : Op) :
    C.gravityGradient.relativeEntropyGradientFlow A B =
      C.gravityGradient.spinTwoFierzChannel A B :=
  C.gravityGradient.relativeEntropyGradient_eq_spinTwo A B

/--
Thermal-time generator theorem:
the Souriau derivation and flow are the Tomita thermal-time derivation and
flow, while the operatorial relative-entropy gradient extracts the spin-2
linearized-gravity channel.
-/
theorem thermal_time_generator_theorem
    {Op : Type*} (C : SouriauTomitaThermalTimeCapstone Op)
    (t : ℝ) (A B : Op) :
    C.derivation.souriauLieDerivation A =
        C.derivation.thermalTimeDerivation A
      ∧ C.thermalTime.souriauThermalFlow t A =
          C.thermalTime.thermalTimeFlow t A
      ∧ C.gravityGradient.relativeEntropyGradientFlow A B =
          C.gravityGradient.spinTwoFierzChannel A B := by
  exact ⟨C.souriauDerivation_eq_thermalTime A,
    C.souriauFlow_eq_thermalTime t A,
    C.relativeEntropyGradient_eq_spinTwo A B⟩

end SouriauTomitaThermalTimeCapstone

section PauliAuditSecondVariation

variable {n : ℕ} [Nonempty (Fin n)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
Pauli-audit endpoint for the requested lift:
the second variation of the relative modular supervolume potential is exactly
the symmetric Krein Hessian bilinear form used by the Sinkhorn/Perelman metric
lane.

This theorem is a SuperMetriplectic-facing alias of the owner theorem in
`RelativeModularBerezinianBridge`; no Type III trace-density Taylor series is
postulated here.
-/
@[rep_depth operator, capstone]
theorem relativeModularSupervolume_secondVariation_is_sinkhornPerelmanKreinMetric
    (C : RelativeModularSupervolumeKreinHessianLift (n := n) (E := E))
    (u v : H₂) :
    C.liftedSupervolumePotential C.basepoint =
        relativeModularSupervolumePotential
          (n := n) C.qPlus C.q0Plus C.qMinus C.q0Minus
      ∧ C.secondVariation u v = krein_form (E := E) u v
      ∧ C.secondVariation u v = C.secondVariation v u
      ∧ C.sinkhornPerelmanMetric u v = krein_form (E := E) u v
      ∧ C.sinkhornPerelmanMetric u v = C.sinkhornPerelmanMetric v u :=
  C.relativeModularSupervolume_secondVariation_Krein_packet u v

end PauliAuditSecondVariation

/--
Available discretization policies for the imaginary modular-time integral.

`chebyshevSpectralCollocation` is the default for the Sinkhorn/Perelman solver
lane because it resolves endpoint/KMS-boundary behavior on `[0,1]`.
`thermalMatsubaraSummation` is retained as a spectral diagnostic lane for
translation-invariant or mode-diagonal thermal data.
-/
inductive ImaginaryTimeDiscretizationScheme where
  | chebyshevSpectralCollocation
  | thermalMatsubaraSummation
deriving DecidableEq, Repr

/--
Policy carrier for discretizing the BKM modular-time integral.

The actual numerical quadrature error estimates are carried as explicit scalar
readouts.  Lean only checks the solver-policy implications.
-/
structure KMSImaginaryTimeDiscretizationPolicy
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℂ Op] where
  scheme : ImaginaryTimeDiscretizationScheme
  /-- Inverse temperature determining the upper KMS boundary. -/
  beta : ℝ
  /-- Complex-time correlation produced by the selected discretization. -/
  stripCorrelation : ℂ → Op
  /-- Domain on which complex differentiability is required. -/
  stripDomain : Set ℂ
  /-- Lower and upper KMS boundary readouts. -/
  lowerBoundary : ℝ → Op
  upperBoundary : ℝ → Op
  /-- Operator-valued Matsubara kernel. -/
  matsubaraKernel : ℤ → ℤ → Op
  /-- One numerical Sinkhorn/Perelman solver step. -/
  solverStep : Op → Op
  /-- Genuine analytic-strip regularity. -/
  analyticStripResolved :
    DifferentiableOn ℂ stripCorrelation stripDomain
  /-- Exact lower and upper KMS boundary equations. -/
  kmsBoundaryResidualControlled :
    (∀ t : ℝ, stripCorrelation (t : ℂ) = lowerBoundary t) ∧
    (∀ t : ℝ,
      stripCorrelation ((t : ℂ) + (beta : ℂ) * Complex.I) =
        upperBoundary t)
  /-- Matsubara mode diagonality means all off-diagonal kernel entries vanish. -/
  matsubaraModeDiagonal :
    ∀ m n : ℤ, m ≠ n → matsubaraKernel m n = 0
  /-- Solver readiness is witnessed by an actual fixed point. -/
  sinkhornPerelmanSolverReady :
    ∃ state : Op, solverStep state = state
  chebyshev_resolves_solver :
    scheme = ImaginaryTimeDiscretizationScheme.chebyshevSpectralCollocation →
      ∃ state : Op, solverStep state = state
  matsubara_is_diagnostic :
    scheme = ImaginaryTimeDiscretizationScheme.thermalMatsubaraSummation →
      ∀ m n : ℤ, m ≠ n → matsubaraKernel m n = 0

namespace KMSImaginaryTimeDiscretizationPolicy

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℂ Op]

/--
Chebyshev spectral collocation is solver-ready when the analytic strip and KMS
boundary residual are controlled.
-/
theorem solverReady_of_chebyshev
    (P : KMSImaginaryTimeDiscretizationPolicy Op)
    (hScheme : P.scheme =
      ImaginaryTimeDiscretizationScheme.chebyshevSpectralCollocation) :
    ∃ state : Op, P.solverStep state = state :=
  P.chebyshev_resolves_solver hScheme

/-- Matsubara summation is exposed as a mode-diagonal diagnostic lane. -/
theorem matsubara_modeDiagonal
    (P : KMSImaginaryTimeDiscretizationPolicy Op)
    (hScheme : P.scheme =
      ImaginaryTimeDiscretizationScheme.thermalMatsubaraSummation)
    (m n : ℤ) (hmn : m ≠ n) :
    P.matsubaraKernel m n = 0 :=
  P.matsubara_is_diagnostic hScheme
    m n hmn

end KMSImaginaryTimeDiscretizationPolicy

/--
Preferred policy packet for the Sinkhorn/Perelman BKM solver.

This records the architectural decision: use Chebyshev collocation for the
actual imaginary-time quadrature when KMS endpoint control matters.
-/
structure SinkhornPerelmanBKMQuadratureChoice
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℂ Op] where
  policy : KMSImaginaryTimeDiscretizationPolicy Op
  selected_chebyshev :
    policy.scheme =
      ImaginaryTimeDiscretizationScheme.chebyshevSpectralCollocation
  analyticStripResolved :
    DifferentiableOn ℂ policy.stripCorrelation policy.stripDomain
  kmsBoundaryResidualControlled :
    (∀ t : ℝ, policy.stripCorrelation (t : ℂ) = policy.lowerBoundary t) ∧
    (∀ t : ℝ,
      policy.stripCorrelation ((t : ℂ) + (policy.beta : ℂ) * Complex.I) =
        policy.upperBoundary t)

namespace SinkhornPerelmanBKMQuadratureChoice

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℂ Op]

/-- The selected Chebyshev policy is solver-ready under the supplied KMS controls. -/
theorem solverReady
    (Q : SinkhornPerelmanBKMQuadratureChoice Op) :
    ∃ state : Op, Q.policy.solverStep state = state :=
  Q.policy.solverReady_of_chebyshev
    Q.selected_chebyshev

end SinkhornPerelmanBKMQuadratureChoice

end InfoGeometry.SuperMetriplectic
