import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

/-! ## 5. Material-response bridge with Fresnel eigenvalues -/

/--
Information potential with a Hessian-style response pairing.

Complex optical coefficients are readouts of calibrated material/operator
response, not consequences of bare algebra alone.
-/
structure InformationPotentialDatum
    (State Tangent : Type*) where
  /-- Information potential. -/
  potential : State → ℝ

  /-- Hessian response pairing. -/
  hessian : State → Tangent → Tangent → ℝ

  /-- Symmetry of the Hessian. -/
  symmetric :
    ∀ X xi eta, hessian X xi eta = hessian X eta xi

  /-- Positive-semidefinite response. -/
  positive_semidefinite :
    ∀ X xi, 0 ≤ hessian X xi xi

namespace InformationPotentialDatum

variable {State Tangent : Type*}
variable (Phi : InformationPotentialDatum State Tangent)

/-- Re-export Hessian symmetry. -/
theorem hessian_symmetric
    (X : State)
    (xi eta : Tangent) :
    Phi.hessian X xi eta = Phi.hessian X eta xi :=
  Phi.symmetric X xi eta

/-- Re-export positive semidefiniteness. -/
theorem hessian_nonneg
    (X : State)
    (xi : Tangent) :
    0 ≤ Phi.hessian X xi xi :=
  Phi.positive_semidefinite X xi

end InformationPotentialDatum

/--
Bregman-style heat/readout datum.

Concrete modules can instantiate this with an explicit Bregman divergence,
such as the finite Jones quadratic potential.
-/
structure BregmanHeatDatum
    (State : Type*) where
  /-- Heat/divergence readout. -/
  heat : State → State → ℝ

  /-- Nonnegativity of the heat readout. -/
  nonnegative :
    ∀ X Y, 0 ≤ heat X Y

  /-- Vanishing on the diagonal. -/
  zero_on_diagonal :
    ∀ X, heat X X = 0

namespace BregmanHeatDatum

variable {State : Type*}
variable (B : BregmanHeatDatum State)

/-- Re-export heat nonnegativity. -/
theorem heat_nonnegative
    (X Y : State) :
    0 ≤ B.heat X Y :=
  B.nonnegative X Y

/-- Re-export diagonal vanishing. -/
theorem heat_self
    (X : State) :
    B.heat X X = 0 :=
  B.zero_on_diagonal X

end BregmanHeatDatum

/--
Abstract linear susceptibility datum.

`Op` is the material/operator response algebra.  `Freq` and `WaveVector`
parametrize the frequency and momentum/wave-vector channels.
-/
structure LinearSusceptibilityDatum
    (Op Freq WaveVector : Type*) where
  /-- Frequency/wave-vector dependent susceptibility. -/
  susceptibility : Freq → WaveVector → Op → Op

  /-- Causality/retarded-response certificate. -/
  causal : Prop

  /-- Kubo or linear-response origin certificate. -/
  linearResponseOrigin : Prop

  /-- Compatibility with a Hessian information response. -/
  hessianCompatibility : Prop

/--
Hessian-to-susceptibility bridge for a concrete material model.

This is where a concrete material proves that its response is induced by the
Hessian of the chosen information potential.
-/
structure HessianSusceptibilityBridge
    (State Tangent Op Freq WaveVector : Type*) where
  /-- Information potential and Hessian response. -/
  potential :
    InformationPotentialDatum State Tangent

  /-- Linear susceptibility datum. -/
  susceptibility :
    LinearSusceptibilityDatum Op Freq WaveVector

  /-- Material state at which response is linearized. -/
  baseState : State

  /-- Map from operator perturbations to Hessian tangent directions. -/
  tangentOfPerturbation : Op → Tangent

  /-- Certificate that susceptibility is induced by the Hessian response. -/
  susceptibility_eq_hessian_response : Prop

/--
Dielectric/impedance response extracted from susceptibility.

This material socket is needed before Fresnel coefficients can be computed.
-/
structure DielectricResponseDatum
    (Freq WaveVector : Type*) where
  /-- Complex dielectric response. -/
  epsilon : Freq → WaveVector → ℂ

  /-- Complex permeability response. -/
  mu : Freq → WaveVector → ℂ

  /-- Complex refractive index. -/
  refractiveIndex : Freq → WaveVector → ℂ

  /-- Complex impedance. -/
  impedance : Freq → WaveVector → ℂ

  /-- Optical backend validity certificate. -/
  opticalBackendValid : Prop

  /-- Compatibility with a susceptibility datum. -/
  fromSusceptibility : Prop

/-- Polarization mode at a planar interface. -/
inductive PolarizationMode where
  | s
  | p
deriving DecidableEq, Repr
