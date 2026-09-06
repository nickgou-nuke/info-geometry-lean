import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Basic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

/-! ## 5. Material-response bridge with Fresnel eigenvalues -/

/--
Information potential with a Hessian-style response pairing.

Complex optical coefficients are readouts of calibrated material/operator
response, not consequences of bare algebra alone.
-/
structure InformationPotentialDatum
    (State Tangent : Type*)
    [AddCommMonoid Tangent] [Module ℝ Tangent] where
  /-- Information potential. -/
  potential : State → ℝ

  /-- Hessian response as a genuine Mathlib bilinear form. -/
  hessian : State → LinearMap.BilinForm ℝ Tangent

  /-- Symmetry of the Hessian in Mathlib's native bilinear-form predicate. -/
  symmetric :
    ∀ X, (hessian X).IsSymm

  /-- Positive-semidefinite response. -/
  positive_semidefinite :
    ∀ X xi, 0 ≤ hessian X xi xi

namespace InformationPotentialDatum

variable {State Tangent : Type*}
variable [AddCommMonoid Tangent] [Module ℝ Tangent]
variable (Phi : InformationPotentialDatum State Tangent)

/-- Re-export Hessian symmetry. -/
theorem hessian_symmetric
    (X : State)
    (xi eta : Tangent) :
    Phi.hessian X xi eta = Phi.hessian X eta xi :=
  by
    exact (LinearMap.BilinForm.isSymm_def.mp (Phi.symmetric X)) xi eta

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
    (Op Freq WaveVector : Type*)
    [AddCommMonoid Op] [Module ℝ Op] where
  /-- Frequency/wave-vector dependent susceptibility. -/
  susceptibility : Freq → WaveVector → Op →ₗ[ℝ] Op

  /-- Frequencies belonging to the retarded-response support. -/
  retardedSupport : Set Freq

  /-- Retarded causality: response vanishes outside the selected support. -/
  causal :
    ∀ omega k perturbation,
      omega ∉ retardedSupport →
        susceptibility omega k perturbation = 0

  /-- Independently constructed Kubo/linear-response operator. -/
  linearResponseOperator : Freq → WaveVector → Op →ₗ[ℝ] Op

  /-- The susceptibility is the installed linear-response operator. -/
  linearResponseOrigin :
    ∀ omega k perturbation,
      susceptibility omega k perturbation =
        linearResponseOperator omega k perturbation

  /-- Independently constructed Hessian-response operator. -/
  hessianResponseOperator : Freq → WaveVector → Op →ₗ[ℝ] Op

  /-- Compatibility with the installed Hessian response. -/
  hessianCompatibility :
    ∀ omega k perturbation,
      susceptibility omega k perturbation =
        hessianResponseOperator omega k perturbation

namespace LinearSusceptibilityDatum

variable {Op Freq WaveVector : Type*}
variable [AddCommMonoid Op] [Module ℝ Op]
variable (chi : LinearSusceptibilityDatum Op Freq WaveVector)

/-- Susceptibility vanishes outside the retarded support. -/
theorem eq_zero_of_not_mem_retardedSupport
    {omega : Freq} (homega : omega ∉ chi.retardedSupport)
    (k : WaveVector) (perturbation : Op) :
    chi.susceptibility omega k perturbation = 0 :=
  chi.causal omega k perturbation homega

/-- Readback of the Kubo/linear-response realization. -/
theorem susceptibility_eq_linearResponseOperator
    (omega : Freq) (k : WaveVector) (perturbation : Op) :
    chi.susceptibility omega k perturbation =
      chi.linearResponseOperator omega k perturbation :=
  chi.linearResponseOrigin omega k perturbation

/-- Readback of the installed Hessian-response realization. -/
theorem susceptibility_eq_hessianResponseOperator
    (omega : Freq) (k : WaveVector) (perturbation : Op) :
    chi.susceptibility omega k perturbation =
      chi.hessianResponseOperator omega k perturbation :=
  chi.hessianCompatibility omega k perturbation

end LinearSusceptibilityDatum

/--
Hessian-to-susceptibility bridge for a concrete material model.

This is where a concrete material proves that its response is induced by the
Hessian of the chosen information potential.
-/
structure HessianSusceptibilityBridge
    (State Tangent Op Freq WaveVector : Type*)
    [AddCommMonoid Tangent] [Module ℝ Tangent]
    [AddCommMonoid Op] [Module ℝ Op] where
  /-- Information potential and Hessian response. -/
  potential :
    InformationPotentialDatum State Tangent

  /-- Linear susceptibility datum. -/
  susceptibility :
    LinearSusceptibilityDatum Op Freq WaveVector

  /-- Material state at which response is linearized. -/
  baseState : State

  /-- Map from operator perturbations to Hessian tangent directions. -/
  tangentOfPerturbation : Op →ₗ[ℝ] Tangent

  /-- Frequency-dependent tangent direction probed by the response. -/
  responseDirection : Freq → WaveVector → Op →ₗ[ℝ] Tangent

  /-- Scalar material readout of an operator response. -/
  responseReadout : Op →ₗ[ℝ] ℝ

  /-- Susceptibility is induced by the Hessian bilinear response. -/
  susceptibility_eq_hessian_response :
    ∀ omega k perturbation,
      responseReadout
          (susceptibility.susceptibility omega k perturbation) =
        potential.hessian baseState
          (tangentOfPerturbation perturbation)
          (responseDirection omega k perturbation)

namespace HessianSusceptibilityBridge

variable {State Tangent Op Freq WaveVector : Type*}
variable [AddCommMonoid Tangent] [Module ℝ Tangent]
variable [AddCommMonoid Op] [Module ℝ Op]
variable (B : HessianSusceptibilityBridge State Tangent Op Freq WaveVector)

/-- Readback of the Hessian realization of material susceptibility. -/
theorem responseReadout_susceptibility
    (omega : Freq) (k : WaveVector) (perturbation : Op) :
    B.responseReadout
        (B.susceptibility.susceptibility omega k perturbation) =
      B.potential.hessian B.baseState
        (B.tangentOfPerturbation perturbation)
        (B.responseDirection omega k perturbation) :=
  B.susceptibility_eq_hessian_response omega k perturbation

end HessianSusceptibilityBridge

/--
Dielectric/impedance response extracted from susceptibility.

This material interface is needed before Fresnel coefficients can be computed.
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

  /-- Electric susceptibility supplying the dielectric response. -/
  electricSusceptibility : Freq → WaveVector → ℂ

  /-- Magnetic susceptibility supplying the permeability response. -/
  magneticSusceptibility : Freq → WaveVector → ℂ

  /-- Refractive-index and impedance dispersion identities. -/
  opticalBackendValid :
    (∀ omega k,
      refractiveIndex omega k ^ 2 = epsilon omega k * mu omega k) ∧
    (∀ omega k,
      impedance omega k ^ 2 * epsilon omega k = mu omega k)

  /-- Dielectric and magnetic responses arise from their susceptibilities. -/
  fromSusceptibility :
    (∀ omega k,
      epsilon omega k = 1 + electricSusceptibility omega k) ∧
    (∀ omega k,
      mu omega k = 1 + magneticSusceptibility omega k)

namespace DielectricResponseDatum

variable {Freq WaveVector : Type*}
variable (D : DielectricResponseDatum Freq WaveVector)

/-- The refractive index squares to the dielectric-permeability product. -/
theorem refractiveIndex_sq
    (omega : Freq) (k : WaveVector) :
    D.refractiveIndex omega k ^ 2 =
      D.epsilon omega k * D.mu omega k :=
  D.opticalBackendValid.1 omega k

/-- The impedance satisfies its dielectric-permeability dispersion law. -/
theorem impedance_sq_mul_epsilon
    (omega : Freq) (k : WaveVector) :
    D.impedance omega k ^ 2 * D.epsilon omega k = D.mu omega k :=
  D.opticalBackendValid.2 omega k

/-- Dielectric response is one plus electric susceptibility. -/
theorem epsilon_eq_one_add_electricSusceptibility
    (omega : Freq) (k : WaveVector) :
    D.epsilon omega k = 1 + D.electricSusceptibility omega k :=
  D.fromSusceptibility.1 omega k

/-- Permeability is one plus magnetic susceptibility. -/
theorem mu_eq_one_add_magneticSusceptibility
    (omega : Freq) (k : WaveVector) :
    D.mu omega k = 1 + D.magneticSusceptibility omega k :=
  D.fromSusceptibility.2 omega k

end DielectricResponseDatum

/-- Polarization mode at a planar interface. -/
inductive PolarizationMode where
  | s
  | p
deriving DecidableEq, Repr
