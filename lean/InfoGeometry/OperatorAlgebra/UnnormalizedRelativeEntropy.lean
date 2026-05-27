/-
InfoGeometry/OperatorAlgebra/UnnormalizedRelativeEntropy.lean

Unnormalized relative entropy and modular transport sockets.

This module replaces normalized density matrices and flat Frobenius Bregman
approximations by proof-carrying relative modular data for unnormalized weights.

Key discipline:

* no `trace rho = 1` normalization;
* no generic `logOp : A -> A` as a foundational primitive;
* no unconditional `log(AB)=log A+log B`;
* no Frobenius/Gaussian divergence as the thermodynamic foundation;
* relative entropy and transport cost may be infinite.

The primitive Type III object is the relative modular/spatial derivative datum.
The symmetric modular Hamiltonian and BKM/Wasserstein metric are calibrated
readouts derived from it.
-/

import Mathlib
import Mathlib.Data.ENNReal.Basic

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy

/-! ## 1. Unnormalized weights -/

/--
A positive-cone weight socket.

This is deliberately not a normalized state. There is no axiom `weight 1 = 1`.

For Type III algebras, a weight is the correct integration primitive.
-/
structure OperatorWeight
    (A : Type*) where
  /-- Positive cone of the algebra/domain. -/
  positiveCone : Set A

  /-- Extended nonnegative weight readout. -/
  weight : A → ℝ≥0∞

  /-- Positivity law on the chosen cone. -/
  positive_law : Prop
  positive_certificate :
    positive_law

  /-- Normality / lower-semicontinuity / directed-sup preservation socket. -/
  normality_law : Prop
  normality_certificate :
    normality_law

  /-- A weight is faithful if it is zero only at the zero element. -/
  faithfulness_law : ∀ x ∈ positiveCone, weight x = 0 → x = 0
  faithfulness_certificate :
    faithfulness_law

  /-- Semifiniteness: the weight is finite on a dense subset. -/
  semifiniteness_law : ∃ S ⊆ positiveCone, (∀ x ∈ S, IsFiniteAt φ x) ∧ True -- placeholder for density
  semifiniteness_certificate :
    semifiniteness_law

namespace OperatorWeight

variable {A : Type*}
variable (φ : OperatorWeight A)

/--
A weight is finite at an element when its value is not infinity.
-/
def IsFiniteAt
    (x : A) : Prop :=
  φ.weight x ≠ ⊤

/--
The mass/readout of a chosen unit-like element.

This is not required to be `1`.
-/
def mass
    (unitLike : A) : ℝ≥0∞ :=
  φ.weight unitLike

end OperatorWeight

/-! ## 2. Relative modular / spatial derivative primitive -/

/--
Relative modular datum for unnormalized weights.

This is the foundational socket. In concrete von Neumann models this should be
instantiated by the relative modular operator / Connes spatial derivative.

The logarithm and Hamiltonian readouts are not primitive generic ring
functions; they are readouts of relative modular data.
-/
structure RelativeModularDatum
    (A Modular : Type*) where
  /-- Relative modular object, morally `Delta_{phi,psi}` or `dphi/dpsi`. -/
  relativeModular :
    OperatorWeight A → OperatorWeight A → Modular

  /--
  Relative logarithmic generator, morally `log Delta_{phi,psi}`.

  This is attached to the relative modular object, not to arbitrary algebra
  elements.
  -/
  relativeLog :
    Modular → Modular

  /--
  Certificate that this relative modular datum is the intended Connes/Araki
  spatial derivative object.
  -/
  spatial_derivative_law : Prop
  spatial_derivative_certificate :
    spatial_derivative_law

  /--
  Domain/support compatibility.

  In concrete models this controls absolute continuity, support projections,
  and the infinite-entropy case.
  -/
  support_compatibility_law : Prop
  support_compatibility_certificate :
    support_compatibility_law

namespace RelativeModularDatum

variable {A Modular : Type*}
variable (Δ : RelativeModularDatum A Modular)

/--
Relative modular logarithm between two weights.
-/
def relativeLogBetween
    (φ ψ : OperatorWeight A) : Modular :=
  Δ.relativeLog (Δ.relativeModular φ ψ)

end RelativeModularDatum

/-! ## 3. Unnormalized relative entropy socket -/

/--
Unnormalized relative entropy datum.

The codomain is `ℝ≥0∞` because relative entropy may be infinite.

This is a readout supplied by a concrete relative modular model. It is not
defined by a naive `trace (rho * (log rho - log sigma))` formula at this layer.
-/
structure UnnormalizedRelativeEntropyDatum
    (A Modular : Type*) where
  relativeModular :
    RelativeModularDatum A Modular

  /-- Nonnegative extended relative entropy. -/
  entropy :
    OperatorWeight A → OperatorWeight A → ℝ≥0∞

  /--
  Entropy is nonnegative.

  For finite unnormalized matrices this corresponds to the mass-corrected
  Bregman KL divergence.
  -/
  entropy_nonnegative :
    ∀ φ ψ : OperatorWeight A,
      (0 : ℝ≥0∞) ≤ entropy φ ψ

  /--
  Zero self-divergence.
  -/
  entropy_self :
    ∀ φ : OperatorWeight A,
      entropy φ φ = 0

  /--
  Relative modular interpretation law.

  Concrete models should connect `entropy phi psi` to the Araki/Connes relative
  modular expression.
  -/
  relative_modular_entropy_law : Prop
  relative_modular_entropy_certificate :
    relative_modular_entropy_law

namespace UnnormalizedRelativeEntropyDatum

variable {A Modular : Type*}
variable (S : UnnormalizedRelativeEntropyDatum A Modular)

/--
Relative entropy is nonnegative.
-/
theorem nonnegative
    (φ ψ : OperatorWeight A) :
    (0 : ℝ≥0∞) ≤ S.entropy φ ψ :=
  S.entropy_nonnegative φ ψ

/--
Self-relative entropy vanishes.
-/
theorem self_eq_zero
    (φ : OperatorWeight A) :
    S.entropy φ φ = 0 :=
  S.entropy_self φ

end UnnormalizedRelativeEntropyDatum

/-! ## 4. Finite trace/log specialization socket -/

/--
Finite log-potential specialization.

This is only for trace-capable finite or semifinite models where a real-valued
formula is justified.

For unnormalized positive operators, the Bregman KL formula includes the mass
correction:

`Tr(rho log rho - rho log sigma - rho + sigma)`.
-/
structure FiniteLogBregmanDatum
    (A : Type*) [Ring A] where
  /-- Operator logarithm on the admissible positive domain. -/
  logOp : A → A

  /-- Trace / finite integration backend. -/
  trace : A → ℝ

  /-- Unit-like element or mass reference. -/
  unitLike : A

  /-- Admissible positive cone/domain. -/
  positiveCone : Set A

  /-- Log-domain law, including positivity/invertibility/support assumptions. -/
  log_domain_law : Prop
  log_domain_certificate :
    log_domain_law

  /--
  Trace cyclicity or trace property on the admissible domain.
  -/
  trace_law : Prop
  trace_certificate :
    trace_law

  /--
  Warning: no unconditional noncommutative logarithm laws are assumed.
  Commuting-log laws belong to separate certificates.
  -/
  no_unconditional_log_mul_law : Prop
  no_unconditional_log_mul_certificate :
    no_unconditional_log_mul_law

namespace FiniteLogBregmanDatum

variable {A : Type*} [Ring A]
variable (L : FiniteLogBregmanDatum A)

/--
Mass-corrected finite unnormalized KL/Bregman expression.

`D(rho||sigma) = Tr(rho log rho - rho log sigma - rho + sigma)`.
-/
def massCorrectedKL
    (ρ σ : A) : ℝ :=
  L.trace (ρ * L.logOp ρ - ρ * L.logOp σ - ρ + σ)

/--
Uncorrected log energy.

This may be useful as a modular energy term, but should not be used as the
foundational nonnegative Bregman divergence on an unnormalized cone.
-/
def uncorrectedLogEnergy
    (ρ σ : A) : ℝ :=
  L.trace (ρ * (L.logOp ρ - L.logOp σ))

end FiniteLogBregmanDatum

/-! ## 5. Optional continuous functional calculus bridge -/

/--
Continuous-functional-calculus log bridge.

This should be instantiated only in a concrete C*-algebraic setting where the
element is positive/invertible or otherwise has spectrum in the logarithm's
domain.

This is intentionally a bridge, not the foundation.
-/
structure CFCLogBridge
    (A : Type*) where
  /-- CFC-defined log readout. -/
  cfcLog : A → A

  /-- Spectrum/log-domain law. -/
  spectrum_log_domain_law : Prop
  spectrum_log_domain_certificate :
    spectrum_log_domain_law

  /-- Agreement with the finite/log Bregman datum where both are defined. -/
  agrees_with_logDatum_law : Prop
  agrees_with_logDatum_certificate :
    agrees_with_logDatum_law

namespace CFCLogBridge

variable {A : Type*}
variable (C : CFCLogBridge A)

end CFCLogBridge

/-! ## 6. BKM / transport metric socket -/

/--
BKM / Bures-Kantorovich-style transport cost on unnormalized weights.

The cost is nonnegative and may be infinite.
-/
structure ModularTransportCostDatum
    (A Modular : Type*) where
  relativeEntropy :
    UnnormalizedRelativeEntropyDatum A Modular

  /-- Transport cost between unnormalized weights. -/
  cost :
    OperatorWeight A → OperatorWeight A → ℝ≥0∞

  /-- Nonnegativity. -/
  cost_nonnegative :
    ∀ φ ψ,
      (0 : ℝ≥0∞) ≤ cost φ ψ

  /-- Zero self-cost. -/
  cost_self :
    ∀ φ,
      cost φ φ = 0

  /--
  Transport/modular calibration law.

  This is where the concrete BKM/Bures/Wasserstein model connects the relative
  modular response to the transport metric.
  -/
  modular_transport_law : Prop
  modular_transport_certificate :
    modular_transport_law

namespace ModularTransportCostDatum

variable {A Modular : Type*}
variable (T : ModularTransportCostDatum A Modular)

theorem nonnegative
    (φ ψ : OperatorWeight A) :
    (0 : ℝ≥0∞) ≤ T.cost φ ψ :=
  T.cost_nonnegative φ ψ

theorem self_eq_zero
    (φ : OperatorWeight A) :
    T.cost φ φ = 0 :=
  T.cost_self φ

end ModularTransportCostDatum

/-! ## 7. Symmetric relative modular Hamiltonian calibration -/

/--
Symmetric relative modular Hamiltonian calibration.

This is not primitive. It is a derived/readout layer used when a concrete model
wants a symmetric generator for response metrics or transport geometry.
-/
structure SymmetricRelativeHamiltonianCalibration
    (A Modular SymHam : Type*) where
  relativeModular :
    RelativeModularDatum A Modular

  /-- Symmetric Hamiltonian readout. -/
  symmetricHamiltonian :
    OperatorWeight A → OperatorWeight A → SymHam

  /--
  Relation to the relative modular/spatial derivative.

  Concrete examples may use symmetric logarithmic derivatives, Kubo-Mori
  operators, or other model-specific response generators.
  -/
  derived_from_relative_modular_law : Prop
  derived_from_relative_modular_certificate :
    derived_from_relative_modular_law

  /--
  Symmetry law, if appropriate for the chosen convention.
  -/
  symmetry_law : Prop
  symmetry_certificate :
    symmetry_law

namespace SymmetricRelativeHamiltonianCalibration

variable {A Modular SymHam : Type*}
variable (H : SymmetricRelativeHamiltonianCalibration A Modular SymHam)

end SymmetricRelativeHamiltonianCalibration

end InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy
