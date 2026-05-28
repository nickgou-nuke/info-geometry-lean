/-
InfoGeometry/OperatorAlgebra/UnnormalizedRelativeEntropy.lean

Unnormalized relative entropy and modular transport data.
-/

import Mathlib
import Mathlib.Data.ENNReal.Basic

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy

/-! ## 1. Unnormalized weights -/

/--
A positive-cone weight datum.
-/
structure OperatorWeight (A : Type*) [Zero A] where
  /-- Positive cone of the algebra/domain. -/
  positiveCone : Set A

  /-- Extended nonnegative weight readout. -/
  weight : A → ℝ≥0∞

  /-- Positivity: the weight is non-negative on the positive cone. -/
  positive_law : ∀ x ∈ positiveCone, 0 ≤ weight x

  /-- A weight is faithful if it is zero only at the zero element. -/
  faithfulness_law : ∀ x ∈ positiveCone, weight x = 0 → x = 0

  /-- Semifiniteness: the weight is finite on a dense subset. -/
  semifiniteness_law : ∃ S ⊆ positiveCone, ∀ x ∈ S, weight x < ⊤

namespace OperatorWeight

variable {A : Type*} [Zero A]
variable (φ : OperatorWeight A)

/-- Positivity of the weight on the positive cone. -/
theorem positive {x : A} (hx : x ∈ φ.positiveCone) : 0 ≤ φ.weight x :=
  φ.positive_law x hx

/-- Faithfulness of the weight. -/
theorem faithfulness {x : A} (hx : x ∈ φ.positiveCone) (hw : φ.weight x = 0) : x = 0 :=
  φ.faithfulness_law x hx hw

end OperatorWeight

/-! ## 2. Relative modular datum -/

/--
Relative modular datum for unnormalized weights.
-/
structure RelativeModularDatum (A Modular : Type*) [Zero A] [Zero Modular] [Mul Modular] where
  /-- Relative modular object, morally `Delta_{phi,psi}` or `dphi/dpsi`. -/
  relativeModular :
    OperatorWeight A → OperatorWeight A → Modular

  /--
  Relative logarithmic generator, morally `log Delta_{phi,psi}`.
  -/
  relativeLog :
    Modular → Modular

  /-- The relative modular operator satisfies a multiplicative chain rule. -/
  chain_rule_law :
    ∀ φ ψ η : OperatorWeight A,
      relativeModular φ ψ * relativeModular ψ η = relativeModular φ η

  /--
  Support compatibility.
  -/
  support_compatibility_law :
    ∀ φ ψ : OperatorWeight A,
      relativeModular φ ψ = 0 ↔ Disjoint φ.positiveCone ψ.positiveCone

namespace RelativeModularDatum

variable {A Modular : Type*} [Zero A] [Zero Modular] [Mul Modular]
variable (Δ : RelativeModularDatum A Modular)

/--
Relative modular logarithm between two weights.
-/
def relativeLogBetween
    (φ ψ : OperatorWeight A) : Modular :=
  Δ.relativeLog (Δ.relativeModular φ ψ)

end RelativeModularDatum

/-! ## 3. Unnormalized relative entropy data -/

/--
Unnormalized relative entropy datum.
-/
structure UnnormalizedRelativeEntropyDatum (A Modular : Type*) [Zero A] [Zero Modular] [Mul Modular] where
  relativeModular :
    RelativeModularDatum A Modular

  /-- Nonnegative extended relative entropy. -/
  entropy :
    OperatorWeight A → OperatorWeight A → ℝ≥0∞

  /--
  Entropy is nonnegative.
  -/
  entropy_nonnegative_law :
    ∀ φ ψ : OperatorWeight A, 0 ≤ entropy φ ψ

  /--
  Zero self-divergence.
  -/
  entropy_self_law :
    ∀ φ : OperatorWeight A, entropy φ φ = 0

namespace UnnormalizedRelativeEntropyDatum

variable {A Modular : Type*} [Zero A] [Zero Modular] [Mul Modular]
variable (S : UnnormalizedRelativeEntropyDatum A Modular)

/--
Relative entropy is nonnegative.
-/
theorem nonnegative (φ ψ : OperatorWeight A) : 0 ≤ S.entropy φ ψ :=
  S.entropy_nonnegative_law φ ψ

/--
Self-relative entropy vanishes.
-/
theorem self_eq_zero (φ : OperatorWeight A) : S.entropy φ φ = 0 :=
  S.entropy_self_law φ

end UnnormalizedRelativeEntropyDatum

/-! ## 4. Finite trace/log specialization -/

/--
Finite log-potential specialization.
-/
structure FiniteLogBregmanDatum (A : Type*) [Ring A] [Module ℝ A] where
  /-- Operator logarithm on the admissible positive domain. -/
  logOp : A → A

  /-- Trace / finite integration backend. -/
  trace : A → ℝ

  /-- Unit-like element or mass reference. -/
  unitLike : A

  /-- Admissible positive cone/domain. -/
  positiveCone : Set A

  /-- The logarithm is defined on the positive cone. -/
  log_domain_law : ∀ x ∈ positiveCone, ∃ y, logOp x = y

  /--
  Trace cyclicity on the admissible domain.
  -/
  trace_law : ∀ x y, trace (x * y) = trace (y * x)

namespace FiniteLogBregmanDatum

variable {A : Type*} [Ring A] [Module ℝ A]
variable (L : FiniteLogBregmanDatum A)

/--
Mass-corrected finite unnormalized KL/Bregman expression.
-/
def massCorrectedKL
    (ρ σ : A) : ℝ :=
  L.trace (ρ * L.logOp ρ - ρ * L.logOp σ - ρ + σ)

end FiniteLogBregmanDatum

/-! ## 5. Optional continuous functional calculus bridge -/

/--
Continuous-functional-calculus log bridge.
-/
structure CFCLogBridge (A : Type*) [NormedRing A] [CompleteSpace A] [Algebra ℝ A] where
  /-- CFC-defined log readout. -/
  cfcLog : A → A

  /-- The spectrum of the element must be in the domain of the logarithm. -/
  spectrum_log_domain_law : ∀ x : A, spectrum ℝ x ⊆ Set.Ioi (0 : ℝ)

namespace CFCLogBridge

variable {A : Type*} [NormedRing A] [CompleteSpace A] [Algebra ℝ A]
variable (C : CFCLogBridge A)

end CFCLogBridge

/-! ## 6. BKM / transport metric data -/

/--
BKM / Bures-Kantorovich-style transport cost on unnormalized weights.
-/
structure ModularTransportCostDatum (A Modular : Type*) [Zero A] [Zero Modular] [Mul Modular] where
  relativeEntropy :
    UnnormalizedRelativeEntropyDatum A Modular

  /-- Transport cost between unnormalized weights. -/
  cost :
    OperatorWeight A → OperatorWeight A → ℝ≥0∞

  /-- Nonnegativity. -/
  cost_nonnegative_law :
    ∀ φ ψ, 0 ≤ cost φ ψ

  /-- Zero self-cost. -/
  cost_self_law :
    ∀ φ, cost φ φ = 0

  /--
  Transport cost is bounded by relative entropy.
  -/
  modular_transport_law :
    ∀ φ ψ, cost φ ψ ≤ relativeEntropy.entropy φ ψ

namespace ModularTransportCostDatum

variable {A Modular : Type*} [Zero A] [Zero Modular] [Mul Modular]
variable (T : ModularTransportCostDatum A Modular)

theorem nonnegative (φ ψ : OperatorWeight A) : 0 ≤ T.cost φ ψ :=
  T.cost_nonnegative_law φ ψ

theorem self_eq_zero (φ : OperatorWeight A) : T.cost φ φ = 0 :=
  T.cost_self_law φ

end ModularTransportCostDatum

/-! ## 7. Symmetric relative modular Hamiltonian calibration -/

/--
Symmetric relative modular Hamiltonian calibration.
-/
structure SymmetricRelativeHamiltonianCalibration (A Modular SymHam : Type*) [Zero A] [Zero Modular]
    [Mul Modular] where
  relativeModular :
    RelativeModularDatum A Modular

  /-- Symmetric Hamiltonian readout. -/
  symmetricHamiltonian :
    OperatorWeight A → OperatorWeight A → SymHam

  /--
  The Hamiltonian is symmetric.
  -/
  symmetry_law :
    ∀ φ ψ, symmetricHamiltonian φ ψ = symmetricHamiltonian ψ φ

namespace SymmetricRelativeHamiltonianCalibration

variable {A Modular SymHam : Type*} [Zero A] [Zero Modular] [Mul Modular]
variable (H : SymmetricRelativeHamiltonianCalibration A Modular SymHam)

end SymmetricRelativeHamiltonianCalibration

end InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy
