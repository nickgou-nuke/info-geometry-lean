import InfoGeometry.Physics.Section37ReviewerResponseFiniteAudit

/-!
# Section 38 repaired: finite stress-energy domain separation

The source attempts a continuum variational calculation for a density-matrix
matter action and then interprets the stress tensor through domain separation
between quantum operators and classical spacetime components.

This repaired file keeps only the finite, kernel-checkable algebra:

* quantum data live in the concrete `2 × 2` complex matrix carrier;
* `trace` is the explicit map from quantum operator products to classical
  scalar components;
* Section 34's compact density stress shadow is reused as the finite owner;
* an explicit `connectionVariation` component can be added as external data;
* if both the metric table and connection-variation table are symmetric, the
  full finite stress shadow is symmetric;
* if the connection-variation term is zero, the full stress reduces to the
  compact Section 34 stress tensor.

No continuum action variation, connection-variation formula, Fenchel--Legendre
ensemble theorem, eigenvector/vierbein theorem, entropy-flow theorem, or arrow of
time is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.Section38StressEnergyDomainSeparation

open Matrix Complex
open BigOperators
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section34StrengthenedFormalism

/-- Classical scalar codomain for finite stress-energy components. -/
abbrev ClassicalScalar := ℂ

/-- Quantum operator domain for density matrices and their finite derivatives. -/
abbrev QuantumOperator := Mat2

/-- Explicit quantum-to-classical readout used in the stress tensor: matrix trace. -/
def quantumTraceToClassical (A : QuantumOperator) : ClassicalScalar :=
  trace A

/-- Finite domain-separated stress datum.

This declaration carries four independent finite tables and no extra law; the
stress identities below are theorem owners, so the carrier is a native nested
product rather than a wrapper structure.
-/
abbrev DomainSeparatedStressDatum :=
  (SpacetimeIndex → SpacetimeIndex → ClassicalScalar) ×
    ((SpacetimeIndex → QuantumOperator) ×
      (ClassicalScalar × (SpacetimeIndex → SpacetimeIndex → ClassicalScalar)))

abbrev DomainSeparatedStressDatum.metric (D : DomainSeparatedStressDatum) := D.1
abbrev DomainSeparatedStressDatum.densityDerivative (D : DomainSeparatedStressDatum) := D.2.1
abbrev DomainSeparatedStressDatum.potential (D : DomainSeparatedStressDatum) := D.2.2.1
abbrev DomainSeparatedStressDatum.connectionVariation (D : DomainSeparatedStressDatum) := D.2.2.2

namespace DomainSeparatedStressDatum

/-- Kinetic trace scalar `g^{ab} Tr(ρ_aρ_b)` for the datum. -/
def kinetic (D : DomainSeparatedStressDatum) : ClassicalScalar :=
  kineticTrace D.metric D.densityDerivative

/-- Compact stress part, without explicit connection-variation data. -/
def compactStress (D : DomainSeparatedStressDatum) (mu nu : SpacetimeIndex) : ClassicalScalar :=
  densityStressShadow D.metric D.densityDerivative D.potential mu nu

/-- Full finite stress shadow including the supplied connection-variation term. -/
def fullStress (D : DomainSeparatedStressDatum) (mu nu : SpacetimeIndex) : ClassicalScalar :=
  D.compactStress mu nu + D.connectionVariation mu nu

/-- If connection variation is zero, the full stress is the compact stress. -/
theorem fullStress_eq_compact_of_zero_connectionVariation
    (D : DomainSeparatedStressDatum)
    (hzero : ∀ mu nu, D.connectionVariation mu nu = 0) (mu nu : SpacetimeIndex) :
    D.fullStress mu nu = D.compactStress mu nu := by
  simp [fullStress, hzero mu nu]

/-- The full stress is symmetric when metric and connection-variation tables are symmetric. -/
theorem fullStress_symmetric
    (D : DomainSeparatedStressDatum)
    (hmetric : ∀ mu nu, D.metric mu nu = D.metric nu mu)
    (hconn : ∀ mu nu, D.connectionVariation mu nu = D.connectionVariation nu mu)
    (mu nu : SpacetimeIndex) :
    D.fullStress mu nu = D.fullStress nu mu := by
  simp [fullStress, compactStress,
    densityStressShadow_symmetric D.metric D.densityDerivative D.potential hmetric mu nu,
    hconn mu nu]

end DomainSeparatedStressDatum

/-- Zero connection-variation table. -/
def zeroConnectionVariation : SpacetimeIndex → SpacetimeIndex → ClassicalScalar :=
  fun _ _ => 0

/-- Build a compact finite stress datum with no connection-variation term. -/
def compactStressDatum
    (metric : SpacetimeIndex → SpacetimeIndex → ClassicalScalar)
    (densityDerivative : SpacetimeIndex → QuantumOperator)
    (potential : ClassicalScalar) : DomainSeparatedStressDatum :=
  (metric, (densityDerivative, (potential, zeroConnectionVariation)))

end InfoGeometry.Physics.Section38StressEnergyDomainSeparation

end noncomputable section
