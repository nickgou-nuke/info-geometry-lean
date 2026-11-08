import InfoGeometry.Physics.Section36ConformalCoordinateAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Section 37 repaired: reviewer-response finite audit

The source is a response to reviewers.  It proposes future work on action
variation, conformal Dirac equations, exact entropy/time-dilation, Kähler
integrability, and chiral arrow-of-time derivations.  Those are not closed by
this note and are not asserted here.

This file extracts the finite algebra that can be checked now:

* the matrix trace identity
  `Tr(([H,ρ])L) = Tr(H(ρL-Lρ))` for `2 × 2` complex matrices;
* a finite von-Neumann entropy-production shadow and its cyclic/readout form;
* exact vanishing when `ρ` commutes with the supplied `logρ` readout;
* exact vanishing when the two Hamiltonian components agree, i.e. when the
  Section 36 Hamiltonian-asymmetry readout is zero.

No theorem below proves an actual von Neumann entropy derivative, a logarithm
functional calculus theorem, a variational Euler--Lagrange equation, an Einstein
or Dirac equation, Kähler integrability, CP violation, or an arrow of time.
-/

noncomputable section

namespace InfoGeometry.Physics.Section37ReviewerResponseFiniteAudit

open Matrix Complex
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section36ConformalCoordinateAlgebra

/-- Local unambiguous name for the Section 31 matrix commutator. -/
abbrev matrixCommutator : Mat2 → Mat2 → Mat2 :=
  InfoGeometry.Physics.Section31UnifiedMatrixDynamics.commutator

/-- Three-factor trace/commutator cyclicity for the concrete `2 × 2` carrier. -/
theorem trace_commutator_mul_eq_trace_mul_commutator (A B C : Mat2) :
    trace ((A * B - B * A) * C) = trace (A * (B * C - C * B)) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Finite entropy-production shadow from the von-Neumann commutator. -/
def entropyProductionVonNeumann (H rho logRho : Mat2) : ℂ :=
  Complex.I * trace ((matrixCommutator H rho) * logRho)

/-- Cyclic/readout form of the same finite entropy-production shadow. -/
def entropyProductionCyclic (H rho logRho : Mat2) : ℂ :=
  Complex.I * trace (H * (rho * logRho - logRho * rho))

/-- The two finite entropy-production shadows agree by trace cyclicity. -/
theorem entropyProductionVonNeumann_eq_cyclic (H rho logRho : Mat2) :
    entropyProductionVonNeumann H rho logRho =
      entropyProductionCyclic H rho logRho := by
  simp [entropyProductionVonNeumann, entropyProductionCyclic, matrixCommutator,
    InfoGeometry.Physics.Section31UnifiedMatrixDynamics.commutator]
  rw [trace_commutator_mul_eq_trace_mul_commutator]

/-- If `ρ` commutes with its supplied finite `logρ` readout, the shadow vanishes. -/
theorem entropyProductionVonNeumann_zero_of_rho_commutes_logRho
    (H rho logRho : Mat2) (hcomm : rho * logRho = logRho * rho) :
    entropyProductionVonNeumann H rho logRho = 0 := by
  rw [entropyProductionVonNeumann_eq_cyclic]
  simp [entropyProductionCyclic, hcomm]

/-- If the two Hamiltonian components agree, the asymmetry-driven shadow vanishes. -/
theorem entropyProductionVonNeumann_zero_of_equal_hamiltonians
    (H1 H2 rho logRho : Mat2) (hH : H1 = H2) :
    entropyProductionVonNeumann (hamiltonianAsymmetry H1 H2) rho logRho = 0 := by
  simp [entropyProductionVonNeumann, hamiltonianAsymmetry, hH,
    matrixCommutator, InfoGeometry.Physics.Section31UnifiedMatrixDynamics.commutator]

/-- The finite reviewer-response packet: cyclicity plus two exact zero tests. -/
theorem repaired_section37_reviewer_response_packet
    (H H1 H2 rho logRho : Mat2)
    (hcomm : rho * logRho = logRho * rho) (hH : H1 = H2) :
    entropyProductionVonNeumann H rho logRho = entropyProductionCyclic H rho logRho ∧
    entropyProductionVonNeumann H rho logRho = 0 ∧
    entropyProductionVonNeumann (hamiltonianAsymmetry H1 H2) rho logRho = 0 := by
  exact ⟨entropyProductionVonNeumann_eq_cyclic H rho logRho,
    entropyProductionVonNeumann_zero_of_rho_commutes_logRho H rho logRho hcomm,
    entropyProductionVonNeumann_zero_of_equal_hamiltonians H1 H2 rho logRho hH⟩

end InfoGeometry.Physics.Section37ReviewerResponseFiniteAudit

end noncomputable section
