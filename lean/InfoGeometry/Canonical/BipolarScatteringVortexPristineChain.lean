import InfoGeometry.Canonical.BipolarLoxodromicAndreevBridge
import InfoGeometry.Canonical.BipolarTwoSheetCore
import InfoGeometry.Canonical.BipolarTwoSheetCausalBulkBridge
import InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge
import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.Analysis.BipolarCriticalWindowsVortex
import InfoGeometry.Analysis.BipolarOrthogonalFlowSplit
import InfoGeometry.Canonical.BipolarTwoPortScattering
import InfoGeometry.Canonical.BipolarPristineMathematicalChain
import Mathlib.Tactic

/-!
# Pristine scattering/vortex chain over the bipolar conformal spine

This capstone reconstructs the exact mathematics behind a second informal stream
that mixed loxodromic Möbius modes, critical-line zeros, Aharonov--Bohm vortices,
Andreev reflection, two-port scattering, metriplectic language, and a two-sheet
parabolic causal-boundary intuition.

The organizing carrier is the repository-owned two-sheet `ChiralSheet` double
cover. On the critical line the base point is fixed while the lifted mirror
exchanges the two sheets. Each sheet is then welded to one of the two opposite
parabolic nilpotent generators `σPlus`, `σMinus`. Their even/odd combinations
recover independent transverse Pauli directions, while the critical unit phase
lifts to a null representative in the repository-owned four-real-coordinate
causal carrier. The logarithmic Cartan generator then acts on those two sheets
with opposite infinitesimal weights and the repository-owned half-log lift
integrates them to the exact multiplicative Cayley weights `q` and `q⁻¹`.

No RH, automatic vortex assignment, bound-state theorem, BdG spectral theorem,
Maxwell duality, AdS/CFT theorem, Einstein dynamics, or dissipative second-law
statement is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarScatteringVortexPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Analysis.BipolarCriticalWindowsVortex
open InfoGeometry.Analysis.BipolarOrthogonalFlowSplit
open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.Canonical.BipolarLoxodromicAndreevBridge
open InfoGeometry.Canonical.BipolarTwoSheetCore
open InfoGeometry.Canonical.BipolarTwoSheetCausalBulkBridge
open InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarTwoPortScattering
open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.Topology.Weyl
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Algebra.RealPauliCausalCone

/-- The two-sheet core is the common carrier: the critical base point is fixed
while its plus/minus lifts are exchanged, and their Cayley readouts are inverse. -/
theorem pristine_two_sheet_core (y : ℝ) :
    sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) ∧
      sheetCayleyReadout (minusLift (criticalLine y)) =
        (sheetCayleyReadout (plusLift (criticalLine y)))⁻¹ ∧
      antiLinearDeck (criticalSheetPhase y) = criticalSheetPhase y := by
  exact two_sheet_core_packet y

/-- The two-sheet cover is welded to the parabolic causal boundary. -/
theorem pristine_two_sheet_parabolic_causal_core (y : ℝ) :
    sheetParabolicGenerator ChiralSheet.plus.swap =
      (sheetParabolicGenerator ChiralSheet.plus)ᴴ ∧
    sheetParabolicGenerator ChiralSheet.plus *
        sheetParabolicGenerator ChiralSheet.minus +
      sheetParabolicGenerator ChiralSheet.minus *
        sheetParabolicGenerator ChiralSheet.plus = 1 ∧
    sheetParabolicGenerator ChiralSheet.plus +
      sheetParabolicGenerator ChiralSheet.minus = σ1 ∧
    detMinkowski (criticalNullBulk y) = 0 := by
  exact two_sheet_parabolic_boundary_reconstruction y

/-- The doubled parabolic pair, together with scalar and grading directions,
reconstructs every `2 × 2` complex matrix. -/
theorem pristine_two_sheet_full_matrix_reconstruction
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ a h p m : ℂ,
      M = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + h • σ3c +
        p • sheetParabolicGenerator ChiralSheet.plus +
        m • sheetParabolicGenerator ChiralSheet.minus := by
  exact two_sheet_generates_full_pauli_carrier M

/-- Exact closure from logarithmic coordinates to infinitesimal and finite
adjoint weights on the two parabolic sheets. -/
theorem pristine_logarithmic_adjoint_flow_core
    {s : ℂ} (hs : s ∈ punctured01) :
    (logarithmicCartanGenerator s * σPlus - σPlus * logarithmicCartanGenerator s =
      bipolarLog s • σPlus) ∧
    (logarithmicCartanGenerator s * σMinus - σMinus * logarithmicCartanGenerator s =
      (-bipolarLog s) • σMinus) ∧
    finiteAdjointFlow s σPlus = crossRatio01 s • σPlus ∧
    finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  exact logarithmic_cartan_adjoint_flow_packet hs

/-- Loxodromic/reflection core with the critical-line unit-modulus specialization. -/
theorem pristine_loxodromic_reflection_core
    {s : ℂ} (hs : s ∈ punctured01) (y : ℝ) :
    bipolarLoxodromic s = crossRatio01 s ∧
      bipolarLoxodromic (mirror s) =
        (Complex.conj (bipolarLoxodromic s))⁻¹ ∧
      ‖bipolarLoxodromic (criticalLine y)‖ = 1 := by
  exact ⟨bipolarLoxodromic_eq_crossRatio01 hs,
    bipolarLoxodromic_mirror hs,
    bipolarLoxodromic_criticalLine_unit y⟩

/-- Particle-hole phase conjugation is a distinct involutive realization of the
same two-sheet exchange architecture. -/
theorem pristine_particle_hole_core (y : ℝ) :
    phaseAndreevFlip (phaseAndreevFlip (criticalPhasePair y)) = criticalPhasePair y ∧
      phaseAndreevFlip (criticalPhasePair y) = criticalPhasePair y := by
  exact ⟨phaseAndreevFlip_sq (criticalPhasePair y), criticalPhasePair_fixed y⟩

/-- Marked critical-line nodes are regular points of the original two-puncture
logarithmic differential; optional vortex poles are separate data. -/
theorem pristine_node_vortex_separation_core (γ : ℝ) :
    (criticalNode γ).re = 1 / 2 ∧
      (criticalNode γ).im = γ ∧
      criticalNode γ ∈ punctured01 ∧
      dlog01 (criticalNode γ) ≠ 0 := by
  exact critical_node_separation_packet γ

/-- An attached translated pole really carries its supplied residue. -/
theorem pristine_translated_vortex_core
    (V : CriticalVortexDatum) {z : ℂ} (hz : z ≠ V.center) :
    (z - V.center) * V.coeff z = V.residue := by
  exact V.local_residue_readout hz

/-- Ordinary unitary scattering and `J`-unitary transfer are separate matrix laws. -/
theorem pristine_scattering_transfer_core
    {r t : ℂ} (h : ScatteringNormalized r t) (α : ℝ) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t = 1 ∧
      Matrix.det (scatteringBlock r t) = 1 ∧
      IsSpecialJUnitary (hyperbolicTransfer α) := by
  exact scattering_transfer_packet h α

/-- Zero transmission implies unit reflection probability, and nothing stronger. -/
theorem pristine_zero_transmission_core
    {r t : ℂ} (h : ScatteringNormalized r t) (ht : t = 0) :
    Complex.normSq r = 1 := by
  exact perfect_reflection_of_zero_transmission h ht

/-- Corrected metric/Hamiltonian-style planar split. -/
theorem pristine_orthogonal_flow_core (x y : ℝ) :
    hamiltonianFlow x y = dPsiCoeff x y ∧
      planeDot (metricFlow x y) (hamiltonianFlow x y) = 0 ∧
      planeNormSq (metricFlow x y) = planeNormSq (hamiltonianFlow x y) := by
  exact orthogonal_flow_packet x y

/-- On the critical line the normal gradient channel survives while the rotated
channel is tangential; only the tangential component of the gradient vanishes. -/
theorem pristine_critical_flow_core (y : ℝ) :
    metricFlow (1 / 2) y = ![-(1 / ((1 / 4 : ℝ) + y ^ 2)), 0] ∧
      hamiltonianFlow (1 / 2) y = ![0, 1 / ((1 / 4 : ℝ) + y ^ 2)] ∧
      metricFlow (1 / 2) y ≠ 0 := by
  exact ⟨metricFlow_half y, hamiltonianFlow_half y, metricFlow_half_ne_zero y⟩

end InfoGeometry.Canonical.BipolarScatteringVortexPristineChain
