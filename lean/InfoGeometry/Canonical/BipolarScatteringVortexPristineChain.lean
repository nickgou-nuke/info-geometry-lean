import InfoGeometry.Canonical.BipolarLoxodromicAndreevBridge
import InfoGeometry.Canonical.BipolarTwoSheetCore
import InfoGeometry.Analysis.BipolarCriticalWindowsVortex
import InfoGeometry.Analysis.BipolarOrthogonalFlowSplit
import InfoGeometry.Canonical.BipolarTwoPortScattering
import InfoGeometry.Canonical.BipolarPristineMathematicalChain
import Mathlib.Tactic

/-!
# Pristine scattering/vortex chain over the bipolar conformal spine

This capstone reconstructs the exact mathematics behind a second informal stream
that mixed loxodromic Möbius modes, critical-line zeros, Aharonov--Bohm vortices,
Andreev reflection, two-port scattering, and metriplectic language.

The organizing carrier is the repository-owned two-sheet `ChiralSheet` double
cover.  On the critical line the base point is fixed while the lifted mirror
exchanges the two sheets.  Incoming/outgoing and particle/hole language are
therefore adapters to one common `Z/2` sheet architecture, not primitive
identifications.

The theorem-safe hierarchy is:

1. `q(s)` is the loxodromic scalar `exp(eta+i theta)`;
2. the two-sheet lifted mirror swaps sheets and reflects the base;
3. on the critical line the base is fixed but the two lifts are exchanged;
4. particle-hole phase closure is an anti-linear realization of sheet exchange;
5. a critical-line point is merely a marked node unless an actual zero law is
   supplied;
6. a vortex at such a node requires a separate translated pole/residue datum;
7. a critical window can carry an ordinary unitary two-port scattering block;
8. a transfer block may instead satisfy determinant-one `J`-unitarity;
9. the planar gradient and Hodge-rotated channels are orthogonal and equal-norm.

No RH, automatic vortex assignment, bound-state theorem, BdG spectral theorem,
Maxwell duality, or dissipative second-law statement is inferred.
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
open InfoGeometry.Canonical.BipolarTwoPortScattering
open InfoGeometry.OperatorAlgebra.AndreevBoundary

/-- The two-sheet core is the common carrier: the critical base point is fixed
while its plus/minus lifts are exchanged, and their Cayley readouts are inverse. -/
theorem pristine_two_sheet_core (y : ℝ) :
    sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) ∧
      sheetCayleyReadout (minusLift (criticalLine y)) =
        (sheetCayleyReadout (plusLift (criticalLine y)))⁻¹ ∧
      antiLinearDeck (criticalSheetPhase y) = criticalSheetPhase y := by
  exact two_sheet_core_packet y

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

/-- Master packet for the recovered second stream, now explicitly rooted in the
two-sheet cover. -/
theorem pristine_scattering_vortex_master
    {s : ℂ} (hs : s ∈ punctured01)
    {r t : ℂ} (hS : ScatteringNormalized r t)
    (α x y : ℝ) :
    sheetMirror (plusLift (criticalLine y)) = minusLift (criticalLine y) ∧
      bipolarLoxodromic s = crossRatio01 s ∧
      bipolarLoxodromic (mirror s) =
        (Complex.conj (bipolarLoxodromic s))⁻¹ ∧
      (scatteringBlock r t)ᴴ * scatteringBlock r t = 1 ∧
      IsSpecialJUnitary (hyperbolicTransfer α) ∧
      planeDot (metricFlow x y) (hamiltonianFlow x y) = 0 := by
  exact ⟨sheetMirror_plus_criticalLine y,
    bipolarLoxodromic_eq_crossRatio01 hs,
    bipolarLoxodromic_mirror hs,
    scatteringBlock_unitary hS,
    hyperbolicTransfer_special α,
    metric_hamiltonian_orthogonal x y⟩

end InfoGeometry.Canonical.BipolarScatteringVortexPristineChain
