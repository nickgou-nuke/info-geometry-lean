import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
import InfoGeometry.Dynamics.SouriauDiracHodge

noncomputable section

namespace InfoGeometry.Dynamics.SouriauAPSBoundary

open Filter
open InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
open InfoGeometry.Dynamics.SouriauDiracHodge

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [InfoGeometry.Krein.KreinSpace H]

theorem boundary_index_vanishes
    (D : KreinOperatorData H)
    (trace : (H →L[ℝ] H) → ℝ)
    (etaInvariant : ℝ)
    (h_eta : etaInvariant = 0)
    (h_boundary : D.indexPairing trace = etaInvariant) :
    D.indexPairing trace = 0 := by
  rw [h_boundary, h_eta]

theorem cylindrical_end_aps_package
    (D : KreinOperatorData H)
    (trace : (H →L[ℝ] H) → ℝ)
    (etaInvariant : ℝ)
    (h_eta : etaInvariant = 0)
    (h_boundary : D.indexPairing trace = etaInvariant) :
    Tendsto thermalCayley atTop (nhds (1 : ℝ)) ∧
      Tendsto
        (fun beta : ℝ => ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
        atTop (nhds 0) ∧
      D.indexPairing trace = 0 := by
  exact ⟨thermalCayley_tendsto_one,
    D.zero_temperature_anomaly_cancellation,
    boundary_index_vanishes D trace etaInvariant h_eta h_boundary⟩

theorem cylindrical_end_aps_readout
    (D : KreinOperatorData H)
    (trace : (H →L[ℝ] H) → ℝ)
    (etaInvariant : ℝ)
    (h_eta : etaInvariant = 0)
    (h_boundary : D.indexPairing trace = etaInvariant) :
    Tendsto thermalCayley atTop (nhds (1 : ℝ)) ∧
      Tendsto
        (fun beta : ℝ => ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
        atTop (nhds 0) ∧
      D.indexPairing trace = 0 := by
  exact cylindrical_end_aps_package D trace etaInvariant h_eta h_boundary

end InfoGeometry.Dynamics.SouriauAPSBoundary
