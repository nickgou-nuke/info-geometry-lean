import InfoGeometry.BostConnes.BostConnesThermofield

/-!
# RestoreBostConnesThermofield

Small sandbox packet for the Möbius/Liouville and reciprocal-zeta readbacks.
-/

namespace InfoGeometry.Restore.BostConnesThermofield

open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation

/-- Möbius decomposes as squarefree projection times Liouville parity. -/
theorem moebius_decomposition (n : ℕ) :
    ArithmeticFunction.moebius n =
      InfoGeometry.BostConnes.squarefreeProj n *
        InfoGeometry.BostConnes.liouvilleParity n := by
  exact InfoGeometry.BostConnes.moebius_eq_squarefreeProj_mul_liouvilleParity n

/-- The Bost-Connes Witten index is the reciprocal zeta readout. -/
theorem witten_index_eq_reciprocal_zeta_restore (beta : ℝ) (hbeta : beta > 1) :
    L ↗μ (beta : ℂ) = (riemannZeta (beta : ℂ))⁻¹ := by
  exact BostConnesThermofield.witten_index_eq_reciprocal_zeta beta hbeta

/-- Thermal anomaly protection: Liouville grading commutes with the modular flow. -/
theorem thermal_anomaly_protection_restore (t : ℝ) (n : ℕ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℂ) *
        BostConnesThermofield.modular_phase t n =
      BostConnesThermofield.modular_phase t n *
        (InfoGeometry.BostConnes.liouvilleParity n : ℂ) := by
  exact BostConnesThermofield.liouville_commutes_modular_flow n t

end InfoGeometry.Restore.BostConnesThermofield
