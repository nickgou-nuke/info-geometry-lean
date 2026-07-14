import InfoGeometry.BostConnes.BostConnesThermofield

/-!
# RestoreBostConnesParity

Small sandbox packet for Möbius/Liouville and modular-flow readbacks.
-/

namespace InfoGeometry.Restore.BostConnesParity

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Möbius decomposes as squarefree projection times Liouville parity. -/
theorem moebius_decomposition_restore (n : ℕ) :
    ArithmeticFunction.moebius n =
      InfoGeometry.BostConnes.squarefreeProj n *
        InfoGeometry.BostConnes.liouvilleParity n := by
  exact BostConnesThermofield.moebius_decomposition n

/-- Liouville grading commutes with modular flow. -/
theorem thermal_anomaly_protection_restore (t : ℝ) (n : ℕ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℂ) *
        BostConnesThermofield.modular_phase t n =
      BostConnesThermofield.modular_phase t n *
        (InfoGeometry.BostConnes.liouvilleParity n : ℂ) := by
  exact BostConnesThermofield.liouville_commutes_modular_flow n t

end InfoGeometry.Restore.BostConnesParity
