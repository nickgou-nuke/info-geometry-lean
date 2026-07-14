import InfoGeometry.Physics.HadjiivanovCuntzBridge
import InfoGeometry.Physics.HadjiivanovBostConnesBridge
import InfoGeometry.Physics.AmplituhedronBostConnes

/-!
# RestoreBundle

Tiny sandbox bundle for the Hadjiivanov/Bost-Connes zeta readout.
-/

namespace InfoGeometry.Restore.Bundle

open Matrix

/-- Bundled restored trace/zeta facts from the owner files. -/
theorem restore_bundle (β : ℂ) :
    InfoGeometry.Physics.Hadjiivanov.logBlockPartitionFunction ℂ = 0 ∧
    InfoGeometry.Physics.AmplituhedronBostConnes.all_loop_integrand_bost_connes_kms_state β =
      riemannZeta β := by
  constructor
  · exact InfoGeometry.Physics.Hadjiivanov.logBlockPartitionFunction_vanishes ℂ
  · rfl

end InfoGeometry.Restore.Bundle
