import InfoGeometry.Canonical.PeirceBCFWShiftSpecialization
import InfoGeometry.Topology.PeirceNullConeKinematicTopological
import InfoGeometry.Topology.BCFWOnShellShiftTopological

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! Topological transport for the typed Peirce-to-BCFW coordinate bridge.
These lemmas establish continuity of the coordinate maps and quadratic readout;
they do not assert a meromorphic amplitude or a residue recursion. -/

theorem continuous_complexifyChannelCoordinates :
    Continuous complexifyChannelCoordinates := by
  unfold complexifyChannelCoordinates
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

theorem continuous_complexifiedChannel :
    Continuous complexifiedChannel := by
  exact continuous_complexifyChannelCoordinates.comp
    continuous_channelCoordinates

theorem continuous_peirceKinematicInner_self :
    Continuous (fun p : PeirceKinematicMomentum =>
      peirceKinematicInner p p) := by
  unfold peirceKinematicInner
  fun_prop

theorem continuous_complexifiedChannel_quadratic :
    Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      peirceKinematicInner (complexifiedChannel M)
        (complexifiedChannel M)) := by
  exact continuous_peirceKinematicInner_self.comp
    continuous_complexifiedChannel

theorem isClosed_complexifiedChannel_onShellLocus :
    IsClosed {M : Matrix (Fin 2) (Fin 2) ℝ |
      peirceKinematicInner (complexifiedChannel M)
        (complexifiedChannel M) = 0} := by
  exact isClosed_singleton.preimage
    continuous_complexifiedChannel_quadratic

theorem isClosed_peirce_shiftedChannel_onShell_locus
    (data : PeirceBCFWShiftParameters)
    (PI : PeirceKinematicMomentum) :
    IsClosed {z : ℂ |
      peirceKinematicInner
          (shiftedChannel data.toBCFWShiftData PI z)
          (shiftedChannel data.toBCFWShiftData PI z) = 0} := by
  exact InfoGeometry.Topology.BCFWOnShellShift.isClosed_shiftedChannel_onShell_locus
    data.toBCFWShiftData PI continuous_peirceKinematicInner_self

end InfoGeometry.Topology
