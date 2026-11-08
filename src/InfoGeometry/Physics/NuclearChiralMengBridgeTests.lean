import InfoGeometry.Physics.NuclearChiralMengBridge

namespace InfoGeometry.Physics.NuclearChiralMengBridge.Tests

open InfoGeometry.Physics.NuclearChiralMengBridge
open InfoGeometry.Physics.BiWaveRamanujan

example :
    Archetype.chpInvolutions ≤ Archetype.fiveGradeCarrier ∧
    Archetype.fiveGradeCarrier ≤ Archetype.quasiparticlePhonon ∧
    Archetype.quasiparticlePhonon ≤ Archetype.solovievCompression ∧
    Archetype.solovievCompression ≤ Archetype.twinWaveKMS ∧
    Archetype.twinWaveKMS ≤ Archetype.operatorZornReadout :=
  causal_chain

example (overlap : ℂ) (h : overlap ≠ 0) :
    weakValue overlap overlap = 1 := by
  exact weakValue_forward_projector overlap h

example (t : ℝ) : ‖boundaryIntertwiner t‖ = 1 := by
  exact boundaryIntertwiner_unitary t

end InfoGeometry.Physics.NuclearChiralMengBridge.Tests
