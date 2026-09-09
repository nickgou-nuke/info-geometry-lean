import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Topology.Pin55TopologicalGroups
import InfoGeometry.Clifford.Cl55RealSplitPinAction

noncomputable section

namespace InfoGeometry.Topology.Pin55ContinuityLemmas

open InfoGeometry.Clifford.Clifford55

theorem continuous_clifford_mul :
    Continuous (fun p : Cl55 × Cl55 => p.1 * p.2) :=
  continuous_mul

theorem continuous_clifford_involute :
    Continuous (CliffordAlgebra.involute (Q := Q55)) :=
  (CliffordAlgebra.involute (Q := Q55)).toLinearMap.continuous_of_finiteDimensional

theorem continuous_realSplitPin55_to_units :
    Continuous (fun g : realSplitPin55 => (g : Cl55ˣ)) :=
  continuous_subtype_val

theorem continuous_realSplitPin55_to_clifford :
    Continuous (fun g : realSplitPin55 => ((g : Cl55ˣ) : Cl55)) := by
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_realSplitPin_twisted_adj :
    Continuous (fun p : realSplitPin55 × V55 =>
      realSplitPinTwistedAdj p.1 p.2) := by
  unfold realSplitPinTwistedAdj
  have hleft : Continuous (fun p : realSplitPin55 × V55 =>
      CliffordAlgebra.involute (Q := Q55) ((p.1 : Cl55ˣ) : Cl55)) := by
    exact continuous_clifford_involute.comp
      (continuous_realSplitPin55_to_clifford.comp continuous_fst)
  have hvec : Continuous (fun p : realSplitPin55 × V55 =>
      ι55 p.2) := by
    exact (IsModuleTopology.continuous_of_linearMap ι55).comp continuous_snd
  have hinv : Continuous (fun p : realSplitPin55 × V55 =>
      (↑((p.1 : Cl55ˣ)⁻¹) : Cl55)) := by
    exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
  exact continuous_clifford_mul.comp₂
    (continuous_clifford_mul.comp₂ hleft hvec) hinv

end InfoGeometry.Topology.Pin55ContinuityLemmas
