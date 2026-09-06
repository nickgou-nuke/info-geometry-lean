import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import InfoGeometry.Canonical.PositiveEnergyMellinKernel

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-!
# Topology of the positive-energy Mellin kernel

The scalar kernel is continuous on the physically relevant positive-energy
domain.  This file does not introduce an integral transform or a soft limit.
-/

/-- The positive-energy half-line. -/
def positiveEnergyLocus : Set ℝ := Set.Ioi 0

theorem isOpen_positiveEnergyLocus : IsOpen positiveEnergyLocus := by
  exact isOpen_Ioi

/-- Joint continuity of `ω ^ (Δ - 1)` on positive energy. -/
theorem continuousOn_mellinKernel :
    ContinuousOn
      (fun p : ℝ × ℝ => mellinKernel p.1 p.2)
      (positiveEnergyLocus ×ˢ (Set.univ : Set ℝ)) := by
  intro p hp
  have hpos : 0 < p.1 := hp.1
  have hne : p.1 ≠ 0 := ne_of_gt hpos
  have hpow : ContinuousAt
      (fun q : ℝ × ℝ => q.1 ^ (q.2 - 1)) p := by
    exact continuous_fst.continuousAt.rpow
      (continuous_snd.continuousAt.sub continuousAt_const) (Or.inl hne)
  simpa [positiveEnergyLocus, mellinKernel] using hpow.continuousWithinAt

end InfoGeometry.Topology
