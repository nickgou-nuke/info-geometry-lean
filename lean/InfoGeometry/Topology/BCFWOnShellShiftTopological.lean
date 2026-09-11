import InfoGeometry.Canonical.BCFWOnShellShift
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.BCFWOnShellShift

open InfoGeometry.Canonical

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [MomentumSpace V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousSub V]
  [ContinuousSMul ℂ V]

omit [ContinuousSub V] in
theorem continuous_shiftedPi (data : BCFWShiftData V) :
    Continuous (fun z : ℂ => shiftedPi data z) := by
  unfold shiftedPi
  exact continuous_const.add (continuous_id.smul continuous_const)

omit [ContinuousAdd V] in
theorem continuous_shiftedPj (data : BCFWShiftData V) :
    Continuous (fun z : ℂ => shiftedPj data z) := by
  unfold shiftedPj
  exact continuous_const.sub (continuous_id.smul continuous_const)

omit [ContinuousSub V] in
theorem continuous_shiftedChannel (data : BCFWShiftData V) (PI : V) :
    Continuous (fun z : ℂ => shiftedChannel data PI z) := by
  unfold shiftedChannel
  exact continuous_const.add (continuous_id.smul continuous_const)

omit [ContinuousSub V] in
theorem continuous_shiftedChannel_quadratic
    (data : BCFWShiftData V) (PI : V)
    (hinner : Continuous (fun x : V => inner x x)) :
    Continuous (fun z : ℂ =>
      inner (shiftedChannel data PI z) (shiftedChannel data PI z)) := by
  exact hinner.comp (continuous_shiftedChannel data PI)

omit [ContinuousSub V] in
theorem isClosed_shiftedChannel_onShell_locus
    (data : BCFWShiftData V) (PI : V)
    (hinner : Continuous (fun x : V => inner x x)) :
    IsClosed {z : ℂ |
      inner (shiftedChannel data PI z) (shiftedChannel data PI z) = 0} := by
  exact isClosed_singleton.preimage
    (continuous_shiftedChannel_quadratic data PI hinner)

omit [ContinuousSub V] in
theorem isCompact_shiftedChannel_onShell_locus_inter
    (data : BCFWShiftData V) (PI : V) (s : Set ℂ)
    (hs : IsCompact s)
    (hinner : Continuous (fun x : V => inner x x)) :
    IsCompact (s ∩ {z : ℂ |
      inner (shiftedChannel data PI z) (shiftedChannel data PI z) = 0}) := by
  exact hs.inter_right (isClosed_shiftedChannel_onShell_locus data PI hinner)

end InfoGeometry.Topology.BCFWOnShellShift
