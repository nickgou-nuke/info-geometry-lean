import InfoGeometry.Canonical.BCFWOnShellShift
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.BCFWOnShellShift

open InfoGeometry.Canonical

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (B : LinearMap.BilinForm ℂ V)
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousSub V]
  [ContinuousSMul ℂ V]

omit [ContinuousSub V] in
theorem continuous_shiftedPi (pi q : V) :
    Continuous (fun z : ℂ => shiftedPi pi q z) := by
  unfold shiftedPi
  exact continuous_const.add (continuous_id.smul continuous_const)

omit [ContinuousAdd V] in
theorem continuous_shiftedPj (pj q : V) :
    Continuous (fun z : ℂ => shiftedPj pj q z) := by
  unfold shiftedPj
  exact continuous_const.sub (continuous_id.smul continuous_const)

omit [ContinuousSub V] in
theorem continuous_shiftedChannel (PI q : V) :
    Continuous (fun z : ℂ => shiftedChannel PI q z) := by
  unfold shiftedChannel
  exact continuous_const.add (continuous_id.smul continuous_const)

omit [ContinuousSub V] in
theorem continuous_shiftedChannel_quadratic
    (PI q : V)
    (hinner : Continuous (fun x : V => B x x)) :
    Continuous (fun z : ℂ =>
      B (shiftedChannel PI q z) (shiftedChannel PI q z)) := by
  exact hinner.comp (continuous_shiftedChannel PI q)

omit [ContinuousSub V] in
theorem isClosed_shiftedChannel_onShell_locus
    (PI q : V)
    (hinner : Continuous (fun x : V => B x x)) :
    IsClosed {z : ℂ |
      B (shiftedChannel PI q z) (shiftedChannel PI q z) = 0} := by
  exact isClosed_singleton.preimage
    (continuous_shiftedChannel_quadratic B PI q hinner)

omit [ContinuousSub V] in
theorem isCompact_shiftedChannel_onShell_locus_inter
    (PI q : V) (s : Set ℂ)
    (hs : IsCompact s)
    (hinner : Continuous (fun x : V => B x x)) :
    IsCompact (s ∩ {z : ℂ |
      B (shiftedChannel PI q z) (shiftedChannel PI q z) = 0}) := by
  exact hs.inter_right (isClosed_shiftedChannel_onShell_locus B PI q hinner)

end InfoGeometry.Topology.BCFWOnShellShift
