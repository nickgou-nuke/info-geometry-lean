import InfoGeometry.Canonical.BCFWAffineChannelPole

namespace InfoGeometry.Topology.BCFWShiftTopological

open InfoGeometry.Canonical

theorem continuous_bcfwChannelInvariant (P_sq slope : ℂ) :
    Continuous (bcfwChannelInvariant P_sq slope) := by
  unfold bcfwChannelInvariant
  fun_prop

theorem bcfwChannelPole_locus_isClosed (P_sq slope : ℂ) :
    IsClosed {z : ℂ | IsBCFWChannelPole P_sq slope z} := by
  change IsClosed
    ((bcfwChannelInvariant P_sq slope) ⁻¹' ({0} : Set ℂ))
  exact isClosed_singleton.preimage
    (continuous_bcfwChannelInvariant P_sq slope)

theorem bcfwChannelPole_locus_eq_singleton
    (P_sq slope : ℂ) (hslope : slope ≠ 0) :
    {z : ℂ | IsBCFWChannelPole P_sq slope z} = {-P_sq / slope} := by
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr
      (bcfw_channel_pole_unique P_sq slope z hslope hz)
  · intro hz
    have hz' : z = -P_sq / slope := Set.mem_singleton_iff.mp hz
    simpa [hz'] using bcfw_channel_pole_value P_sq slope hslope

theorem isCompact_bcfwChannelPole_locus_inter
    (P_sq slope : ℂ) (s : Set ℂ) (hs : IsCompact s) :
    IsCompact (s ∩ {z : ℂ | IsBCFWChannelPole P_sq slope z}) :=
  hs.inter_right (bcfwChannelPole_locus_isClosed P_sq slope)

theorem isConnected_bcfwChannelPole_locus
    (P_sq slope : ℂ) (hslope : slope ≠ 0) :
    IsConnected {z : ℂ | IsBCFWChannelPole P_sq slope z} := by
  rw [bcfwChannelPole_locus_eq_singleton P_sq slope hslope]
  exact isConnected_singleton

end InfoGeometry.Topology.BCFWShiftTopological
