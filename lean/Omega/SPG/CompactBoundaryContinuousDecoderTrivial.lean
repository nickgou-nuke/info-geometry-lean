import Mathlib.Tactic

namespace Omega.SPG

/-- A continuous additive decoder from a compact boundary into the additive reals is trivial once
its image is recognized as a compact subgroup of `ℝ`.
    thm:spg-compact-boundary-continuous-decoder-trivial -/
theorem paper_spg_compact_boundary_continuous_decoder_trivial
    {decoderTrivial boundaryCompact decoderContinuous decoderAdditive
      imageCompactSubgroup : Prop}
    (imageCompactSubgroup_of_boundary :
      boundaryCompact → decoderContinuous → decoderAdditive → imageCompactSubgroup)
    (trivial_of_compact_subgroup : imageCompactSubgroup → decoderTrivial)
    (hBoundaryCompact : boundaryCompact)
    (hDecoderContinuous : decoderContinuous)
    (hDecoderAdditive : decoderAdditive) : decoderTrivial := by
  exact trivial_of_compact_subgroup
    (imageCompactSubgroup_of_boundary
      hBoundaryCompact hDecoderContinuous hDecoderAdditive)

end Omega.SPG
