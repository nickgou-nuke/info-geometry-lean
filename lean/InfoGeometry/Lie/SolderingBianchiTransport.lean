import InfoGeometry.Lie.SplitAlgebraSolderingForm

/-!
# Additive Bianchi transport through the canonical soldering form

The canonical circular soldering is a linear equivalence, not a ring
equivalence.  Consequently it transports additive cyclic identities, but it
does not transport noncommutative curvature products.  The latter remain in
`CoordinateFreeConnectionChannels`, where the channel is a ring hom.
-/

namespace InfoGeometry.Lie.SplitAlgebraSolderingForm

/-! Transport a zero cyclic Bianchi sum through the canonical soldering. -/
theorem canonicalSoldering_map_cyclicSum_of_zero
    (x y z : SplitCarrier)
    (h : x + y + z = 0) :
    canonicalSoldering x + canonicalSoldering y + canonicalSoldering z = 0 := by
  calc
    canonicalSoldering x + canonicalSoldering y + canonicalSoldering z =
        canonicalSoldering (x + y + z) := by
          simp only [map_add]
    _ = canonicalSoldering 0 := by rw [h]
    _ = 0 := by simp

/-! The converse is available because soldering is a linear equivalence. -/
theorem canonicalSoldering_map_cyclicSum_iff
    (x y z : SplitCarrier) :
    canonicalSoldering x + canonicalSoldering y + canonicalSoldering z = 0 ↔
      x + y + z = 0 := by
  constructor
  · intro h
    have hs := congrArg canonicalSoldering.symm h
    simpa only [map_add, map_zero, canonicalSoldering.symm_apply_apply] using hs
  · intro h
    exact canonicalSoldering_map_cyclicSum_of_zero x y z h

end InfoGeometry.Lie.SplitAlgebraSolderingForm
