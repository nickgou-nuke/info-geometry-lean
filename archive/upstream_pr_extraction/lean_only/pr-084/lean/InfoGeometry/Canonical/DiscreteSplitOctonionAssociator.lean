import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms

namespace InfoGeometry.Canonical

/-!
# The split-octonion associator readout

The discrete octonionic-analysis source uses associator expressions to keep
track of non-associativity.  This owner exposes that expression for the native
rational split-octonion product and records its invariance under the already
verified colour automorphisms.  No associativity is imposed or inferred.
-/

def splitOctonionAssociatorQ
    (x y z : StandardRationalSplitOctonion) :
    StandardRationalSplitOctonion :=
  splitOctonionMulQ (splitOctonionMulQ x y) z -
    splitOctonionMulQ x (splitOctonionMulQ y z)

theorem colorCycle_preserves_splitOctonionAssociatorQ
    (x y z : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionAssociatorQ x y z) =
      splitOctonionAssociatorQ
        (trialityColorCycle x) (trialityColorCycle y)
        (trialityColorCycle z) := by
  simp only [splitOctonionAssociatorQ, map_sub, colorCycle_map_mul]

theorem colorReflection_preserves_splitOctonionAssociatorQ
    (x y z : StandardRationalSplitOctonion) :
    colorReflection (splitOctonionAssociatorQ x y z) =
      splitOctonionAssociatorQ
        (colorReflection x) (colorReflection y)
        (colorReflection z) := by
  simp only [splitOctonionAssociatorQ, map_sub, colorReflection_map_mul]

end InfoGeometry.Canonical
