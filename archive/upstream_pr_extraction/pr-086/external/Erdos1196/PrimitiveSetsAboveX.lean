import InfoGeometry.Arithmetic.Erdos1196ProofPin

/-!
# Compatibility root for `PrimitiveSetsAboveX`

The tracked root `lean/PrimitiveSetsAboveX.lean` is a symlink to this file.  The
full external Erdős 1196 proof is recorded by
`InfoGeometry.Arithmetic.Erdos1196ProofPin`; this compatibility module gives
legacy Lake and blueprint scanners a concrete source file to index without
asserting the external theorem as a local axiom.
-/

namespace PrimitiveSetsAboveX

/-- Metadata-only pointer to the pinned external Erdős 1196 proof source. -/
def proofPin : InfoGeometry.Arithmetic.ExternalLeanProofPin :=
  InfoGeometry.Arithmetic.erdos1196ProofPin

end PrimitiveSetsAboveX
