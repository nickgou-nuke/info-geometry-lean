import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# Pinned external Lean proof source for Erdős Problem 1196

This module records the local proof authority for the primitive-set-above-`x`
theorem without pretending that the external proof has already been ported into
the `InfoGeometry.Arithmetic` namespace.

The external proof has been cloned locally under:

`external/Erdos1196`

at commit:

`02fba13be7487cc51315f68d8fa7ef277633d3c8`

Its theorem authority is:

* `PrimitiveSetsAboveX.mainTheorem`
* `Erdos1196.erdos_1196`

The upstream repository was pinned to Lean `v4.30.0-rc1`. The local checkout
has been retargeted to this repository's Lean `v4.28.0` and source-compatibility
patched so that the explicit Lake target

`lake build PrimitiveSetsAboveX`

builds against this repository's cached mathlib.
-/

namespace InfoGeometry.Arithmetic

/-- Metadata for a pinned external Lean proof source. -/
structure ExternalLeanProofPin where
  /-- Repository URL. -/
  repository : String
  /-- Exact commit used locally. -/
  commit : String
  /-- Local checkout path. -/
  localPath : String
  /-- Upstream Lean toolchain recorded by the proof repository. -/
  upstreamToolchain : String
  /-- Local Lean toolchain used by this vendored checkout. -/
  localToolchain : String
  /-- Main external theorem declaration. -/
  mainTheorem : String
  /-- Formal-conjectures bridge theorem declaration. -/
  formalConjecturesTheorem : String
  deriving Repr

/--
Pinned external proof source for the primitive-sets-above theorem.

This is metadata only; it is not a mathematical axiom and does not assert the
external theorem inside this namespace.
-/
def erdos1196ProofPin : ExternalLeanProofPin where
  repository := "https://github.com/math-inc/Erdos1196"
  commit := "02fba13be7487cc51315f68d8fa7ef277633d3c8"
  localPath := "external/Erdos1196"
  upstreamToolchain := "leanprover/lean4:v4.30.0-rc1"
  localToolchain := "leanprover/lean4:v4.28.0"
  mainTheorem := "PrimitiveSetsAboveX.mainTheorem"
  formalConjecturesTheorem := "Erdos1196.erdos_1196"

end InfoGeometry.Arithmetic
