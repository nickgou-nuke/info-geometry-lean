import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/- Metadata constants for a pinned external proof source. -/
namespace erdos1196ProofPin

/-- Repository URL of the pinned external proof source. -/
def repository : String := "https://github.com/math-inc/Erdos1196"

/-- Exact commit used by the local external checkout. -/
def commit : String := "02fba13be7487cc51315f68d8fa7ef277633d3c8"

/-- Local checkout path of the external proof source. -/
def localPath : String := "external/Erdos1196"

/-- Upstream Lean toolchain recorded by the proof repository. -/
def upstreamToolchain : String := "leanprover/lean4:v4.30.0-rc1"

/-- Local Lean toolchain used by the vendored checkout. -/
def localToolchain : String := "leanprover/lean4:v4.28.0"

/-- Main theorem declaration in the external source. -/
def mainTheorem : String := "PrimitiveSetsAboveX.mainTheorem"

/-- Formal-conjectures bridge theorem declaration in the external source. -/
def formalConjecturesTheorem : String := "Erdos1196.erdos_1196"

end erdos1196ProofPin

end InfoGeometry.Arithmetic
