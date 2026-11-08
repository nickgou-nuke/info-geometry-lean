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
has been retargeted to this repository's Lean `v4.34.1` and source-compatibility
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
def localToolchain : String := "leanprover/lean4:v4.34.1"

/-- Main theorem declaration in the external source. -/
def mainTheorem : String := "PrimitiveSetsAboveX.mainTheorem"

/-- Formal-conjectures bridge theorem declaration in the external source. -/
def formalConjecturesTheorem : String := "Erdos1196.erdos_1196"

end erdos1196ProofPin

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
  repository := erdos1196ProofPin.repository
  commit := erdos1196ProofPin.commit
  localPath := erdos1196ProofPin.localPath
  upstreamToolchain := erdos1196ProofPin.upstreamToolchain
  localToolchain := erdos1196ProofPin.localToolchain
  mainTheorem := erdos1196ProofPin.mainTheorem
  formalConjecturesTheorem := erdos1196ProofPin.formalConjecturesTheorem

end InfoGeometry.Arithmetic
