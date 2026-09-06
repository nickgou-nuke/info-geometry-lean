import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# AFP CBO Hilbert-basis and Parseval adapters

This file exposes Mathlib's Hilbert basis existence, reconstruction, and
Parseval identities in the repository CBO namespace.
-/

noncomputable section

open scoped InnerProductSpace
open scoped BigOperators

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace HilbertBasisParseval

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Hilbert-space orthonormal basis existence, rooted in Mathlib's Zorn argument. -/