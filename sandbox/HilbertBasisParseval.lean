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
theorem exists_hilbertBasis_CBO : ∃ (w : Set E) (b : HilbertBasis w ℂ E), ⇑b = Subtype.val :=
  exists_hilbertBasis ℂ E

/-- Hilbert basis reconstruction from coefficients. -/
theorem hilbertBasis_hasSum_repr (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x :=
  b.hasSum_repr x

/-- Hilbert basis element representation from `ℓ²` space. -/
theorem hilbertBasis_hasSum_repr_symm (b : HilbertBasis ι ℂ E) (f : ℓ²(ι, ℂ)) :
    HasSum (fun i => f i • b i) (b.repr.symm f) :=
  b.hasSum_repr_symm f

/-- Parseval identity in bilinear `HasSum` form. -/
theorem hilbertBasis_parseval_hasSum (b : HilbertBasis ι ℂ E) (x y : E) :
    HasSum (fun i => ⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ) ⟪x, y⟫_ℂ :=
  b.hasSum_inner_mul_inner x y

/-- Summability for Parseval identity. -/
theorem hilbertBasis_parseval_summable (b : HilbertBasis ι ℂ E) (x y : E) :
    Summable (fun i => ⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ) :=
  b.summable_inner_mul_inner x y

/-- Parseval identity as a `tsum`. -/
theorem hilbertBasis_parseval_tsum (b : HilbertBasis ι ℂ E) (x y : E) :
    (∑' i, ⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ) = ⟪x, y⟫_ℂ :=
  b.tsum_inner_mul_inner x y

end HilbertBasisParseval
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
