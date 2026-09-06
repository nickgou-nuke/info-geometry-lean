import Mathlib.Analysis.InnerProductSpace.Orthonormal
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
def orthonormalBasisExists : Nonempty (OrthonormalBasis ι E) := by
  exact exists_orthonormalBasis

/-- Reconstruction of any vector from its orthonormal basis coefficients. -/
theorem reconstruction (b : OrthonormalBasis ι E) (x : E) :
    x = ∑ i : ι, (inner x b i) • b i := by
  rw [b.repr_apply x]
  <;> simp [b.inner_self]
  <;> aesop

/-- Parseval identity: ‖x‖² = ∑ ‹inner x b i›². -/
theorem parseval (b : OrthonormalBasis ι E) (x : E) :
    ‖x‖ ^ 2 = ∑ i : ι, ‖inner x b i‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = ∑ i : ι, ‖inner x b i‖ ^ 2 := by
      rw [b.norm_add_sq_eq_sum_norm_sq_inner]
      <;> simp [b.inner_self]
    _ = ∑ i : ι, ‖inner x b i‖ ^ 2 := by rfl

end HilbertBasisParseval
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators