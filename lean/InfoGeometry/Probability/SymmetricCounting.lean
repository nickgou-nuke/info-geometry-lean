import Mathlib.Data.Finset.Card
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Basic

/-!
# Finite symmetric counting atoms

This file states the counting invariance facts directly using mathlib's
canonical `Finset.card`, `Finset.map`, `Finset.map_inter`, Cartesian product
`×ˢ`, and equivalences.  No local counting-measure or symmetry-action wrapper is
introduced.

The results are finite cardinality statements only: no analytic measure,
probability normalization, concentration limit, or quotient construction is
asserted.
-/

set_option autoImplicit false

namespace SymmetricCounting

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
/-- Finite cardinality is invariant under mapping by an equivalence. -/
theorem unnormalized_measure_invariant (e : Equiv α α) (A : Finset α) :
    (A.map e.toEmbedding).card = A.card := by
  exact Finset.card_map (Equiv.toEmbedding e)

/-- Intersection counts are invariant under an equivalence that fixes the target subset. -/
theorem projection_invariant (e : Equiv α α) (A B : Finset α)
    (hB : B.map e.toEmbedding = B) :
    ((A.map e.toEmbedding) ∩ B).card = (A ∩ B).card := by
  calc
    ((A.map e.toEmbedding) ∩ B).card
        = ((A.map e.toEmbedding) ∩ (B.map e.toEmbedding)).card := by
            rw [hB]
    _ = ((A ∩ B).map e.toEmbedding).card := by
            rw [Finset.map_inter (f := Equiv.toEmbedding e) A B]
    _ = (A ∩ B).card := Finset.card_map (Equiv.toEmbedding e)

omit [DecidableEq α] [DecidableEq β] in
/-- Cartesian-product state counts are invariant under product equivalences. -/
theorem product_measure_invariant (e1 : Equiv α α) (e2 : Equiv β β)
    (A : Finset α) (B : Finset β) :
    ((A ×ˢ B).map (Equiv.prodCongr e1 e2).toEmbedding).card = (A ×ˢ B).card := by
  exact Finset.card_map (Equiv.toEmbedding (Equiv.prodCongr e1 e2))

end SymmetricCounting
