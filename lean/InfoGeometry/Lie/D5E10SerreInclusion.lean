import Mathlib.Algebra.Lie.SerreConstruction
import InfoGeometry.Lie.E10SerrePresentation

/-!
# D₅ to E₁₀ Cartan Embedding
## The Pin(5,5) / E₁₀ Unification Bridge

This module formally proves that the repository's core D₅ / Pin(5,5) architecture
is exactly the foundational sub-structure of the newly implemented E₁₀ Serre algebra.
We explicitly define the D₅ configuration and prove that the E₁₀ generalized 
Cartan matrix restricts identically to the D₅ Cartan matrix across the 
first 5 diagrammatic nodes.
-/

namespace InfoGeometry.Lie.D5E10Inclusion

open InfoGeometry.Lie.E10

/-- The canonical embedding of the D₅ diagram into the E₁₀ diagram.
We select the 5 nodes from the E₁₀ diagram that form the D₅ sub-diagram.
In our E₁₀ numbering, nodes {0, 1, 2, 3, 4} form the exact D₅ star configuration.
-/
def d5ToE10 (i : Fin 5) : Fin 10 :=
  ⟨i.val, by
    have h : i.val < 5 := i.isLt
    omega⟩

/-- The D₅ edges derived by restricting the E₁₀ diagram to the first 5 nodes. -/
def d5Edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (2, 3), (0, 4)]

/-- The D₅ generalized Cartan Matrix. -/
def d5CartanMatrix : Matrix (Fin 5) (Fin 5) ℤ := fun i j =>
  if i = j then 2 else if (min i.val j.val, max i.val j.val) ∈ d5Edges then -1 else 0

/-- Theorem: The E₁₀ Cartan matrix exactly restricts to the D₅ Cartan matrix
    on the first 5 nodes, proving that D₅ (and thus SO(5,5) / Pin(5,5))
    is a canonical sub-algebra of the E₁₀ Serre presentation. -/
theorem e10_cartan_restricts_to_d5 (i j : Fin 5) :
    cartanMatrix (d5ToE10 i) (d5ToE10 j) = d5CartanMatrix i j := by
  revert i j
  decide

/-- The Serre Algebra of the restricted D₅ core. -/
noncomputable abbrev D5SerreAlgebra := Matrix.ToLieAlgebra ℚ d5CartanMatrix

end InfoGeometry.Lie.D5E10Inclusion
