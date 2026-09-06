import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block

/-!
# Gauge Group Hierarchy and Induction

This module formalizes the algebraic relationships between primary gauge groups
used in the Information Geometry of Yang-Mills fields:
- `SU(N)`: Special Unitary Group
- `PSU(N)`: Projective Special Unitary Group (Quotient by Center)
- `SU(2, N)`: Indefinite Unitary Group (Noncompact real form)

We establish the formal induction contracts and block embedding relations.
-/

namespace InfoGeometry.Canonical.GaugeGroups

open scoped Matrix

variable {n : ℕ}

/--
The Special Unitary Group SU(N) contract.
In the canonical layer, we model this as a structure that satisfies the
unitary and unimodular (det=1) obligations.
-/
structure SUN (n : ℕ) where
  carrier : Type*
  [instGroup : Group carrier]
  /-- Mapping to matrix representation in M_n(ℂ). -/
  toMatrix : carrier → Matrix (Fin n) (Fin n) ℂ
  is_unitary : ∀ g : carrier, (toMatrix g)ᴴ * (toMatrix g) = (1 : Matrix (Fin n) (Fin n) ℂ)
  is_special : ∀ g : carrier, Matrix.det (toMatrix g) = 1

/--
The center of SU(N), isomorphic to the group of n-th roots of unity μ_n.
-/
structure SUNCenter (n : ℕ) where
  elements : Set ℂ
  is_roots_of_unity : ∀ z ∈ elements, z^n = 1
  cardinality : Nat.card elements = n

/--
The Projective Special Unitary Group PSU(N) = SU(N) / μ_n.
Formalized as a quotient contract where the fiber is the center.
-/
structure PSUN (n : ℕ) (G : SUN n) where
  carrier : Type*
  [instGroup : Group carrier]
  projection : G.carrier → carrier
  center : SUNCenter n
  is_quotient : ∀ g₁ g₂ : G.carrier,
    projection g₁ = projection g₂ ↔ ∃ z ∈ center.elements, G.toMatrix g₁ = z • G.toMatrix g₂

/--
Indefinite Unitary Group SU(2, N).
This is a different real form with signature (2, n), noncompact.
It models the phase space symmetry of the "doubled" information manifold.
-/
structure SU2N (n : ℕ) where
  carrier : Type*
  [instGroup : Group carrier]
  toMatrix : carrier → Matrix (Sum (Fin 2) (Fin n)) (Sum (Fin 2) (Fin n)) ℂ
  /-- Signature matrix J = diag(1, 1, -1, ..., -1). -/
  J : Matrix (Sum (Fin 2) (Fin n)) (Sum (Fin 2) (Fin n)) ℂ
  is_J_unitary : ∀ g : carrier, (toMatrix g)ᴴ * J * (toMatrix g) = J
  is_special : ∀ g : carrier, Matrix.det (toMatrix g) = 1

/--
Block Embedding Contract for Group Induction.
Induction SU(N) ⊂ SU(2N) via g ↦ diag(g, I_N).
This embedding tracks the growth of the informational Hilbert space.
-/
def block_embedding_induction (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℂ :=
  Matrix.fromBlocks g 0 0 (1 : Matrix (Fin n) (Fin n) ℂ)

/--
Theorem (Contract): the block embedding preserves the `SU(N)` structure inside
`SU(Sum (Fin n) (Fin n))`.
-/
theorem block_embedding_is_unitary (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᴴ * g = (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (block_embedding_induction n g)ᴴ * (block_embedding_induction n g)
      = (1 : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℂ) := by
  unfold block_embedding_induction
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hg]

end InfoGeometry.Canonical.GaugeGroups
