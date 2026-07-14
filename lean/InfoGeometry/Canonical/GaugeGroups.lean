import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Gauge Group Definitions: SU(N), PSU(N)

Core algebraic contracts for gauge groups consumed by `YangMillsFiniteBridge`.
- `SUN`: Special Unitary Group (unitary + det = 1)
- `SUNCenter`: n-th roots of unity (center of SU(N))
- `PSUN`: Projective Special Unitary Group (quotient by center)

Dead declarations (`SU2N`, `block_embedding_*`) removed — sorry-equivalent
with zero external consumers. See `reports/dag/sorry-equivalence.md`.
-/

namespace GaugeGroups

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

end GaugeGroups
