import Mathlib.Tactic
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Galois-action and crossed-product data

The Bost-Connes algebra is the semigroup crossed product C(Ẑ) ⋊ ℕ+, where
C(Ẑ) ≅ C*(ℚ/ℤ) is the algebra of continuous functions on the profinite integers,
equivalently the group C*-algebra of ℚ/ℤ.

## Architecture

1. **Commutative Subalgebra C_comm** ≅ C(Ẑ), represented via the group algebra
   of ℚ (with periodicity e(r+1)=e(r) encoding the quotient ℚ/ℤ).

2. **Semigroup Endomorphisms α_n**: The action of ℕ+ on C_comm by non-invertible
   endomorphisms. α_p averages over the p-th roots: α_p(e(r)) = (1/p) Σ e((r+k)/p).

3. **Galois Action**: Gal(ℚ^{ab}/ℚ) ≅ Ẑ^× acts on C_comm by automorphisms
   permuting the roots of unity: g·e(a/n) = e(χ_n(g)·a/n).

4. **Crossed Product Relation**: S_n A S*_n = α_n(A) for all A ∈ C_comm.

5. **Galois-Semigroup Equivariance**: g∘α_n = α_n∘g, ensuring the Galois group
   acts as global automorphisms of the crossed product.

This module defines explicit structures for a commutative algebra with
rationally indexed generators, semigroup endomorphisms, a supplied group
action, equivariance, and a crossed-product relation. The structures are data
interfaces; they do not construct a profinite C*-algebra or identify a group
with an absolute Galois group.
-/

set_option linter.unusedVariables false

open Complex

universe u

noncomputable section

namespace InfoGeometry.Canonical.BostConnesGalois

open BostConnesKMS
open InfoGeometry.Arithmetic.BostConnesSystem

/-! ### 1. The Commutative Subalgebra (≅ C(Ẑ)) -/

/-- Algebraic structure carried by the commutative coefficient type. -/
structure CommutativeBoundaryAlgebra (C_comm : Type u) where
  [commRing : CommRing C_comm]
  [starRing : StarRing C_comm]
  [algebra : Algebra ℂ C_comm]

attribute [instance] CommutativeBoundaryAlgebra.commRing
attribute [instance] CommutativeBoundaryAlgebra.starRing
attribute [instance] CommutativeBoundaryAlgebra.algebra

/--
Rationally indexed generators with additive, involutive, and period-one laws.
-/
structure GroupElementRepresentation
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm] where
  e : ℚ → C_comm
  e_zero : e 0 = 1
  e_add : ∀ r s : ℚ, e (r + s) = e r * e s
  e_star : ∀ r : ℚ, star (e r) = e (-r)
  e_periodic : ∀ r : ℚ, e (r + 1) = e r

/-! ### 2. Semigroup Endomorphism Action of ℕ+ -/

/--
Endomorphisms indexed by positive natural numbers, with additive,
multiplicative, unit, and semigroup laws.
-/
structure SemigroupEndomorphismAction
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm) where
  α : ℕ+ → C_comm → C_comm
  α_add : ∀ n x y, α n (x + y) = α n x + α n y
  α_mul : ∀ n x y, α n (x * y) = α n x * α n y
  α_one : ∀ n, α n 1 = 1
  α_semigroup : ∀ n m A, α n (α m A) = α (n * m) A
  /--
  α_p(e(r)) is the average over the p-th roots:
    α_p(e(r)) = (1/p) Σ_{k=0}^{p-1} e((r+k)/p).

  We express this as: α_p(e(r)) ∈ span of { e((r+k)/p) | k = 0,...,p-1 }.
  The field below records only the stated span condition.
  -/
  α_on_generator_span : ∀ (p : ℕ+) (r : ℚ),
    α p (e_rep.e r) ∈ Submodule.span ℂ
      {e_rep.e ((r + (k : ℚ)) / (p : ℚ)) | (k : ℕ) (_ : k < (p : ℕ))}

/-! ### 3. The Galois Action -/

/--
Data for a supplied group action on rational indices, including additivity,
periodicity, and a faithfulness condition.
-/
class GaloisActionData (G : Type u) where
  [group : Group G]
  [topologicalSpace : TopologicalSpace G]
  /-- Action on rational indices. -/
  actOnQ : G → ℚ → ℚ
  actOnQ_zero : ∀ g, actOnQ g 0 = 0
  actOnQ_add : ∀ g r s, actOnQ g (r + s) = actOnQ g r + actOnQ g s
  actOnQ_periodic : ∀ g r, actOnQ g (r + 1) = actOnQ g r + 1
  /-- Faithfulness: if g acts as identity on all rationals, then g = 1. -/
  act_faithful : ∀ g, (∀ r, actOnQ g r = r) → g = 1

attribute [instance] GaloisActionData.group
attribute [instance] GaloisActionData.topologicalSpace

/--
Lifted algebra automorphisms carrying each supplied generator according to the
supplied action on rational indices.
-/
structure GaloisAlgebraAutomorphism
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm)
    {G : Type u} [GaloisActionData G] where
  galoisAut : G → C_comm →ₐ[ℂ] C_comm
  galoisAut_on_generator : ∀ (g : G) (r : ℚ),
    galoisAut g (e_rep.e r) = e_rep.e (GaloisActionData.actOnQ g r)
  galoisAut_faithful : ∀ g, (∀ A, galoisAut g A = A) → g = 1

/-! ### 4. Galois-Semigroup Equivariance -/

/--
Data asserting that the supplied algebra automorphisms commute with the
supplied semigroup endomorphisms.
-/
structure GaloisSemigroupEquivariance
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep)
    (G : Type u) [GaloisActionData G]
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) where
  equivariance : ∀ (g : G) (n : ℕ+) (A : C_comm),
    galoisAut.galoisAut g (semigroup.α n A) =
    semigroup.α n (galoisAut.galoisAut g A)

/-! ### 5. The Semigroup Crossed Product -/

/--
An algebraic carrier with an embedding of the coefficient algebra and a
specified conjugation relation for the supplied indexed operators.
-/
structure BostConnesCrossedProduct
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (Op : Type u) [Ring Op] [StarRing Op] [Algebra ℂ Op]
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep)
    (cuntz : CuntzMultiplicativeIndexing Op) where
  /-- Embedding of the coefficient algebra into the operator carrier. -/
  ι : C_comm →ₐ[ℂ] Op
  /--
  The supplied conjugation relation for the indexed operators.
  -/
  crossed_product_relation : ∀ (n : ℕ+) (A : C_comm),
    BostConnesKMS.S cuntz n * ι A *
      star (BostConnesKMS.S cuntz n) = ι (semigroup.α n A)

end InfoGeometry.Canonical.BostConnesGalois
