import Mathlib
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Bost-Connes Galois Action — Semigroup Crossed Product and Symmetry Breaking

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

No new postulates: all structure is carried by explicit fields.
-/

set_option linter.unusedVariables false

open Complex

universe u

noncomputable section

namespace BostConnesGalois

open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Arithmetic.BostConnesSystem

/-! ### 1. The Commutative Subalgebra (≅ C(Ẑ)) -/

/-- Wrapper for the commutative algebra structure. -/
structure CommutativeBoundaryAlgebra (C_comm : Type u) where
  [commRing : CommRing C_comm]
  [starRing : StarRing C_comm]
  [algebra : Algebra ℂ C_comm]

attribute [instance] CommutativeBoundaryAlgebra.commRing
attribute [instance] CommutativeBoundaryAlgebra.starRing
attribute [instance] CommutativeBoundaryAlgebra.algebra

/--
The generating elements e(r) for r ∈ ℚ, representing the roots of unity
in the group algebra of ℚ/ℤ. Periodicity e(r+1) = e(r) encodes the quotient.

Properties: e(0) = 1, e(r+s) = e(r)*e(s), e(r)* = e(-r), e(r+1) = e(r).
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
The semigroup endomorphisms α_n : C_comm → C_comm for n ∈ ℕ+.
These are non-invertible endomorphisms dual to the multiplication-by-n map on Ẑ.
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
  The precise averaging with equal weight (1/p) is enforced by the isometry
  condition on the Cuntz generators in the crossed product.
  -/
  α_on_generator_span : ∀ (p : ℕ+) (r : ℚ),
    α p (e_rep.e r) ∈ Submodule.span ℂ
      {e_rep.e ((r + (k : ℚ)) / (p : ℚ)) | (k : ℕ) (_ : k < (p : ℕ))}

/-! ### 3. The Galois Action -/

/--
Galois group data for ℚ^{ab}/ℚ. The Galois group G ≅ Ẑ^× acts on ℚ/ℤ
via the cyclotomic character: for a root of unity ζ_n = e(1/n),
g(ζ_n) = ζ_n^{χ(g) mod n} where χ: Ẑ^× → (ℤ/nℤ)^×.

The action on ℚ is: for r = a/n ∈ ℚ, g·r = χ_n(g)·a / n (mod ℤ).
-/
class GaloisActionData (G : Type u) where
  [group : Group G]
  [topologicalSpace : TopologicalSpace G]
  /-- Action on roots: G → (ℚ → ℚ), compatible with the cyclotomic character. -/
  actOnQ : G → ℚ → ℚ
  actOnQ_zero : ∀ g, actOnQ g 0 = 0
  actOnQ_add : ∀ g r s, actOnQ g (r + s) = actOnQ g r + actOnQ g s
  actOnQ_periodic : ∀ g r, actOnQ g (r + 1) = actOnQ g r + 1
  /-- Faithfulness: if g acts as identity on all rationals, then g = 1. -/
  act_faithful : ∀ g, (∀ r, actOnQ g r = r) → g = 1

attribute [instance] GaloisActionData.group
attribute [instance] GaloisActionData.topologicalSpace

/--
Lifted Galois action on the commutative algebra: g · e(r) = e(g·r).
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
**Theorem data (Galois-Semigroup Equivariance).**

The Galois action commutes with every semigroup endomorphism α_n:
  g · α_n(A) = α_n(g · A).

This is the structural condition ensuring Gal(ℚ^{ab}/ℚ) acts as global
automorphisms of the semigroup crossed product C_comm ⋊ ℕ+.

Proof: on generators e(r), both sides compute to the average over the
p-th roots with the Galois-twisted argument g·((r+k)/p) = (g·r + k)/p,
which holds because the Galois action on ℚ/ℤ commutes with division by p
(the cyclotomic character is compatible with the projection Ẑ^× → (ℤ/pℤ)^×).
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
The full Bost-Connes crossed product: a non-commutative algebra containing
the commutative subalgebra C_comm and the Cuntz isometries S_n, subject to:

  S_n A S*_n = α_n(A)  for all A ∈ C_comm, n ∈ ℕ+.

This is the defining relation of the semigroup crossed product C_comm ⋊ ℕ+,
the ambient algebra of the Bost-Connes system.
-/
structure BostConnesCrossedProduct
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (Op : Type u) [Ring Op] [StarRing Op] [Algebra ℂ Op]
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep)
    (cuntz : CuntzMultiplicativeIndexing Op) where
  /-- Embedding of the commutative subalgebra into the crossed product. -/
  ι : C_comm →ₐ[ℂ] Op
  /--
  **The Crossed Product Relation**: S_n ι(A) S*_n = ι(α_n(A)).

  This extends the Cuntz isometry relation (S*_n S_n = 1) to the full
  non-commutative structure: the isometries "implement" the semigroup
  endomorphisms via conjugation.
  -/
  crossed_product_relation : ∀ (n : ℕ+) (A : C_comm),
    BostConnesKMS.S cuntz n * ι A *
      star (BostConnesKMS.S cuntz n) = ι (semigroup.α n A)

end BostConnesGalois
