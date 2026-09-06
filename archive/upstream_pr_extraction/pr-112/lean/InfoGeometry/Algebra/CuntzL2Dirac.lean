import Mathlib
import InfoGeometry.Algebra.GenericDirac
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.HilbertBasisParseval

/-!
# Cuntz ℓ² Dirac convergence socket

This module closes the honest analytic gap around the prime-indexed expression

`D = ∑ p, a p • (S p + S p*)`.

The finite self-adjointness theorem in `GenericDirac` is purely algebraic.  The
infinite theorem has to pass through an actual summability/convergence datum.
Here we isolate that datum as a `HasSum` certificate for the weighted creation
part and then prove the Dirac limit is self-adjoint.

The theorem intentionally does not identify the index type with primes or prove
`∑ p, p^(-2β) < ∞`; that prime-zeta estimate belongs in the number-theoretic
analytic layer.  Once that layer supplies the `HasSum` certificate for
`T p = p^(-β) • S p`, the theorem below gives the norm/topological Dirac limit
and its self-adjointness.
-/

noncomputable section

open scoped BigOperators
open scoped InnerProductSpace

namespace InfoGeometry.Algebra.Cuntz

/-! ## 1. Finite weighted Dirac terms -/

/--
A weighted creation family written in the algebraically safe form
`T i + T i*`.

For real positive Boltzmann weights one instantiates `T i = a i • S i`.  This
avoids baking scalar-star simplification into the basic convergence theorem.
-/
abbrev diracTerm {A ι : Type*} [Add A] [Star A] (T : ι → A) (i : ι) : A :=
  T i + star (T i)

/-- Every weighted Dirac term `T i + T i*` is self-adjoint. -/
lemma diracTerm_selfAdjoint {A ι : Type*} [AddCommMonoid A] [StarAddMonoid A]
    (T : ι → A) (i : ι) :
    IsSelfAdjoint (diracTerm T i) := by
  change IsSelfAdjoint (T i + star (T i))
  exact selfAdjoint_add_star (T i)

/--
Finite weighted Dirac sums are self-adjoint.  No Cuntz relations are used.
-/
lemma finiteWeightedDirac_selfAdjoint {A ι : Type*} [AddCommMonoid A]
    [StarAddMonoid A] [Fintype ι] (T : ι → A) :
    IsSelfAdjoint (∑ i, diracTerm T i) := by
  change IsSelfAdjoint (∑ i, (T i + star (T i)))
  exact finiteDirac_selfAdjoint T

/-! ## 2. Infinite creation certificates -/

/--
A certificate that the weighted creation part has a topological sum and that
star transports that sum to the corresponding annihilation part.

In a normed star algebra with continuous star, the second field should usually
be derived from the first.  It is kept explicit here so the theorem is usable
against the repository's current star-algebra sockets without forcing a heavier
C⋆-algebra API.
-/
structure L2CreationCertificate (A ι : Type*) [TopologicalSpace A]
    [AddCommMonoid A] [StarAddMonoid A] where
  /-- The weighted creation terms, e.g. `p ↦ p^(-β) • S p`. -/
  T : ι → A
  /-- The norm/topological limit of the weighted creation part. -/
  creationLimit : A
  /-- Summability/convergence of the weighted creation series. -/
  hasSum_creation : HasSum T creationLimit
  /-- Summability/convergence of the formal adjoint/annihilation series. -/
  hasSum_annihilation : HasSum (fun i => star (T i)) (star creationLimit)

namespace L2CreationCertificate

variable {A ι : Type*}
variable [TopologicalSpace A] [AddCommMonoid A] [ContinuousAdd A]
variable [StarAddMonoid A]

/-- The bounded/topological Dirac limit attached to a creation certificate. -/
def diracLimit (C : L2CreationCertificate A ι) : A :=
  C.creationLimit + star C.creationLimit

/-- The infinite Dirac series associated to a creation certificate. -/
def diracSeries (C : L2CreationCertificate A ι) : ι → A :=
  fun i => diracTerm C.T i

/--
The certified infinite Dirac series converges to `creationLimit + creationLimit*`.
-/
theorem hasSum_dirac (C : L2CreationCertificate A ι) :
    HasSum C.diracSeries C.diracLimit := by
  exact C.hasSum_creation.add C.hasSum_annihilation

/--
The certified infinite Dirac limit is self-adjoint.

This is the closure step needed by the prime-indexed Cuntz/O∞ Dirac package:
once the analytic layer supplies an ℓ²/norm-convergence certificate for the
creation part, self-adjointness follows formally.
-/
theorem diracLimit_selfAdjoint (C : L2CreationCertificate A ι) :
    IsSelfAdjoint C.diracLimit := by
  change IsSelfAdjoint (C.creationLimit + star C.creationLimit)
  exact selfAdjoint_add_star C.creationLimit

/-- Readback theorem bundling convergence and self-adjointness of the limit. -/
theorem hasSum_dirac_and_selfAdjoint (C : L2CreationCertificate A ι) :
    HasSum C.diracSeries C.diracLimit ∧ IsSelfAdjoint C.diracLimit :=
  ⟨C.hasSum_dirac, C.diracLimit_selfAdjoint⟩

end L2CreationCertificate

/-! ## 3. Hilbert-basis ℓ² convergence readout -/

namespace HilbertL2Creation

variable {ι E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/--
The canonical ℓ² creation limit against a Hilbert basis.

This is the concrete analytic model behind the abstract certificate: an ℓ²
coefficient vector determines a norm-convergent Hilbert-basis expansion.
-/
def creationLimit (b : HilbertBasis ι ℂ E) (f : ℓ²(ι, ℂ)) : E :=
  b.repr.symm f

/--
Hilbert-basis ℓ² expansion as a `HasSum` theorem.

This is the reusable analytic limit theorem: square-summable coefficients give
norm convergence of the creation expansion.
-/
theorem hasSum_creation (b : HilbertBasis ι ℂ E) (f : ℓ²(ι, ℂ)) :
    HasSum (fun i => f i • b i) (creationLimit b f) := by
  simpa [creationLimit] using
    InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.HilbertBasisParseval.hilbertBasis_hasSum_repr_symm
      b f

/-- The corresponding Hilbert-basis creation expansion is summable. -/
theorem summable_creation (b : HilbertBasis ι ℂ E) (f : ℓ²(ι, ℂ)) :
    Summable (fun i => f i • b i) :=
  (hasSum_creation b f).summable

end HilbertL2Creation

end InfoGeometry.Algebra.Cuntz
