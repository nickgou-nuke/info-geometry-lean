# Zorn primal–dual geometry: theorem contract

Status: source implementation and compiler repair in progress. A theorem
script is not compiler evidence. The focused verification workflow records
the exact owner coverage and axiom audit separately from source review.

## Provenance and target

This extends draft PR #445. The second submitted Lean draft is preserved
verbatim in `verification/zorn-cl44-triality/intake-primal-dual-20261124.txt`.
The accompanying mathematical narrative supplies proposed interpretations;
the statements below give their corrected finite real algebraic content.
The Lean and Mathlib pins remain unchanged.

The target carrier is the existing `Canonical.ZornMatrix ℝ`. No tuple-only
duplicate octonion type is introduced. Its norm is `ab - dot x y`, its
associated symmetric form is `zornBilin`, and its full Clifford action is
the existing action on `DiracSpinor16 = ZornMatrix ℝ × ZornMatrix ℝ`.

The dependency order is:

1. The canonical product, norm, linear coordinate equivalence and multiplication
   operators fix the convention.
2. An explicit Witt splitting identifies the norm with primal–dual evaluation.
3. Native Clifford polarization gives the null-generator CAR on the doubled
   spinor space.
4. The normalized Clifford commutator gives the three infinitesimal triality
   actions and their covariance identity.
5. The existing trace-zero matrix derivation construction identifies the
   mixed-plane boost and supplies its Leibniz law.
6. Nondegeneracy, conjugate contraction and its polarization give exact
   null-multiplication kernels and their dimensions.

## Three distinct decompositions

| Construction | Carrier and dimensions | Restriction of the norm or grading |
| --- | --- | --- |
| Witt splitting | `ZornMatrix ℝ ≃ W ⊕ W*`, dimensions `4+4` | Both summands are totally isotropic. |
| Quaternion decomposition in the submitted basis | `H ⊕ ell H`, dimensions `4+4` | The first summand is positive definite and the second negative definite. Neither is a null summand. |
| Dirac chirality | `DiracSpinor16 = S+ ⊕ S-`, dimensions `8+8` | Gamma exchanges these summands; bivectors preserve them. |

Using split quaternions instead of the displayed definite quaternion basis
would give nondegenerate `(2,2)` summands, still not the Witt null summands.
The real direct sum `W ⊕ W*` does not require complexification or an operation
of forgetting complex scalars. A Lorentz form on `W` is additional structure;
the evaluation norm itself exists for every real four-dimensional `W`.

## Explicit Witt coordinates and CAR normalization

Reuse `ZornPolarizationMetricBridge.nullFourSplit` on the native coordinate
carrier. With `W = ℝ × (Fin 3 → ℝ)`, the splitting is

`(a,b,x,y) ↦ (q,p) = ((a,x),(b,-y))`.

The coordinate pairing `p(q) = p₀q₀ + Σ pᵢqᵢ` is then precisely

`N(a,b,x,y) = ab - dot x y = p(q)`.

The public `Fin 4` coordinates apply the same spatial reflection to both
halves, giving `q=[a,-x₀,-x₁,-x₂]` and `p=[b,y₀,y₁,y₂]`. This preserves
evaluation and makes the primal inclusion agree exactly with the first
intake's signed convention. The native standard-basis duality bundles the
second factor as `Module.Dual ℝ Four` and gives a quadratic isometry to
the repository's `canonicalNeutralFormUnscaled`.

The inclusions of `(q,0)` and `(0,p)` are complementary four-dimensional
linear subspaces. Their restrictions of the norm vanish. The two mixed
terms in the associated form are

`B((q,p),(r,s)) = (s(q) + p(r))/2`.

Consequently, for the native doubled action,

* `{gamma(q,0), gamma(r,0)} = 0`;
* `{gamma(0,p), gamma(0,s)} = 0`;
* `{gamma(q,0), gamma(0,p)} = p(q) I₁₆`.

In dual bases the mixed coefficient is `δ`, not `2δ`, for the specified
quadratic form `Q(q,p)=p(q)`. The factor two is valid only with a consistently
rescaled quadratic form or generators. `NeutralDualPairClifford` already
owns this unscaled normalization abstractly; the extension specializes the
existing Zorn gamma law instead of redefining the Clifford algebra.

`ZornSignedConvention.primal` and `dual` from the first intake use raw signed
spatial coordinates. Their norm formula is the Minkowski cross pairing.
The present positive evaluation coordinates absorb the spatial minus sign
into the covector. These are different coordinate labels on the same norm.

## Full Clifford algebra and dimension obstruction

The full algebra is `Cl(4,4) ≃ M₁₆(ℝ)`, of real dimension 256. Its faithful
action is on the sixteen-dimensional Dirac carrier. `Endℝ(ZornMatrix ℝ)` has
dimension 64. The new `no_eight_dimensional_clifford_action` theorem rules
out a unital algebra homomorphism from the full Clifford algebra into that
endomorphism algebra: simplicity forces injectivity, which contradicts the
dimension inequality.

The even Clifford algebra has two chiral matrix factors. A single
eight-dimensional half-spin representation is an action of the even
algebra, and has a kernel on that full even algebra. It does not extend to
the proposed full eight-dimensional Clifford representation.

## Reciprocity and orthogonal blocks

In the chosen dual coordinates the existing `fundamental` map is the
unsigned exchange `S(q,p)=(p,q)`. It satisfies `S²=I`, preserves `Q`, and
reverses the alternating form

`Ω((q,p),(r,s)) = s(q) - p(r)`.

The existing coordinate owner also proves this particular exchange
multiplicative on Zorn coordinates. It is not an outer triality permutation.
Identifying the dual space with the original space requires the displayed
coordinate duality; the exchange is not a basis-independent operation on
an arbitrary vector space with no such choice.

The signed quarter-turn `J(q,p)=(p,-q)` instead satisfies `J²=-I`, preserves
`Ω`, and reverses `Q`. It must not be called the same involution as `S`.

A general split-orthogonal infinitesimal transformation has blocks

`[[A, beta], [B, -transpose A]]`,

where `B` and `beta` are skew. The existing
`ZornWittEndomorphismBlockBridge.wittSkew_iff` owns this block condition.
Only the block diagonal subalgebra preserves the selected primal and dual
summands separately. Chirality preservation by even Clifford operators is
a statement about the different `8+8` spinor splitting.

## Mixed-plane derivation and its support

For the signed quaternion and split axes `e_i` and `f_i=ell*e_i`, set

`B₁₂ = Tᵥ(e₁,f₂) - Tᵥ(f₁,e₂)`.

Its canonical action is

`(a,b,x,y) ↦ (0,0,(-x₁,-x₀,0),(y₁,y₀,0))`.

The existing `CanonicalZornPeirceSL3Bridge` constructs precisely this
derivation from the trace-zero spatial matrix

`[[0,-1,0],[-1,0,0],[0,0,0]]`.

Its upper action is `Mx`, and its lower action is `-Mᵀy`. The extension
identifies that constructed derivation with the vector bivector difference
and with both chiral spinor differences. Thus its Leibniz law is inherited
from an actual native derivation, rather than supplied as a new hypothesis.
It sends `e₁` to `-f₂`, `e₂` to `-f₁`, `f₁` to `-e₂`, and `f₂` to `-e₁`.
It kills `1`, `ell`, `e₃`, and `f₃`, so its square is not the full identity.

Let `P` project onto the first two spatial coordinates in each vector slot.
The exact operator identities are `B₁₂²=P` and `D₁₂²=-P`, where `D₁₂` is
the rotation from the first intake. Both operators preserve Dirac chirality.

## General derivation invariance

`SplitOctonionDerivationWittOrthogonalBridge.derivation_native_witt_skew`
already proves skewness for every native canonical derivation. Its proof
uses the complete fourteen-parameter classification. The new
`ZornCl44DerivationInvariant` owner identifies that native trace pairing
with `2 * zornBilin` and gives an injective native Lie algebra homomorphism
from `canonicalZornDerivations` into `skewAdjointLieSubalgebra zornBilin`.

It also bundles the full composition tensor as three nested linear maps,
`C(x,y,z)=B(x*y,z)`, and derives

`C(Dx,y,z) + C(x,Dy,z) + C(x,y,Dz) = 0`

for every canonical derivation `D`. There is no invariant-form assumption
in this statement: general skewness comes from the existing theorem and
Leibniz from native derivation membership. The result is an infinitesimal
invariance statement for the actual octonionic multiplication tensor.
On the full eight-dimensional carrier this tensor is not asserted to be
an alternating three-form. No gauge field is constructed from it.

The reused skew theorem has a wider dependency closure (approximately
eighty repository modules) than the coordinate bridges. Verification must
compile that actual closure; a check of the two concrete derivations alone
does not certify this general result.

## Null incidence and the necessary nonzero hypothesis

The full target is, for each `z ≠ 0` with `N(z)=0`,

`finrank ℝ (ker L_z) = finrank ℝ (ker R_z) = 4`,

with these kernels totally isotropic for `zornBilin`. The nonzero condition
is essential: multiplication by zero has the entire eight-dimensional
carrier as its kernel.

The bounded reuse search found a rank-four theorem for the full operator
of a trace-zero null element in `SplitOctonionAnnihilatorDimension` and a
factorization theorem on the chart `z.a ≠ 0` in
`CanonicalZornNullFactorization`. Neither theorem alone covers the stated
arbitrary nonzero null carrier. The new owner must supply that missing
implication, rather than silently retain a chart or imaginary restriction.

For left multiplication, conjugate contraction and its polarization give
`ker L_z = range L_conj(z)`. Adjointness with respect to the nondegenerate
form gives `(range L_conj(z))⊥ = ker L_z`. Therefore the kernel equals its
own orthogonal complement, and the native dimension theorem gives four.
This also proves maximal total isotropy. Conjugation transports right
kernels to conjugate left kernels, giving dimension four and isotropy.
On the doubled spinor carrier, Clifford polarization instead gives
`ker gamma(z) = range gamma(z)`, of dimension eight. The kernel of `L_z`
lives in a spinor copy of the octonions in the
triality interpretation; it is not a reason to identify all three copies.

## Interpretation boundaries

The finite algebraic construction does not by itself supply a smooth
principal bundle, connection, curvature, field equation or particle model.
An orthogonal bivector is a possible infinitesimal structure-algebra value;
a gauge potential requires a differential one-form, and curvature requires
its derivative and bracket. Likewise a chiral grading operator is not by
itself a construction of every exterior grade or a Hodge-star theorem.

Outer `S₃` triality acts on the vector and two half-spin representations.
It does not identify a four-dimensional primal space, its four-dimensional
dual, and a twenty-eight-dimensional flux space. The projective null quadric
in an eight-dimensional split space belongs to the `D₄` triality geometry;
the split Cayley hexagon uses the trace-zero seven-dimensional octonionic
geometry and additional incidence structure.

For a real Lie group `G`, a cotangent trivialization identifies the cotangent
groupoid with a coadjoint action groupoid. With source-coordinate convention
`(g,μ)`, the source is `μ`, the target is `Ad_g* μ`, and composition is
`(h,Ad_g* μ) ∘ (g,μ) = (hg,μ)`, where
`Ad_g* μ = μ ∘ Ad_(g⁻¹)`. Mathlib's action category provides the algebraic
groupoid once an action is supplied; a smooth cotangent identification and
multiplicative canonical symplectic form require separate constructions.
No such theorem is inferred here from the finite Clifford operators.

For `G=Spin(4,4)`, `g*` has dimension 28 and `T*G` dimension 56. The ten
components `(P_μ,M_μν)` describe a different, Poincaré-type Lie algebra
dual. Neither a subgroup construction nor a moment map to that dual is
automatic from the notation in the intake.

## Validation ledger

Focused CI on the initial PR head reached `ZornSignedConvention` and failed
at fifteen elaboration locations, before reaching the other four new owners.
The repair normalizes finite-vector projections and replaces the failed
half-sum proofs with native scalar cancellation. The downstream coordinate
owners receive the same projection normalization. These are actual compiler
diagnostics; the attachment's statement that all equations compile is not
used as evidence.

Every newly selected owner must pass the focused build, fresh elaboration
with warnings treated as errors, and the complete declaration axiom audit.
Source screening and mathematical review are reported separately. The
shared local build remains subject to the repository lock; it is not
bypassed. Repository-wide existing fixture debt and root-package dependency
issues remain outside this focused theorem certificate.

## Background references

* Marco Gualtieri, *Generalized complex geometry*, §§1.1–1.3:
  https://www.math.utoronto.ca/mgualt/gcg/gcg.pdf
  (neutral pairing, orthogonal block form, and the exterior-algebra spinor
  model of dimension `2^dim W`).
* Peter Crooks and Maxence Mayrand, *Symplectic reduction along a submanifold*,
  §4.1:
  https://www.cambridge.org/core/journals/compositio-mathematica/article/symplectic-reduction-along-a-submanifold/9E17032854939CB7FC79521E367894FD
  (cotangent/coadjoint groupoid and its canonical symplectic structure).

These references support mathematical conventions and interpretation. Lean
acceptance is determined by the actual source statements and compiler audit.
