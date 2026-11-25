# Triality, invariant duals, and cotangent action groupoids

## Intake and mathematical corrections

Source: the user's `TrialitySymplecticGroupoidBridge` Lean proposal supplied
on 2026-11-24, continuing PR #440. The new work starts independently from
`main` at `fe24e350b08fdea04f74c0748ef9fd9417c47529`; it does not depend on
unmerged Legendre modules.

The proposal has two parts: a lift of a group automorphism to arrows
`G × g*`, and four-dimensional real Hadamard/reflection triality matrices.
Its explicit source/target convention is retained:

\[
s(k,\alpha)=\alpha,\qquad t(k,\alpha)=\alpha\circ\operatorname{Ad}(k^{-1}),
\qquad (k,\alpha)(l,\beta)=(kl,\beta)
\]

where the product requires `α = Ad*(l) β`. Its fiber form is retained:

\[
\omega_\alpha((X,\xi),(Y,\eta))
=\eta(X)-\xi(Y)+\alpha([X,Y]).
\]

The submitted theorem only asserted covariance of the operations. It did not
prove the groupoid laws, restrict multiplication to composable pairs, or
construct a native groupoid. Its `hAd_one` and `hAd_mul` assumptions were
unused. An arbitrary `bracket : g → g → g` also supplies neither bilinearity
nor alternation. The new owners use a bundled representation and native Lie
algebra structures for precisely these obligations.

The proposal's prose said that arbitrary fixed arrows define a canonical
**symplectic** subgroupoid `T*G^τ`. That assertion is false without additional
conditions. On the additive group `ℝ²`, the genuine automorphism
`T(x,y)=(x+y,y)` fixes the first coordinate vectors, while its contragredient
fixes the second coordinate covectors. Their pairing vanishes. The native
restricted canonical form on the two-dimensional fixed phase space is zero.

Finite real symmetry gives a constructive repair. For a representation of a
finite group `F`, native Reynolds averaging is a projection

\[
P_F=\frac1{|F|}\sum_{a\in F}\rho(a),\qquad
(V^*)^F\simeq(V^F)^*,\qquad
\varphi\longmapsto\varphi\circ P_F.
\]

Restriction and this explicit extension are proved inverse. No finite
dimension assumption on `V` is required; the dual is algebraic. The real
group-cardinality inverse is constructed, rather than supplied as an
unproved nondegeneracy field. This sufficient condition applies to the native
faithful `S₃` representation constructed below. Infinite actions may also
have nondegenerate fixed restrictions; finiteness is not claimed necessary.

## Existing owners and precise reuse

| Existing owner | Reused content |
|---|---|
| `Canonical/SouriauContragredientPairing.lean` | The actual inverse-dual linear map/equivalence and evaluation pairing |
| `Clifford/NeutralPhaseSpaceCore.lean` | `PhaseSpaceCarrier`, `canonicalNeutralBilin`, `neutralOmega`, and nondegeneracy |
| `Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean` | Existing Hadamard matrix, fourth-coordinate reflection, cycle relations, fixed submodule/equivalence and rank |
| Mathlib `CategoryTheory.Action` | Actual `ActionCategory`, morphisms and native `Groupoid` |
| Mathlib `LinearAlgebra.FixedSubmodule` | Fixed covector submodules |
| Mathlib `RepresentationTheory.Invariants` | Native invariants, dual representation, Reynolds average and its projection laws |
| Mathlib `GroupTheory.SpecificGroups.Dihedral` | Native six-element group, assembled into an explicit equivalence with `Equiv.Perm (Fin 3)` |

The elementary Cartan block is extracted verbatim into `Lie/CartanTriality.lean`
under its original namespace and declaration names. Its original consumer
imports that owner. The removed and extracted declaration blocks are exactly
equal; their SHA-256 is
`4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`.
The changed consumer receives a separate regression build.

Bounded discovery searched repo-owned `lean/`, `src/`, and `tools/` Lean
sources for cotangent/action-groupoid declarations, and inspected the owners
above, the deeper D₄/G₂ construction and its consumers. Search results and
docstrings were used for navigation, not as compilation evidence.

## Exact theorem contracts

### 1. CotangentActionGroupoid

Carrier: a group `G`, a `CommSemiring R` module `V`, and
`Ad : G →* (V ≃ₗ[R] V)`. The construction is the action groupoid of the
contragredient representation on `Module.Dual R V`.

The owner proves coadjoint action laws, source/target/inverse/unit/associativity
laws on composable arrows, compatibility with native morphisms, and
equivariance under `(τ,dτ)` satisfying the actual intertwining law.
The lifted functor is full, faithful and essentially surjective, giving a
native category equivalence. The fixed subgroup acts on the native fixed
dual submodule. Its inclusion is object-injective and faithful; its morphism
image consists precisely of the arrows with fixed group label. It is not
claimed to be a full subcategory.

The input representation is not assumed to be the differential adjoint of a
Lie group by its name. That identification remains a separate obligation.

### 2. CotangentLieForm

Carrier: a real Lie algebra `V` and its full algebraic dual. The bracket
correction is a native bilinear form added to the existing `neutralOmega`.
Alternation, skewness and nondegeneracy are proved. A linear equivalence
intertwining the bracket preserves this form when paired with its
contragredient; a native `LieEquiv` supplies that hypothesis.

### 3. FiniteCotangentInvariants

Carrier: an arbitrary real representation of a finite group. The owner
constructs `(V*)^F ≃ₗ[ℝ] (V^F)*` by restriction and explicit Reynolds extension.
The actual inclusion of fixed primal/dual pairs pulls the ambient form back
to the canonical form on the invariant space. The restriction is alternating
and nondegenerate. The bracket-corrected ambient form also has nondegenerate,
alternating restriction to these fixed factors; that assertion does not
silently claim that they are a Lie subalgebra.

### 4. CotangentFixedShear

Carrier: the full real plane and its full algebraic dual. The owner constructs
the shear and its fixed submodules, proves both fixed factors are isomorphic
to `ℝ`, proves the fixed phase dimension is two, and proves the entire
restricted canonical form is zero. A concrete nonzero radical vector proves
nondegeneracy fails. Natural restriction of fixed covectors is also zero.

### 5. CartanTriality and CartanTrialityRepresentation

The supplied matrices are exactly the existing Hadamard matrix `H` and the
new first-coordinate reflection `S=diag(-1,1,1,1)`. The explicit orthogonal
involution `P(v)=(-v₃,v₁,v₂,-v₀)` conjugates the existing reflection to `S`
and leaves `H` unchanged. This is a coordinate-action equivalence.

The owners prove the exact orders, Coxeter relations, noncommutativity,
standard Euclidean orthogonality, a native basis/equivalence/rank for
`v₀=0, v₁+v₂+v₃=0`, the three distinct unit orbit vectors, and a faithful
native `S₃` representation. The fixed submodule is proved equal to the
all-elements invariant space of that representation.

The proposal's theorem statement omitted the claimed nonidentity, exact
dimension, basis and norm assertions; these are now explicit theorems.

### 6. CartanTrialityCotangent

The representation acts by genuine automorphisms of the additive vector
group `ℝ⁴`, written as `Multiplicative (Fin 4 → ℝ)`. Its trivial adjoint
model instantiates the general groupoid lift. The actual simultaneously
fixed arrow/phase coordinates are identified with invariant primal and dual
factors. Their native restricted form is alternating and nondegenerate and
their dimension is exactly four, canonically the cotangent space of the
two-dimensional fixed Cartan coordinate plane.

This instantiation is explicitly the abelian vector-group model. The
noncommuting `S₃` operators still act on the full four-dimensional vector
space; they are not replaced by scalar or diagonal proxies.

## Boundaries and provenance

The new owners do not construct a smooth cotangent bundle, a closed
differential form, or multiplicativity of that form on a Lie groupoid.
They also do not identify the coordinate action with the differential of an
outer automorphism of real `Spin(4,4)`, prove a Killing-form normalization,
or construct a smooth `G₂(2)` fixed subgroup. Those require explicit maps,
smoothness and compatibility theorems.

The existing deep owner has a concrete split boost Cartan. The intake's named
octonion rotation planes do not become that Cartan merely through a
four-by-four coordinate conjugacy. Consequently the new matrix form theorem
is accurately named standard Euclidean orthogonality.

For the convention and additional smooth-groupoid obligations, see
Alekseev–Meinrenken, *On the coadjoint Virasoro action*,
[Appendix A.2, Example A.5 and equation (78)](https://arxiv.org/pdf/2211.06216).
For cotangent lifts and the fixed-locus statement under involution hypotheses,
see Meinrenken, *Symplectic Geometry* (Fall 2024),
[§§3.4, 8.4 and Example 4.16](https://www.math.toronto.edu/mein/teaching/LectureNotes/symplectic.pdf).
These references guide the theorem contract; they do not substitute for
Lean verification.

## Validation

The reproducible package and exact observed results are recorded in
[`verification/triality-cotangent/README.md`](../verification/triality-cotangent/README.md)
and [`VALIDATION.md`](../verification/triality-cotangent/VALIDATION.md).
Source review, a text screen, a kernel build, an axiom audit, and the
regression build have distinct status. No whole-repository certificate is
inferred from the focused package.
