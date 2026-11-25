# Real direct-limit pairings, radical reduction, and derivations

## Provenance and base

This is the algebraic continuation of PR #432, **Formalize finite Euler,
Weil–Krein and Stokes cores**. Its remote base is
`c40e82ff31a4d5eb17aac53c63f3facbe0cd1ded`, with tree
`82567210b8c8cc74372da8bb5bb0213b2bc28e61`. The independently prepared local base
has the same tree. This change targets that PR's branch because its radical
quotient and finite arithmetic owners are not yet on `main`.

The supplied `Pasted text(20261123-132550).txt` is preserved in
`docs/intake/real-colimit-20261123/colimit-proposal.txt`, with its SHA-256 digest
beside it. The proposal supplies targets and interpretations, not evidence of
Lean acceptance. The implementation keeps Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Owner search and construction order

The source search covered the existing categorical/direct-limit owners, real
Fock pairing and completion, representative-based modular derivation,
finite Euler identities, reflection lemmas, and positive radical quotient.
The pinned Mathlib direct-limit, bilinear-map, quotient, derivation, and unit-map
APIs were inspected. This was a bounded owner search, not an exhaustive
repository certification.

`Categorical.FilteredDirectLimitOwner` already owns categorical universal
properties. The new concrete calculations use Mathlib's root `DirectLimit`
and its existing module/algebra maps. No alternate colimit carrier or assumed
universal-property record is added. `ModularColimitDerivation` is reused by
proving its interface fields on the actual native carrier.

The dependency order is:

1. A nonempty directed preorder, modules or commutative algebras, and native
   `DirectedSystem` coherence.
2. Compatible stage forms, endomorphisms, or derivations.
3. Constructed maps on the native direct limit and representative formulas.
4. Radical reduction, using symmetry for the quotient pairing and an explicit
   adjoint relation for the quotient operator.
5. A comparison with stage radical quotients when radical stability is available.

All forms and endomorphisms here are real. The derivation construction is
generic over a commutative scalar ring and therefore specializes to real
algebras. No finite-dimensionality or injective-transition assumption is added.

## Exact declaration contracts

| Owner | Implemented statement and hypotheses |
|---|---|
| `LinearAlgebra/DirectLimitBilinear` | Exact stage form preservation constructs `form` through native `DirectLimit.lift₂` and `LinearMap.mk₂`. Same-stage/common-stage formulas and `form_unique` identify it. Symmetric stages give a symmetric limit. Limit nonnegativity is equivalent to stage nonnegativity. A negative stage self-pairing gives a nonzero negative image. |
| `LinearAlgebra/DirectLimitEndomorphism` | Compatible linear maps construct `descendEnd` using native `DirectLimit.Module.lift`. Involution, square-zero, commutation, eigen-equations, and the actual operator identity `J ∘ D ∘ J = -D` transport by representatives. |
| `LinearAlgebra/DirectLimitReflection` | Applies the existing arithmetic reflection theorems to the constructed limit maps. The native `HasEigenvector` result explicitly requires the original stage image to be nonzero. |
| `LinearAlgebra/DirectLimitPairingOperators` | Stage adjoint pairs descend to a native `LinearMap.IsAdjointPair`. That relation proves preservation of the left radical. `Submodule.mapQ` constructs the quotient endomorphism with exact representative readback. |
| `LinearAlgebra/DirectLimitRadicalQuotient` | Reuses `PositiveRadicalQuotient` for positivity equivalence and survival of negative classes. Characterizes persistent radical membership. Under explicit radical stability, constructs quotient transition maps, proves their injectivity, and constructs the canonical `LinearEquiv` from the colimit of quotients to the quotient of the colimit. |
| `Arithmetic/FiniteEulerLogDerivative` | Adds naturality of unit logarithmic derivatives, including the negative convention, under a native algebra homomorphism intertwining the two native derivations. |
| `Modular/NativeDirectLimitDerivation` | Supplies the existing derivation interface from actual native algebra maps and representative/equality theorems; bundles the result as `Derivation`. Proves stage readback, uniqueness, unit naturality, and the exact one-factor finite-power Euler identity with its remainder. |
| `Clifford/RealFockInfinityPairing` | Identifies the existing two-lift Fock pairing with the generic constructed form on exactly the same carrier. The existing pairing, metric instances, and completion construction are reused. |

### Positivity and negative witnesses

For exactly compatible real forms,

\[
B_\infty(\iota_i x,\iota_i y)=B_i(x,y),\qquad
B_\infty\ge0\iff\forall i,\ B_i\ge0.
\]

For symmetric forms, the same equivalence holds after quotienting by
`LinearMap.ker B∞`. If `Bᵢ(x,x) < 0`, both the limit image and its radical
quotient class are nonzero and have that same negative self-pairing. Original
transition-map injectivity is unnecessary.

### Persistent radicals and the canonical comparison

Without assuming radical stability, the implemented characterization is

\[
\iota_i x\in\ker B_\infty
\iff
\forall j\ge i,\ f_{ij}x\in\ker B_j.
\]

Exact form preservation alone does not preserve stage radicals. The explicit
counterexample includes the zero-form line by `t ↦ (t,0)` into the real
hyperbolic plane with pairing `ad + bc`. The image of `1` pairs to `1` with the
new second-coordinate vector.

If every transition preserves the stage radicals, the native quotient maps
form a directed system and are injective. The constructed equivalence is

\[
\varinjlim_i(V_i/\ker B_i)
\simeq_{\mathbb R}
(\varinjlim_iV_i)/\ker B_\infty,
\qquad [[x]_i]\longmapsto[\iota_i x].
\]

This is a canonical **linear equivalence**, with its representative formula;
there is no separately bundled isometry between quotient-limit pairings.
Symmetric positive semidefinite target forms imply radical stability, using
the existing theorem that zero self-pairing is equivalent to radical
membership under those hypotheses. This equivalence is not used for an
indefinite form.

### Operators and Euler identities

The reflection relation alone does not supply radical preservation. The
operator quotient instead consumes an adjoint relation
`B(Tx,y)=B(x,Sy)`. The proof tests a radical vector against `S y` and then uses
native quotient functoriality.

The existing modular derivation interface's `surj_dense` field is instantiated
as exact algebraic representative existence. It is not interpreted as
topological density. Its eventual-equality field is proved from the native
quotient relation, not assumed as stage-map injectivity.

For a unit Euler factor with `E⁻¹=1-a` and `δa=-ell*a`, the transported identity
retains `ell*E*a^(M+1)`. The power cutoff `M` is finite. The theorem treats one
factor; existing finite-product theorems remain available in the arbitrary
commutative-algebra owner. Distinct finite Euler products are not identified
as a compatible single element.

## Explicit remaining obligations

- The real Fock pairing identification reuses an existing concrete positive
  system. It is not an identification of an arithmetic Weil form with that system.
- A new extended negative index in `ℕ∞`, including its colimit equality, is not
  implemented. Mathlib's finite-valued `QuadraticForm.sigNeg` is not used to
  infer positivity of an infinite-dimensional carrier.
- The proposed polynomial Euler-factor quotient algebras, their ideal-stable
  derivations, and generator-renaming transition maps are not constructed here.
  The native limit derivation accepts arbitrary actual compatible algebras.
- The proposed finitely supported hyperbolic block system is not identified
  with a particular arithmetic spectral model.
- The square-zero theorem is for a single endomorphism. It is not a constructed
  degree-indexed chain complex or a new theorem about homology and colimits.
- Completion of the general radical quotient, bounded extension of its
  operators, closability of unbounded operators, and spectral consequences
  remain separate obligations. The existing Fock completion is a regression target.
- Infinite products, limiting Weil forms, trace/heat-kernel limits, infinite
  curvature sums, and critical-strip analytic continuation require additional
  compatibility or analytic estimates. No GRH conclusion is asserted.

## Verification and review status

The implementation is a draft pending compiler acceptance. The bounded
verification entry point is `verification/real-colimit/check.py`; its source,
kernel, and axiom-log stages have separate statuses. It uses the existing
pinned focused package and the maintained shared-lock wrapper. The eight
owners, the existing Fock completion, and the finite arithmetic audit define
its scope. It does not certify the root package or the whole repository.

Independent source audit and acceptance review results, concrete command
results, and any blocked compiler status are recorded in the handover before
publication. Adding the focused CI workflow is not evidence that it has passed.
