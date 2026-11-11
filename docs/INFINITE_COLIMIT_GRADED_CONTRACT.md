# Graded operators on the infinite Clifford colimit

## Provenance and carrier

The [raw intake](INFINITE_COLIMIT_GRADED_INTAKE.md) was supplied on 2026-11-11.
Its 17,337-byte payload is preserved exactly, with SHA-256
`0f232707387d8dd1ce8b8f8f70696e276d072168c71dbeed9e00d59937153af4`.
The source baseline is `c143c264bc18bbf41d692be4e270b5b7f7405702`.

The carrier is the existing real algebra
`InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit`, denoted below by \(B\).
Its matrix stages are \(A_n=M_{2^n}(\mathbb R)\), embedded by the existing tensor
tower maps. The existing `Cl11ColimitDimension.not_finiteDimensional` proves
\(\neg\operatorname{FiniteDimensional}_{\mathbb R} B\). The parameters
\(n:\mathbb N\) and \(k:\operatorname{Fin}n\) select a charge; every operator
in this addition acts on **all** \(X\in B\).

The two new owner files are:

- [Cl11ChiralityAlgebra.lean](../lean/InfoGeometry/Clifford/Cl11ChiralityAlgebra.lean)
- [Cl11GradedDifferential.lean](../lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean)

They introduce no replacement colimit or global chirality element. The existing
descended ring action is the function being bundled as an algebra equivalence.

## Exact construction and dependency order

Let \(\theta\) be `Cl11TensorTowerLimit.limitChiralityConj`. Its existing
involutivity and multiplicativity are reused. The first new theorem proves

\[
\theta(\operatorname{algebraMap}_{\mathbb R,B}(r))
=\operatorname{algebraMap}_{\mathbb R,B}(r).
\]

The proof uses the actual scalar representation at stage zero and
\(\Gamma_0=1\). This supplies `limitChiralityAlgEquiv : B ≃ₐ[ℝ] B`, whose
forward and inverse functions are both the existing \(\theta\).

For the actual embedded Jordan--Wigner operators, put

\[
u=\operatorname{ofStage}_n(\operatorname{jwCreation}(n,k)),\qquad
v=\operatorname{ofStage}_n(\operatorname{jwAnnihilation}(n,k)).
\]

The existing all-stage CAR and chirality theorems give

\[
u^2=v^2=0,\qquad uv+vu=1,\qquad
\theta(u)=-u,\qquad\theta(v)=-v.
\]

Define native real linear endomorphisms of \(B\) by

\[
d(X)=uX-\theta(X)u,\qquad h(X)=vX.
\]

`jwDifferential` is the existing generic `IntrinsicGradedAdjoint.gradedAdjoint`
specialized to this actual algebra equivalence and charge. `jwHomotopy` is
Mathlib's `LinearMap.mulLeft`. Products in `Module.End ℝ B` mean composition,
so \((dh)(X)=d(h(X))\).

| New declaration | Statement or role | Established input |
| --- | --- | --- |
| `limitChiralityConj_algebraMap` | The descended action fixes real scalars | Stage-zero scalar representation |
| `limitChiralityAlgEquiv` | The same action as `B ≃ₐ[ℝ] B` | Scalar preservation and existing involutivity |
| `limitChiralityAlgEquiv_apply` | Definitional readback of that action | Native construction |
| `gradedAdjoint_ofStage` | \(d_{\operatorname{ofStage}_n Q}(\operatorname{ofStage}_n X)=\operatorname{ofStage}_n(QX-(\Gamma_nX\Gamma_n)Q)\) | Ring-map laws and chirality readback |
| `jwDifferential` | \(d=L_u-R_u\theta\) on the entire \(B\) | Generic graded-adjoint owner |
| `jwDifferential_sq` | \(d^2=0\) | Odd charge, involution, generic square theorem, \(u^2=0\) |
| `jwDifferential_annihilation` | \(d(v)=1\) | \(\theta(v)=-v\) and \(uv+vu=1\) |
| `jwDifferential_ne_zero` | \(d\ne0\) | \(d(v)=1\) and the actual nontrivial limit |
| `jwHomotopy` | \(h=L_v\) on the entire \(B\) | Native linear left multiplication |
| `jwHomotopy_sq` | \(h^2=0\) | \(v^2=0\) and associativity |
| `jwDifferential_homotopy` | \(dh+hd=I\) | Graded Leibniz, \(d(v)=1\), and oddness of \(v\) |
| `jwDifferential_range_eq_ker` | \(\operatorname{range}d=\ker d\) | Nilpotency and the explicit primitive \(h(X)\) |

The contraction is obtained in the stated multiplication order:

\[
d(vX)=d(v)X+\theta(v)d(X)=X-vd(X).
\]

Thus \(d(h(X))+h(d(X))=X\). Nilpotency gives
\(\operatorname{range}d\subseteq\ker d\); if \(d(X)=0\), this identity gives
\(X=d(h(X))\), proving the reverse inclusion. The final theorem derives
exactness from these maps; exactness is not an assumption or a structure field.

## Reused source and bounded search

The implementation consumes these existing owners without modifying them:

| Owner | Relevant existing content |
| --- | --- |
| `Clifford.Cl11TensorTowerLimit` | Actual direct-limit algebra, real scalar embedding, stage maps, transported identities |
| `Clifford.Cl11ChiralityTransport` | Descended ring action, involutivity, stage readback, oddness of the JW generators |
| `Canonical.Cl55WittCAR` | `creation_sq`, `annihilation_sq`, and `same_site_car`, for every stage \(n\) |
| `OperatorAlgebra.IntrinsicGradedAdjoint` | Native graded endomorphism, graded Leibniz, and the square identity |
| `Clifford.Cl11ColimitDimension` | Stage dimension \(4^n\), infinite dimension of this limit, and nonsurjectivity of every stage |

The search covered these owners, alternate scalar/parity formulations, imports,
consumers in `lean`, related `src`/`proofs` files, and the pinned Mathlib APIs.
No existing scalar-compatible `AlgEquiv` for this particular action or this
actual JW contraction was located in that bounded search. Other head-tail and
doubled-matrix parity constructions have different carriers.

The existing `Canonical.Cl11TensorTowerInfiniteCAR` already defines countable
modes. This addition does not duplicate them. Its wider import branch reaches
an unresolved `Architect` import at the reviewed baseline. The present proof
uses the existing all-stage JW elements directly and leaves that unrelated
import boundary untouched. The selected closure has 23 repository modules and
29 direct Mathlib import roots, without an umbrella `Mathlib` import.

## Claim ledger and analytic boundary

The following distinctions are part of the contract. A source result listed as
existing is not automatically covered by the new selected-owner native audit.

| Intake theme | What the inspected source establishes | What remains separate |
| --- | --- | --- |
| Infinite tower | `Cl11ColimitDimension` proves infinite dimension of the actual real limit; `Cl11StarAlgebraFiltration` gives strictness and exhaustion | Analytic completion and a chosen Hilbert representation |
| Global chirality | Coherent conjugation actions descend even though the displayed stage chirality elements are not a coherent element sequence | An internal implementer in a larger algebra or representation |
| Ordered graded action | For an odd charge, the generic square is \(d_Q^2=L_{Q^2}-R_{Q^2}\) | Oddness alone does not give nilpotency; the new theorem uses \(u^2=0\) |
| Cofinal tail | `Cl11MatrixTowerTailShift` gives an equivalence for a cofinal tail of the index diagram | An intersection of physical tensor tails or a quotient by a tail ideal |
| GNS transport | `FilteredGNSCofinalTail` assumes compatible states on complex C*-algebra stages | Constructing that data and connecting it to this real algebraic limit |
| Bounded contraction | `BoundedHomotopyCoercivity` proves a Hilbert-space estimate from its bounded-operator hypotheses | A bounded extension of the new maps, a positive norm bound, and the intended vacuum projection |
| Colimit coercivity | `LieJordanHodgeColimit` transfers a common coercivity bound under its compatibility hypotheses | Deriving a stage-independent bound or the required intertwining |

The new contraction has **zero projection**: \(dh+hd=I\). It contains no
Hilbert adjoint, operator norm, state, physical vacuum, or Hamiltonian. In the
existing analytic estimate, if \(dh+hd=I-P\), \(\|h\|\le C\), \(C>0\), and
\(Px=0\), then the Hodge quadratic form is bounded below by
\(\|x\|^2/(2C^2)\). The hypotheses, carrier, and meaning of \(P\) must be
supplied; an arbitrary bounded map \(P\) is not thereby an orthogonal or
one-dimensional vacuum projection.

The intake's referenced
[PublicTheory.lean at commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean)
exposes spectral-representation, positive-energy, unique-vacuum, and invariance
requirements as fields of its Wightman-theory structures. This addition neither
constructs an instance of those structures nor identifies a physical energy
generator. The [Jaffe--Witten problem statement, section 4](https://www.arthurjaffe.com/Assets/pdf/QuantumYangMillsWebRevised.pdf)
uses a spectral gap of the physical Hamiltonian above the vacuum. An arbitrary
algebraic contraction or a positive operator estimate is not that identification.
No Yang--Mills mass-gap result is asserted here.

## Validation contract

The unchanged pins are Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Source authorship, independent mathematical review, and final evidence review
are separate roles. Static acceptance is not native elaboration evidence.

The dedicated [workflow](../.github/workflows/infinite-colimit-graded.yml)
uses the unchanged configurable `tools/quality/check_peirce_coupling.py` with
these explicit audit targets:

1. `InfoGeometry.Clifford.Cl11ChiralityAlgebra`
2. `InfoGeometry.Clifford.Cl11GradedDifferential`
3. `InfoGeometry.Clifford.Cl11ColimitDimension`
4. `InfoGeometry.Clifford.Cl11ChiralityTransport`
5. `InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint`

It compiles their complete repository import closure into a fresh isolated
output, under the shared build lock. It does not use incremental repository
artifact reuse or skip the declaration audit. All declarations owned by the
five targets, including generated declarations, are audited natively; the only
permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Both new owners must have zero warnings. Existing dependency warnings are
recorded separately and are not described as new-owner warnings.

The workflow binds the exact checked revision and tree, event head/base,
targets, import graph, raw intake, source contract, workflow, checker helpers,
pins, and source bytes. It reconciles live files and copied sources against
the checked Git blobs and verifies generated artifact hashes. The uploaded
artifact includes source copies, owner binaries, logs, source selection,
environment, native report, generated audit source, and checksum manifests.
Normal pinned dependency caching is allowed; this is not a claim of a hermetic
rebuild of Mathlib. For pull requests the checked revision is GitHub's test
merge, recorded distinctly from the PR head.

Native pass/fail results, run identifiers, independent artifact review, and
unrelated repository-wide failures belong in the PR's current validation
record. This contract defines what must be checked; it does not predeclare a
successful run or a clean exhaustive repository build.
