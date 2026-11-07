# Finite group harmonics, Walsh geometry, and an open-chain countermodel

## Intake and ground-truth contract

This continuation compiles the Bulgarian user intake on cyclic Fourier bases,
Sylvester–Walsh characters, binary PMI logarithms, group convolution, and
Kac–Murdock–Szegő (KMS) open chains. It follows the source paper
[Karkada et al., arXiv:2602.15029](https://arxiv.org/abs/2602.15029), but the
paper's model assumptions and empirical observations are not Lean hypotheses
unless explicitly present in a theorem type. The intake's rhetoric, proposed
physical interpretations, and universal claims are retained in the claim
ledger below rather than silently promoted to theorems.

The starting revision is
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`. The separate cyclic character,
centering, inverse-DFT, and Gram-matrix work is in
[PR #296](https://github.com/nickgou-nuke/info-geometry-lean/pull/296).
This change starts from main and does not require that unmerged branch.
The frozen UTF-8 intake transcription has SHA-256
`5146e18981e412783c351e5dc7f452f751528fb8db587b4d69f3a248b9d8e556`.

### Exact carriers and conventions

1. A finite group `G`, a commutative coefficient semiring `R`, and a possibly
   noncommutative `R`-algebra `A`. A representation is the native monoid
   homomorphism `G →* A`; the concrete matrix specialization uses
   `Matrix n n ℂ`. The existing convolution convention is
   `(f * g)(x) = ∑ y, f(y) g(y⁻¹ * x)`. All sums use counting measure.
2. The native additive group `ι → ZMod 2` for a finite decidable coordinate
   type `ι`. Its sign functions are native additive characters. The Walsh
   matrix and weighted coordinate-sign kernel are actual real matrices with
   all Boolean group elements as row and column indices.
3. Real numbers `s,z`, with `|s| < 1` and `z² = 1`, for the exact two-point
   logarithm identity. Positivity of `1 ± s` is proved from the hypothesis;
   the logarithm is the native `Real.log`.
4. Actual rational `3 × 3` matrices for the KMS countermodel at `q = 1/2`,
   its two-sided inverse, and the standard Dirichlet discrete Laplacian.
   This is an explicit finite counterexample, not a general spectral theorem.

### Existing owners and the missing implications

| Existing owner | Readout and reuse | New implication required |
|---|---|---|
| `InfoGeometry.Algebra.NoncommutativePlaneWaveKernel` | `finiteConvolution`, `finitePlaneWaveTransform`, coefficient readout, and `finitePlaneWaveTransform_mul_convolution`; native `MonoidAlgebra` carrier | Push the group-algebra transform through an actual representation, expose the matrix-valued finite sum, and preserve the order for both conventions |
| Mathlib `MonoidAlgebra.lift` and opposite algebras | Native algebra homomorphism extending a monoid representation | Inverse-argument coefficients must land in the opposite algebra before `unop` reverses multiplication |
| Mathlib additive characters, finite sums, and matrices | Character laws, finite character orthogonality, matrix multiplication | Explicit Boolean character family, full Walsh matrix orthogonality, and coordinate-kernel diagonalization |
| `Omega.Core.WalshFourier` | Genuine integer-valued Fourier theory on `Word n = Fin n → Bool`, indexed by coordinate subsets; orthogonality and inversion already exist | The new native `ZMod 2` group and real-matrix bridge does not replace or duplicate the integer inversion owner |
| `InfoGeometry.Canonical.V4GroupFourierTransform` | Fixed four-character group calculation | Does not provide the arbitrary finite-coordinate real Walsh matrix |
| Mathlib `Real.log_mul` and `Real.log_div` | Exact logarithm rules with their nonzero/positivity hypotheses | The two-point affine expansion under `z² = 1` and `|s| < 1` |
| Mathlib finite matrices and rational arithmetic | Native full matrix multiplication | Explicit KMS inverse and a nonzero commutator with the Dirichlet matrix |
| `InfoGeometry.Analysis.OperatorDirichletLaplacian` | Genuine Hilbert-space sum of adjoint compositions | Does not identify a finite KMS precision matrix with the fixed Dirichlet second-difference matrix |

Owner discovery searched repository definitions, consumers, and alternate
formulations before selecting these surfaces. The existing plane-wave owner
is imported by the root aggregates; its algebra API is reused rather than
redefined. The scalar `Omega.POM.VisibleWalshGramTransfer` carrier does not
supply the required full matrix theorem and is not used as evidence for it.
The reused plane-wave owner also receives its required source header and
minimal linter cleanup: unused theorem section instances are omitted and two
unused simplifier arguments are removed. Its operations and convolution law
are unchanged; that touched owner is included in the complete native audit.

### Promoted theorem surface

| Module | Substantive public results |
|---|---|
| `InfoGeometry.Algebra.FiniteGroupFourier` | `finiteRepresentationTransform_apply`, `finiteRepresentationTransform_convolution`, `inverseFiniteRepresentationTransform_convolution`, native matrix specializations, `representation_trace_conjugate`, `right_translation_invariant_iff`, `groupDifferenceMatrix_convolution`, `groupDifferenceMatrix_mulVec_right_translate` |
| `InfoGeometry.LLM.WalshCharacterGeometry` | `walshCharacter_orthogonality`, `walshMatrix_mul_transpose`, `walshMatrix_isHadamard`, `attributeSpectrum_single`, `attributeSpectrum_eq_zero_of_not_singleton`, `attributeKernel_mul_walshMatrix`, `walshMatrix_transpose_mul_attributeKernel_mul`, `log_one_add_mul_of_sq_eq_one`, `binaryLogKernel_eq_constant_add_attributeKernel` |
| `InfoGeometry.LLM.KMSBoundaryCounterexample` | `kmsThree_apply`, `kmsThree_mul_inverse`, `inverse_mul_kmsThree`, `inverse_endpoint_ne_interior`, `kmsThree_dirichlet_commutator_entry`, `kmsThree_mul_dirichlet_ne`, `inverse_ne_affine_dirichlet` |

The three new owners contain 42 explicit theorems and 13 definitions. The
existing owner cleanup adds no declarations. Native generated helpers are
counted separately by the independent owner audit.
All three new modules are also imported by `InfoGeometry.lean` and
`InfoGeometry.AllExhaustive`; the latter supplies `InfoGeometry.All`.
These two aggregate changes add only imports. Their complete package build
remains subject to the separately reported root integration failure.

## Atomic claim ledger

| Intake claim | Exact disposition and boundary |
|---|---|
| A translation-invariant finite group kernel is a difference kernel | `[kernel_verified]`: `K(i,j) = κ(i*j⁻¹)` iff simultaneous right translation preserves its entries; full matrix kernel multiplication realizes convolution |
| Group Fourier turns convolution into multiplication | `[kernel_verified]`: forward coefficients `∑ f(g) • ρ(g)` preserve order; inverse-argument coefficients `∑ f(g) • ρ(g⁻¹)` reverse order for the stated convolution |
| Nonabelian characters are matrices | Correction: representations are matrix-valued; their characters are scalar traces. Matrix coefficients and characters must not be conflated |
| The displayed finite inversion formula has no normalization | Correction: counting-sum forward coefficients require a factor `1 / |G|` in irreducible Fourier inversion. A full irreducible inversion/completeness theorem is outside this change |
| Pontryagin duality and Peter–Weyl follow from the same finite sum | Open analytic scope: locally compact topology, continuity, unitary characters, Haar measure, and compact-group completion are not constructed here |
| Boolean characters form an orthogonal basis | `[kernel_verified]`: actual Walsh matrix `W` satisfies `W * Wᵀ = |G| I`, with native coordinate-kernel spectral consequences |
| `(ZMod 2)^d` is a partially ordered group | Correction: the Boolean coordinate order is not a translation-invariant group order. The formal carrier is an additive group, without that extra assertion |
| Squaring a binary feature to one collapses the logarithm | `[kernel_verified]`: exact two-point affine interpolation and full binary-log matrix decomposition; coefficients remain real logarithmic expressions |
| Independent binary features force every learned embedding to be a hypercube | Conditional/model claim: an explicit coordinate-feature kernel has Walsh eigenmodes. Training dynamics, factorization choices, and universal learned geometry are not supplied by that theorem |
| A KMS inverse is the standard Dirichlet Laplacian | `[countermodel_found]`: the inverse has distinct endpoint and interior diagonal entries, the KMS matrix does not commute with the standard Dirichlet matrix, and its inverse is not any rational affine rescaling of that matrix |
| The fixed Dirichlet sine basis diagonalizes every KMS chain | Rejected as stated by the boundary counterexample; the Lean theorem establishes matrix noncommutation, not a general analytic eigenfunction classification |
| Toeplitz structure automatically provides `sl₂` or a continuous translation generator | Open debt: no such Lie representation is constructed from this finite matrix alone |
| Fourier coordinates are the only possible learned coordinates | Correction: basis changes within eigenspaces and factorization freedom remain; no uniqueness theorem is asserted |
| Removing direct co-occurrences necessarily preserves all geometry | Conditional/empirical claim from a specified statistical model; no missing-data robustness theorem follows solely from convolution |
| Cyclic statistics produce exact circles, higher harmonics, and two-hop Gram structure | Prior finite operator scope is recorded in PR #296; model/optimizer and empirical claims remain separate |
| A joint seasonal/binary model is automatically a Kronecker sum with identities | Correction: the additive PMI model in Appendix D uses all-ones matrices in the cross factors. Separate cyclic and Walsh results do not yet prove the full joint eigensystem |

## Dependency order

The proof dependencies, rather than linguistic analogies, determine the order:

1. Existing finite convolution and group-algebra transform, then native
   representation extension, then the forward multiplication law.
2. Group inversion into the opposite algebra, then the same multiplication
   law, then inverse-convention order reversal.
3. Group cancellation and finite reindexing, then difference-kernel
   reconstruction and its matrix product law.
4. Explicit Boolean additive characters, then character separation and
   orthogonality, then full Walsh matrix identities and coordinate-kernel
   diagonalization.
5. Binary square-one dichotomy and positivity, then real logarithm identities,
   then the exact affine formula and decomposition of the full binary log
   kernel into its constant and coordinate-character parts.
6. Explicit KMS entries, then exact matrix products, then two-sided inversion
   and the noncommutation counterexample.

These branches have no claimed causal edge to empirical language-model
training, Lie-algebra classification, categorical colimits, or analytic
completion.

## Sources

The user paper is provenance, not a formal axiom. For the KMS boundary issue,
see [Fikioris, arXiv:1804.08140](https://arxiv.org/abs/1804.08140),
Theorem 2.1(i), equation (2.1). For a finite-group forward Fourier convention,
representation characters, and the counting-measure inversion factor, see
[Ganev, notes on the Lusztig Fourier transform](https://ivganev.github.io/notes/files/Lusztig-Fourier.pdf),
Appendix Definition 4.1 and Lemma 4.2. The Lean proofs establish the exact
finite statements independently of these references.

In the paper's [version 3](https://arxiv.org/html/2602.15029v3), Appendix D,
equations (44)–(45), gives the binary logarithm coefficients. Appendix B.2
records the general linear change-of-factorization freedom. Appendix E.4
uses a continuum limit and Robin endpoint conditions, equations (78)–(80);
it does not establish a universal fixed finite Dirichlet sine basis.

## Verification and acceptance

**Disposition: `[accepted_limited_scope]` for the exact finite statements.**
Independent semantic review and separate acceptance QA both passed. The
complete selected closure was copied into a new source tree and rebuilt:
the four touched modules plus the unchanged `FiniteSpinAlgebra` dependency.
No earlier project `.olean` was reused. All five modules passed with
`-DwarningAsError=true` and zero warnings.

The runtime is Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Root toolchain/dependency files,
the untouched dependency owner, Mathlib, and all eight pinned Mathlib
dependencies were checked for source and revision integrity.

| Audited owner | Explicit declarations | Generated declarations | Native total |
|---|---:|---:|---:|
| `NoncommutativePlaneWaveKernel` | 18 | 5 | 23 |
| `FiniteGroupFourier` | 21 | 6 | 27 |
| `WalshCharacterGeometry` | 24 | 14 | 38 |
| `KMSBoundaryCounterexample` | 10 | 3 | 13 |
| **Total** | **73** | **28** | **101** |

The native audit enumerated declarations by their actual owning module and
inspected transitive dependencies of checked types and values. The exact
aggregate axiom footprint is `{propext, Classical.choice, Quot.sound}`.
There are no custom axioms, unsafe or partial owned declarations, forbidden
proof markers, hard placeholder findings, or constructivity-gate findings.
Five soft short-proof heuristics were reviewed individually: they concern
concrete cancellation, character symmetry, and computed spectrum support,
and do not assume their conclusions.

The maintained `tools/quality/check_operator_geometry.py` ran with the four
explicit module targets, a fresh work directory, the pinned Mathlib checkout,
and a Lean wrapper enforcing warnings as errors. The independent native
owner audit covers these four owners rather than the checker's fixed legacy
owner list. Frozen source hashes were checked again after verification.

The separate root integration command was also executed:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail \
  InfoGeometry.Algebra.NoncommutativePlaneWaveKernel \
  InfoGeometry.Algebra.FiniteGroupFourier \
  InfoGeometry.LLM.WalshCharacterGeometry \
  InfoGeometry.LLM.KMSBoundaryCounterexample
```

It exited **1** during package resolution because the configured local
`external_refs/homotopy-hypothesis-lean4` package is absent. The isolated
five-module result does not repair that missing dependency or certify the
root project. No dependency pin or package configuration was changed to
obtain the isolated result. Actual commit/pre-push hook outcomes are recorded
in the PR after their execution; this change is for draft review while the
root integration failure remains unresolved.
