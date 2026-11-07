# Language symmetry: theorem contract and verification boundary

## Provenance and scope

This work formalizes the algebraic and finite spectral claims in the user intake
of 2026-11-07, motivated by Karkada, Korchinski, Nava, Wyart, and Bahri,
[*Symmetry in language statistics shapes the geometry of model representations*](https://arxiv.org/abs/2602.15029v3),
arXiv:2602.15029v3 (ICML 2026). The checked starting revision is
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.

The intake proposes a noncommutative target/helper decomposition, an exact
binary logarithm identity, a Fourier–Walsh product basis, and a three-site
exponential Toeplitz inverse. Its accompanying claims of a complete paper
formalization and a `propext`-only axiom footprint are not accepted as evidence.
Lean declarations and actual verification determine the delivered scope.

## Contract fixed before implementation

| Claim | Carrier and hypotheses | Intended result | Boundary |
|---|---|---|---|
| Compressed square after block ablation | Arbitrary associative ring, `p*p=p`, `p*m*p=0` | Reuse `InfoGeometry.Core.PeirceCompressionDefect.compression_square_defect` to identify `p*(m*m)*p` with the complementary transfer product | Equality alone does not establish a nonzero product |
| Target/helper equivariance | Rectangular native matrices and two correctly typed intertwining equations | The target round trip commutes with the target action | An arbitrary commuting action does not identify Fourier modes |
| Genuine helper Gramian | Complex finite matrices, Hermitian projection and input | Positive semidefiniteness and nonvanishing precisely when the helper block is nonzero | No corpus training or robustness theorem is asserted |
| Translation kernel spectrum | Finite abelian group, native `Matrix.circulant`, complex additive characters | Character eigenvalues and native character eigenbasis | No unconditional ordering of frequencies |
| Product kernel | Product of finite abelian groups; additive seasonal and attribute kernel | Product-character eigenvalues with character-sum factors; mixed nontrivial modes vanish | The additive kernel uses all-ones tensor factors, not a Kronecker sum with identities |
| Binary logarithm | Real sign `σ²=1`, coupling `-1<s<1` | Actual `Real.log` identity and positive arguments | No arbitrary-ring logarithm or unspecified functional calculus |
| Explicit Walsh support | Native coordinate characters on `Fin d → ZMod 2`, `|s r|<1` | Constant and coordinate eigenvalues; all other attribute modes vanish | No ranking or nonzero coefficient is assumed |
| Exponential Toeplitz inverse | Native `Matrix (Fin 3) (Fin 3) K` | Two-sided scaled product; inverse under a nonzero denominator | Three sites only; not the continuum Proposition 3 |

## Required corrections to the intake

* Algebraic block ablation `p*m*p=0` is distinct from deleting observed pairs.
  For positive marginals, zero PMI corresponds to replacement by independence.
  Literal zero joint probability is outside the positive real logarithm domain.
  Lean's totalized `Real.log 0` must not be used to infer a probabilistic statement.
* A zero direct block does not force a nonzero helper product: the zero operator
  is a counterexample. A nonzero complex coupling does give a nonzero adjoint
  Gramian; this uses more than ring axioms.
* Translation symmetry determines eigenvectors, not their eigenvalue ordering.
  In particular, it does not alone make the first nonconstant harmonic dominant.
* An involution does not supply a logarithm in an arbitrary ring. The scalar
  formulas use `Real.log`; their probabilistic interpretation and the
  positive-factor logarithm formulas require the stated positivity conditions.
  Two-point affine interpolation itself is also valid for the total real log.
* A three-site scaled matrix identity is not an unrestricted inverse, a standard
  graph Laplacian, or a continuum boundary-value theorem.
* The paper's perturbation robustness, training dynamics, linear decoding bounds,
  continuum eigenproblem, and spectral dominance remain outside this PR.

## Reuse and dependency order

The existing compression owner supplies the noncommutative defect. Native
Mathlib supplies rectangular matrices, adjoints, positive semidefiniteness,
circulants, additive characters, and their complex basis. The binary logarithm
and Toeplitz branches are logically independent. They are not assigned a
fabricated total causal order.

The source search inspected the existing Peirce compression owner and its
consumers, `LLM/FourierCharacterEncoding.lean`, `LLM/ZModFourierBridge.lean`,
the finite V4 Fourier owners, the categorical infrastructure map, and the
corresponding pinned Mathlib sources. The new spectral layer uses native
`AddChar` rather than the older custom `FourierCharacter` carrier.

## Implemented interface

Import `InfoGeometry.LLM.LanguageSymmetryRepresentationGeometryPoset`.
The declarations live in `InfoGeometry.LLM.LanguageSymmetry`; the existing
`InfoGeometry.LLM` umbrella imports this synthesis module.

| Source module | Main declarations and exact result |
|---|---|
| `LanguageSymmetryHelpers` | `compressed_square_eq_helper_product`; rectangular `helper_product_commutes`; adjoint-compatible `helper_gram_commutes`; `compressed_square_posSemidef`; `compressed_square_ne_zero_iff`; a noncommuting real 2×2 ablation witness |
| `LanguageSymmetryFourier` | `translation_invariant_eq_circulant`; `circulant_mulVec_character`; full-basis `circulant_toMatrix_complexBasis`; `productCharacterBasis`; `seasonalBinaryBasis`; correct all-ones Kronecker decomposition and mixed-mode annihilation |
| `LanguageSymmetryBinary` | Positive-domain `log_ratio_eq_zero_iff`; actual `binary_log_affine_closed_form`; positivity and logarithm of the finite attribute product |
| `LanguageSymmetryWalsh` | Native `coordinateSign` and `coordinateCharacter`; nontriviality and injectivity; `attributeLogKernel_expansion`; exact constant, coordinate, and zero-outside-support eigenvalues |
| `LanguageSymmetryToeplitz` | Both scaled product identities; `expToeplitz3_inv`; generic endpoint/cyclic-shift noncommutation and the decaying rational Toeplitz counterexample at `α=1/2` |
| `LanguageSymmetryRepresentationGeometryPoset` | Helper-column permutation covariance implies a circulant Gramian and full character diagonalization; `seasonal_attribute_eigenvalue` and its seasonal/coordinate specializations |

There are 65 theorem declarations and 16 definitions in these six modules.
The audit companion lists all 81 public declarations. The filename `Poset`
follows the intake: the mathematical dependencies are implemented by imports
and theorem applications, not by claiming that an enumeration of topics proves
a formal causal partial order.

For the binary part, put `β_r = binaryLogContrast (s r)` and
`c = ∑ r, binaryLogMean (s r)`. With counting measure on the binary states,
the proved eigenvalue is

\[
\lambda_\psi=2^d\left(\mathbf 1_{\psi=0}c+
  \sum_r\mathbf 1_{\psi=\chi_r}\beta_r\right).
\]

Here `0` is Mathlib's trivial additive character (the constant-one function).
The coordinate characters `χ_r` are constructed and proved distinct and
nontrivial. Thus their eigenvalues are exactly `2^d β_r`; all other nonconstant
attribute modes vanish. In the joint seasonal kernel, a nonconstant seasonal
mode has eigenvalue `2^d μ_χ`, and a pure coordinate mode has eigenvalue
`N * 2^d * β_r`. No empirical embedding theorem is inferred from these identities.

## Validation and observed environment

Lean is pinned to `v4.34.1`; Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No root dependency pins are changed.

The normal root command

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Core.PeirceCompressionDefect
```

exited with code 1 before theorem compilation because the configured path
`external_refs/homotopy-hypothesis-lean4` is absent. A focused verification
project uses the same pinned toolchain and Mathlib to check the exact repository
source files and their imported owner. Its result must not be presented as a
successful root-package or whole-repository build.

The focused command

```sh
python3 verification/language-symmetry/check.py build InfoGeometry.LLM.LanguageSymmetryRepresentationGeometryAudit --wfail
```

completed successfully (3107 Lake jobs in the selected dependency graph), with
no compiler warnings. Its audit output covered all 81 public declarations.
The union of their axiom dependencies is exactly
`{propext, Classical.choice, Quot.sound}`. No claim of a `propext`-only footprint
is made.

Strict OpenGauss screening and `opengauss_cli.py refute --strict` reported zero
traps. The Gate 4 static review passed at its explicitly static scope. The
lexical vacuity linter emitted one `no_hyp_use` warning for
`coordinateCharacter_ne_zero`: its pattern captured the binder with trailing
whitespace and stopped before the proof body. Independent QA confirmed that
the proof explicitly uses the coordinate in the single-bit witness and derives
the contradiction `-1 = 1`. This is a reviewed false positive; the theorem was
not weakened or changed to suppress it. The scoped semantic-content scan found
no blocking or review findings. The staged proof gate passed. These checks are
separate from the actual Lean build and axiom inspection.

The root dependency pins are unchanged. The broad `InfoGeometry.LLM` umbrella's
new import edge is included, but its unrelated existing dependency subtree and
the root default targets are not certified by the focused check. Independent
source review returned **PASS**. A separate, non-authoring QA agent reran the
focused build, directly re-elaborated the audit file, checked all 81 axiom
records, and returned **ACCEPTED_WITH_LIMITED_SCOPE** for the exact sources
below. The focused dependency graph and the audited declarations are the
accepted scope; the root integration boundary remains open.

## Accepted source fingerprints

SHA-256 values recorded after independent review and QA:

| Source | SHA-256 |
|---|---|
| `LanguageSymmetryBinary.lean` | `055b1a28d7b7e85d23b399c4378f4ace6b4cfb3cc66e4d8f528eddce1be6a97d` |
| `LanguageSymmetryFourier.lean` | `7482423828bc7a77c62c0b0984207df0ab5fba23309b8018c2dcf8652f7400c9` |
| `LanguageSymmetryHelpers.lean` | `39c1b4bce6c53c981975de01ffecf67776241ffdfbcdb67e2dfbf0ccb23b070e` |
| `LanguageSymmetryRepresentationGeometryAudit.lean` | `f7b268622b3d9160501bc6a80bdd5d42d6e58b76cd09c37e9a5b068ce41f910e` |
| `LanguageSymmetryRepresentationGeometryPoset.lean` | `3757c69143cc3fe093c1515d784185dd8f416de7973b295eeaf3d8729a2c1a2d` |
| `LanguageSymmetryToeplitz.lean` | `af3ef03f1bd041358d2331e3f8a4446828b0cbf309706702ec170497ed7ae5e3` |
| `LanguageSymmetryWalsh.lean` | `e33ce9f4c2e77f878a3e9f4e29788d6a583e0bf54cc194947d22a92e769f5fec` |
| `verification/language-symmetry/check.py` | `18ce257b3cddfbdda0c21fb01bfe5ebe02c0060a895ea5d608acd870bbb43b8f` |
