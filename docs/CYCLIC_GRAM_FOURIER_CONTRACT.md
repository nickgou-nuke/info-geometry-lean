# Cyclic Gram matrices and Fourier modes

## Intake and theorem boundary

The user supplied <https://arxiv.org/abs/2602.15029> and requested the established
Lean 4 / native Mathlib formalization and upstream pull-request workflow.
The source examined on 2026-11-07 is version 3, revised 2026-06-29:
Dhruva Karkada, Daniel J. Korchinski, Andres Nava, Matthieu Wyart, and Yasaman
Bahri, *Symmetry in language statistics shapes the geometry of model
representations*. The fixed source is
<https://arxiv.org/html/2602.15029v3>.

The retrieved HTML was retained with SHA-256
`8b30eb3bb54a9af2c8da0be37539350334f7cc058fef58834e8401126fb63cc1`.
The source receipt identifies the version; it is not evidence for a Lean proof.

The selected mathematical target is the finite cyclic matrix mechanism in
Proposition 1 / Appendix E.2. This contract was recorded before implementation.
The repository base is `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.
The unchanged environment pins are Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Ground truth

Let `N : ℕ` with `[NeZero N]`, let `G = ZMod N`, and let `κ : G → ℂ`.
The carrier is the full native matrix algebra `Matrix G G ℂ`. Native
`Matrix.circulant κ` has entries `κ (i - j)`. The matrix-vector product is
Mathlib's `Matrix.mulVec`; matrix products keep their actual multiplication
order. No diagonal surrogate or supplied spectral certificate is used.

Use the counting-measure convention already fixed by native `ZMod.dft`:

\[
\widehat\kappa(k)=\sum_{a\in G}\operatorname{stdAddChar}(-ak)\kappa(a),
\qquad v_k(i)=\operatorname{stdAddChar}(ik).
\]

The raw matrix eigenvalue is `ZMod.dft κ k`, with no additional `1/N`.
If `J` is the all-ones matrix, centering is `P = I - N⁻¹ • J`.

### Intended proof chain

1. Simultaneous translation invariance reconstructs a matrix as the native
   circulant of its zero column.
2. Every native additive character is an eigenvector, by finite reindexing.
   Specialize to `stdAddChar` and reconcile the eigenvalue with `ZMod.dft`.
3. Prove the centering action, self-adjointness, and idempotence. Establish
   `P * circulant κ * P = circulant (κ - mean κ)`.
4. Use character orthogonality to prove that centering kills the constant
   mode and fixes every nonzero standard Fourier mode. Transfer the actual
   eigenvector equation to the centered matrix.
5. Construct an autocorrelation matrix as the Gram matrix of cyclically shifted
   features, with conjugation for complex features. Prove positive
   semidefiniteness from this construction and preserve it under centering.
6. Prove the complete centered matrix action by native DFT and inverse DFT.
   Compute the unnormalized autocorrelation spectrum as `normSq (dft g k)`.
7. Construct the native real feature matrix with rows
   `(a * re χ(k*i), a * im χ(k*i))`, prove its full real circulant Gram
   matrix, and prove its constant diagonal `a²`.

The autocorrelation convention is the unnormalized sum
`R_g(b) = ∑ t, g (b+t) * star (g t)`. Its matrix is `C_g * C_gᴴ` and its
spectrum is `|dft g|²`. An averaged autocorrelation has an additional `1/N`
on both sides. The real Fourier pair has squared row norm `a²`, hence radius
`|a|`; distinctness, two-dimensional span, and full-circle coverage are not
asserted.

The case `N = 1` is included. Nonzero-frequency statements then have no
instances. No parity assumption is needed, and no claim that every nonzero
frequency has a distinct conjugate partner is made.

## Owner search and reuse

The complete restored `lean/` and `proofs/` source trees were searched for
cooccurrence spellings, Fourier, circulant, Gram, centering, and translation
invariance. Candidate owners and their consumers were read. The pinned Mathlib
source was also searched. This is a bounded source search, not a classification
of all semantically related statements in the repository.

| Owner | Actual reused content / boundary |
|---|---|
| `LLM/ZModFourierBridge.lean` | Native cyclic additive characters and `ZMod.dft`; extend this owner for matrix spectral statements. |
| `LLM/FourierSuperposition.lean` | Translation invariance from a supplied finite character sum; does not derive matrix geometry from statistics. |
| `LLM/FourierCharacterEncoding.lean` | Custom units-valued character data; use native cyclic characters for the present result. |
| `Canonical/AttentionSpectralHeadsBridge.lean` | Consumer of the character-sum surface, without a cooccurrence Gram construction. |
| `LLM/PositionalEncodingRepresentation.lean` | Genuine real-parameter representation from normalized invertible factors, with different hypotheses. |
| `Canonical/PlabicGramEigenvectorTransport.lean` | Native rectangular Gram spectral transport; does not construct the cyclic spectrum. |
| Mathlib `LinearAlgebra/Matrix/Circulant` | Native difference matrices, product closure, conjugate transpose, and circulant commutation. |
| Mathlib `Analysis/Fourier/ZMod` | Native invertible DFT and exact sign/normalization convention. |
| Mathlib `NumberTheory/LegendreSymbol/AddCharacter` | Character orthogonality and primitive standard cyclic character. |
| Mathlib `LinearAlgebra/Matrix/PosDef` | Constructed Gram positivity and congruence transport. |

Nearby retrocirculant and Weyl-mixing certificates supply spectral conclusions
as fields or cover fixed dimensions. They are not proofs of the new arbitrary
cyclic matrix theorem. The focused Gram/centering owner will consume the
extended native Fourier owner.

## Claims retained outside the formal theorem

| Source claim | Disposition |
|---|---|
| Periodic translation symmetry gives Fourier matrix modes | Selected finite theorem. |
| Centering removes the DC component | Selected exact matrix theorem. |
| Autocorrelation supplies a positive kernel | Selected constructed Gram theorem, with explicit normalization. |
| Trained embeddings have the specified Gram matrix | Open here: optimization, balanced factorization, rank, and convergence are not proved. |
| A selected statistics submatrix determines the embedding Gram | Insufficient alone: Appendix B uses the restricted spectral parts of the global matrix, hence global matrix absolute value. |
| Entrywise PMI/logarithm preserves positivity | Not assumed or claimed; a positive autocorrelation matrix need not remain positive after entrywise logarithm. |
| Multidimensional half-space enumeration, continuum kernels, decoding bounds, perturbation robustness, and empirical LLM geometry | Outside this finite cyclic contract. |

In particular, no empirical statement or philosophical interpretation is
promoted to a Lean theorem. Native finite matrix results establish their own
stated types. They do not replace the missing optimization and analytic steps.

## Promoted theorem surface

The implementation adds **35 explicitly named theorems and 3 definitions**.
The existing Fourier owner gains 9 theorems; the new Gram owner contains
26 theorems and the definitions `cyclicCentering`, `cyclicAutocorrelation`,
and `cyclicRealFourierPair`.

| Mathematical step | Representative declaration |
|---|---|
| Symmetry reconstructs the native matrix | `matrix_translation_invariant_iff_eq_circulant` |
| Character eigenvectors, including nonzeroness | `circulant_hasEigenvector_stdAddChar` |
| Full cyclic operator diagonalization | `dft_circulant_mulVec` |
| Exact two-sided centering | `cyclicCentering_circulant` |
| DC removal and retained frequencies | `centered_circulant_hasEigenvector_stdAddChar` |
| Complete centered operator reconstruction | `centered_circulant_mulVec_eq_invDFT` |
| Constructed positive autocorrelation Gram | `cyclicAutocorrelation_gram`, `cyclicAutocorrelation_posSemidef` |
| Squared Fourier amplitude | `dft_cyclicAutocorrelation_eq_normSq` |
| Centered feature factorization | `centered_cyclicAutocorrelation_gram` |
| Real two-coordinate geometry | `cyclicRealFourierPair_gram_eq_circulant`, `cyclicRealFourierPair_gram_diag` |

These declarations are in `InfoGeometry.LLM`. Their dependency order is
actual proof reuse: finite character reindexing gives the spectrum; mean
subtraction and character orthogonality give centered eigenvalues; invertible
native DFT gives reconstruction; the adjoint-kernel DFT identity combines with
the constructed Gram factorization to give the autocorrelation spectrum.

## Acceptance record

Disposition: `[kernel_verified]` for the exact declarations and
`[accepted_limited_scope]` for the finite cyclic paper formalization.
The root integration gate is separately blocked, as described below.

### Independent verification

- The exact selected repository source closure comprises three modules:
  `InfoGeometry.Algebra.FiniteSpinAlgebra`,
  `InfoGeometry.LLM.ZModFourierBridge`, and
  `InfoGeometry.LLM.CyclicGramGeometry`.
- The maintained `tools/quality/check_operator_geometry.py` checked this
  complete closure with explicit `--target` selections. An independent
  acceptance agent compiled it again into fresh output with
  `-DwarningAsError=true`: **PASS, zero warnings**.
- A native Lean audit enumerated every declaration owned by both touched
  modules, including generated helpers: **50 declarations**, comprising
  17 from `ZModFourierBridge` and 33 from `CyclicGramGeometry`. All passed.
  The audit includes 46 theorem declarations and 4 definitions; these counts
  include existing declarations and generated equations, so they differ from
  the count of 35 newly written theorems.
- The exact transitive axiom union is `propext`, `Classical.choice`, and
  `Quot.sound`. No custom axiom, unsafe declaration, or partial declaration was
  accepted. This is ordinary native Mathlib mathematics, not a claim of
  eliminating classical foundations.
- The independent semantic reviewer returned **PASS** for the final sources,
  including normalization, product order, nonzero eigenvectors, boundary
  frequencies, Gram construction, and the limited interpretation of the real
  Fourier pair. Generation, semantic audit, and acceptance were separate roles.
- Untouched `FiniteSpinAlgebra` and the root `lean-toolchain`, manifest, and
  `lakefile.lean` matched the base commit's Git blobs. Mathlib and all eight
  of its dependencies retained their exact manifest revisions and unchanged
  tracked sources.

The official Lean 4.34.1 release binary was verified against its published
SHA-256. The execution environment needed a narrowly scoped compatibility
shim for its own-process executable-path lookup: numeric `/proc/<pid>/exe`
lookups were normalized to `/proc/self/exe`. It did not modify the Lean kernel,
mathematical sources, or dependency pins.

Frozen mathematical source SHA-256 values:

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/LLM/ZModFourierBridge.lean` | `4a663b8d09f76e5a2072954d46925ec3dec6b64bcf5e9ea771214af7f6dd8ab3` |
| `lean/InfoGeometry/LLM/CyclicGramGeometry.lean` | `0ffd830f18dad9abed6ac89f2a2ca133965d9752bcec94082733094d19bac208` |

### Root integration boundary

The actual command

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.LLM.ZModFourierBridge InfoGeometry.LLM.CyclicGramGeometry
```

exited **1** during package resolution:

```text
error: HomotopyHypothesis: package directory not found:
  external_refs/homotopy-hypothesis-lean4
```

That required path is absent, untracked, and ignored; current tracked
configuration supplies no source URL or immutable revision from which to
restore it. The manifest also requires an absent ignored Atlas checkout.
No placeholder package, dependency update, or manifest edit was introduced.
The successful isolated native checks establish the stated theorem closure;
they do not establish a successful root-package build.

The final commit-hook and pre-push outcomes are recorded after their actual
execution. Publication is a draft pull request pending root integration.
