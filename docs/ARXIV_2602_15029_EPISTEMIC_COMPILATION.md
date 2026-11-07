# Epistemic compilation: translation symmetry and representation geometry

## Scope and source

This note normalizes Karkada, Korchinski, Nava, Wyart, and Bahri, “Symmetry in
language statistics shapes the geometry of model representations” (arXiv
2602.15029; ICML 2026). The paper studies translation-symmetric co-occurrence
statistics, their Fourier geometry, learned embeddings, and robustness under
perturbations. Its periodic and open-boundary models have different spectral
assumptions; conclusions from one are not silently transferred to the other.

Primary sources: [arXiv abstract and version history](https://arxiv.org/abs/2602.15029),
[PMLR publication](https://proceedings.mlr.press/v306/karkada26a.html).

## Fundamental cut

* **Statistical thesis:** on a periodic latent domain, pair statistics depend
  only on displacement. The resulting target matrix is circulant. The paper's
  target is a normalized excess co-occurrence ratio and is only approximately
  PMI in its stated setup.
* **Representation shadow:** a factorization or learned embedding can exhibit
  circles, helices, and low-dimensional coordinates. This step needs the
  paper's factorization, rank, dimension, and spectral hypotheses; it does not
  follow from translation invariance alone.

The algebraic implication formalized here is deliberately the finite one:
composition of two displacement kernels preserves simultaneous translation
invariance. It is a prerequisite for spectral analysis, not a formal proof of
the paper's embedding theorem.

## Four relational layers

1. **Internal consistency:** a periodic kernel has entries `f (j - i)` and is
   unchanged when both indices are shifted by the same group element.
2. **Outward projection:** for a finite periodic model, Fourier characters
   diagonalize circulants. A real even kernel has equal eigenvalues at paired
   frequencies `k` and `-k`, yielding the sine/cosine plane except at
   self-conjugate frequencies.
3. **Inward perturbation:** masking co-occurrences changes the matrix. The
   paper's robustness result uses a spectral gap and its latent-variable
   model; it is not implied by closure of the circulant algebra under products.
4. **Unexamined boundary:** an open interval gives a Toeplitz problem. The
   paper solves a specific exponential-kernel case with its own boundary and
   continuum assumptions. A general Toeplitz matrix is not thereby
   Fourier-diagonalized.

## Integrative bridge and exact aporia

The shared object is a translation action on a finite index group. It acts on
both endpoints and reindexes the intermediate state in matrix composition.
That gives the exact identity

```text
(K_f K_g)(i + a, j + a) = (K_f K_g)(i, j),
where K_f(i,j) = f(j-i).
```

This is the second-order closure law formalized in
`InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry`.

The gap between this law and the paper's high-level conclusion is the central
aporia: invariant statistics constrain an operator, but do not uniquely fix a
learned factorization. Factorization symmetries, dimension truncation, the
specific spectral hypotheses, optimization, and empirical validation must be
accounted for before identifying a model representation with the Fourier
geometry.

## Seven-node dependency order

```text
LΣ₁ displacement symmetry
  → LΣ₂ finite relative-kernel matrix
  → LΣ₃ composition closure under simultaneous shifts
  → LΣ₄ cyclic characters / Fourier diagonalization (separate theorem needed)
  → LΣ₅ conjugate frequency-pair geometry under real-even symmetry
  → LΣ₆ embedding factorization and dimension assumptions
  → LΣ₇ perturbation robustness and empirical comparison
```

Only `LΣ₂ → LΣ₃` is added as a new Lean result here. Existing Fourier and
attention owners support parts of `LΣ₁`, `LΣ₂`, and `LΣ₄`; they do not supply
the entire paper-specific chain.

## Repository owner map

| Paper primitive | Repo-owned source | Exact scope |
|---|---|---|
| Native circulant reconstruction & DFT diagonalization (`ℤ_N`) | `src/InfoGeometry/LLM/ZModFourierBridge.lean` (`matrix_translation_invariant_iff_eq_circulant`, `circulant_hasEigenvector_stdAddChar`, `dft_circulant_mulVec`) | Exact equivalence between simultaneous translation invariance and `Matrix.circulant`, plus Fourier character eigenvectors with eigenvalue `ZMod.dft κ k` |
| Centered circulant spectrum, autocorrelation PSD Gram, & real 2D Fourier circle coordinates | `src/InfoGeometry/LLM/CyclicGramGeometry.lean` (`cyclicCentering_circulant`, `centered_circulant_hasEigenvector_stdAddChar`, `centered_circulant_mulVec_eq_invDFT`, `cyclicAutocorrelation_posSemidef`, `dft_cyclicAutocorrelation_eq_normSq`, `cyclicRealFourierPair_gram_eq_circulant`) | Two-sided centering on `ZMod N`, Wiener–Khinchin power spectrum, and explicit `N × 2` real cosine/sine embedding matrix |
| Helper-word two-hop Peirce Gramian recovery & shift equivariance under ablation (`P M P = 0`, Sec. 4.1.1 & App. C.1) | `src/InfoGeometry/Canonical/LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.lean` (`helper_word_ablation_resilience_and_shift_equivariance`, `ls7_peirce_helper_excursion_bkm_attribute_surprisal_and_kms_toeplitz_laplacian`) | Proves `P * (M * M) * P - (P * M * P) * (P * M * P) = conePlus P M * coneMinus P M`, survival `P * (M * M) * P = conePlus P M * coneMinus P M` when `P * M * P = 0`, and shift commutation `comm T_P (conePlus P M * coneMinus P M) = 0` under helper shift equivariance |
| Binary semantic attribute involution linearization (App. D, Eq. 44) & joint `ℤ_N × V₄` Fourier–Walsh basis | `src/InfoGeometry/Canonical/LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.lean` (`involution_exact_linearization_of_binary_attribute_pmi`, `ls7_peirce_helper_excursion_bkm_attribute_surprisal_and_kms_toeplitz_laplacian`) & `src/InfoGeometry/Canonical/V4GroupFourierTransform.lean` | Proves exact linear collapse of `Real.log (1 + s * σ)` and `f_plus * (1 + σ) + f_minus * (1 - σ)` for `σ² = 1`, two-sheeted BKM operator normal form, and joint `ZMod.stdAddChar × v4Character` multiplicativity |
| Open-boundary 1D exponential Toeplitz kernel & tridiagonal discrete Laplacian inverse (Sec. 3.2, Prop. 3) | `src/InfoGeometry/Canonical/LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.lean` (`open_boundary_exponential_kernel_tridiagonal_inverse`, `symToeplitz3_comm_cyclicShift3`) | Proves `symToeplitz3 1 α (α ^ 2) * kmsTridiagonalLaplacian3 α = (1 - α ^ 2) • 1` on `3 × 3` matrices and `[symToeplitz3 t0 t1 t2, cyclicShift3] = (t2 - t1) • toeplitzBoundaryDefect3` |
| 3×3 circulant commutes with cyclic shift | `src/InfoGeometry/Canonical/SmithBlockCirculantMoorePenrose.lean`, `blockCirculant3_commutes_cyclicShift` | Concrete dimension 3 circulant commutation |
| Finite Fourier character kernels & folded translation-symmetry embeddings | `src/InfoGeometry/Canonical/LanguageStatisticsCirculantBirkhoffYangianPeircePoset.lean` (`InfoGeometry.Information.TranslationSymmetryEmbeddings`), `src/InfoGeometry/LLM/FourierCharacterEncoding.lean`, `src/InfoGeometry/LLM/FourierSuperposition.lean` | Character sums, difference-kernel equivalence, and two-harmonic torus Gramian identities |
| Relative-position attention score | `src/InfoGeometry/LLM/PositionalEncodingRepresentation.lean`, `transformed_attentionScore_depends_only_on_difference` | Conditional on the score-operator relation in its hypothesis |
| Finite softmax / Markov kernel | `src/InfoGeometry/QuantumContext/FiniteSoftmaxMarkovKernel.lean` | Row-stochasticity and finite Markov results; no cyclic symmetry unless supplied |
| Bistochastic/Sinkhorn scaling | `src/InfoGeometry/Thermodynamics/SinkhornBirkhoffGibbsBridge.lean`, `src/InfoGeometry/Routing/BirkhoffVonNeumann.lean` | Two-sided marginal scaling and convex permutation decomposition |
| Peirce corner centralizer & recursive tensor Peirce decomposition | `src/InfoGeometry/Algebra/IdempotentCornerCommutant.lean`, `src/InfoGeometry/Core/TensorPeirceDecomposition.lean` | Algebraic commutant theorem and recursive `2^k × 2^k` tensor block extraction |

The names “Yangian,” “Birkhoff,” “MoE,” “Clifford,” and “Peirce” are not
additional nodes in this paper's proof poset. Combining them requires a typed
map and a compatibility theorem; proximity or shared vocabulary is not such a
map.

## Formalization boundary

The new theorem assumes a finite additive commutative group and a semiring and
proves translation invariance of the product of two relative-kernel matrices.
It does not formalize a general `N`-point DFT, eigenvalue multiplicity, PCA or
embedding optimization, Weyl/Davis–Kahan estimates, data-level experiments, or
the continuous latent-variable robustness theorem. Those remain separate
targets with their own contracts.
