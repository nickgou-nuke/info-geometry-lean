# Future-pass packet: Clifford-wavelet transform in `Cl(3,1)`

## Source

- Paper: Shabnam Jahan Ansari and V. R. Lakshmi Gorty,
  "Analysis of Clifford-wavelet transform in `Cl(3,1)`",
  South East Asian J. of Mathematics and Mathematical Sciences
  Vol. 20, No. 2 (2024), pp. 299--322.
- DOI: `10.56827/SEAJMMS.2024.2002.22`
- Local PDF: `/home/goutev/Downloads/collection_for_formalization/2_20_2_1329451630_DOI 10.56827SEAJMMS.2024.2002.22 (3).pdf`
- Classification: upstream theorem-factory material. The integral-analytic
  claims are not current Lean closure.

## Symbol dictionary

| Paper term | Mathematical role | Repo-native carrier |
| --- | --- | --- |
| `Cl(3,1)` | space-time Clifford algebra | `InfoGeometry.Clifford.GradedGraceContraction.Cl31` |
| `⟨M⟩_k` | grade projection | `cliffordGradeProj Q31 k` |
| scalar part | grade-zero scalar readout | `InfoGeometry.Riemannian.hTrace_cl Q31` |
| reversion | grade-sign anti-automorphism | `CliffordAlgebra.reverse` |
| `ψ_{a,Θ,b}` | daughter wavelet | `InfoGeometry.Analysis.CliffordWaveletTransform.CliffordWaveletModel` + `SimilitudeParameter` |
| similitude group | dilation/rotation/translation | `SimilitudeParameter` (abstract, no group law proved in paper-facing owner) |
| `Wψ f` | Clifford-wavelet transform | `CliffordWaveletModel.waveletTransform` |
| reconstruction | inverse / reproducing stage | `CliffordWaveletModel.reconstruction` |
| admissibility | left-inverse reconstruction | `CliffordWaveletModel.admissible` |
| reproducing kernel | right-inverse reconstruction | `CliffordWaveletModel.reproducingKernel` |
| `Cψ` | admissibility constant | not formalized; open debt |

## Theorem families and status

### A. `Cl(3,1)` grade algebra — closed in repo

- Paper (2.4): five-grade decomposition of a multivector.
  Repo: `cliffordGradeProj_sum_range_apply`, specialized by
  `cl31_grade_decomposition`.
- Scalar channel: grade zero equals the Clifford scalar trace.
  Repo: `cliffordGradeProj_zero_eq_algebraMap_hTrace`, specialized by
  `cl31_scalar_projection_eq_algebraMap_hTrace`.
- Vector channel: grade one contains embedded vectors.
  Repo: `cliffordGradeProj_one_ι`, specialized by `cl31_vector_projection_ι`.

### B. Reversion / conjugation grade signs — partially available

The repo's general reversion grade-sign theorem lives in
`InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_reverse`.
That owner was not loadable in this pass because its dependency
`Geometry.LegendreDuality.lean` has an unrelated syntax error. Therefore no
paper-facing reversion theorem is asserted in the new owner. This is an
explicit open composition debt, not a falsified claim.

### C. Fourier transform and Plancherel — open analytic debt

- Paper (2.7), (2.10), (5.1), (5.2): two-sided Clifford Fourier transform and
  Plancherel/Parseval on `L²(ℝ(3,1), Cl(3,1))`.
- Repo has generic Hilbert/Schwartz Fourier Plancherel in
  `InfoGeometry.Analysis.CliffordWaveletNativeL2.integral_normSq_fourier`
  and `norm_fourier_toL2_eq`, but no Cl(3,1)-specific two-sided Fourier
  transform with the paper's kernel `e^{-e₁ω₁x₁ - i₄ ω⃗·x⃗}`.
- Do not identify the generic Hilbert Fourier theorem with the paper theorem.

### D. Daughter wavelets and covariance — finite interface only

- Paper (3.11): normalization `a^{-2} ψ(r_Θ^{-1}((x-b)/a))`.
- Repo: `SimilitudeParameter` records scale, translation, and rotation, but no
  group law, Haar measure, or measure-change theorem is proved in the
  paper-facing owner. The wavelet transform is witness-gated at the model
  level.
- Paper Theorems 4.1--4.5 (linearity, translation/dilation/rotation
  covariance, derivative property) are not asserted as analytic theorems here.

### E. Admissibility constant `Cψ` — open debt

- Paper (3.20)--(3.23): zero-mean admissibility, `Cψ = C̃ψ`, grade decomposition
  `Cψ = ⟨Cψ⟩₀ + ⟨Cψ⟩₁`, and an inverse formula with a denominator condition.
- No `Cψ` operator or inverse theorem exists in the repo. The scalar/vector
  inverse formula is not promoted because the printed OCR denominator and
  sign conditions are ambiguous and no native derivation is available.

### F. Inversion and reproducing kernel — abstract model level only

- Paper Theorem 6.1: weak inversion formula.
- Paper Theorem 6.2: reproducing kernel identity.
- Repo: `admissible` is left-inverse reconstruction; `reproducingKernel` is
  right-inverse reconstruction. The new owner proves the honest algebraic
  consequences:
  - `waveletTransform_injective_of_admissible`
  - `reconstruction_surjective_of_admissible`
  - `reconstruction_injective_of_reproducing`
  - `waveletTransform_surjective_of_reproducing`
  - `waveletTransform_bijective_of_admissible_reproducing`
- These are model-level invertibility facts, not the paper's integral formulas.

### G. Examples and physics applications — open debt

- Paper §7--8: exponential and Gaussian examples, fermionic field, Dirac
  equation, Klein--Gordon equation, and Feynman propagator readout.
- No example computation, Dirac equation solution, KG solution, or propagator
  theorem is formalized. Repo has separate Dirac/Krein/CAR owners, but no
  theorem connecting them to this wavelet transform.

## New Lean owner

`lean/InfoGeometry/Analysis/Cl31WaveletAlgebraicCore.lean`

Scope: grade decomposition/readouts plus abstract injectivity/surjectivity
consequences of reconstruction laws. No analytic integral theorem is asserted.

## Verification

```bash
flock /home/goutev/.hermes/cache/scratch/rm_export_verify.lock \
  nice -n 10 lake build InfoGeometry.Analysis.Cl31WaveletAlgebraicCore
```

Recorded result: exit 0, zero Lean errors, `Build completed successfully (3149 jobs)`.

## Explicit open debts

1. Cl(3,1)-specific Fourier kernel and Plancherel theorem.
2. Daughter-wavelet normalization via change of variables.
3. Translation/dilation/rotation covariance as integral identities.
4. Derivative property as Fourier-side multiplication.
5. `Cψ` admissibility constant, its grade decomposition, and inverse.
6. Weak inversion formula as an `L²` integral identity.
7. Reproducing kernel convolution identity on `L²(G, dλ)`.
8. Example 7.1/7.2 computations and §8 Dirac/KG applications.
9. Paper-facing reversion grade-sign theorem once the blocking dependency is repaired.
