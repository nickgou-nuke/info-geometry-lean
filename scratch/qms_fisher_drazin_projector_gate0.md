# Gate 0 contract: concrete Fisher–Souriau Drazin sectors

## Claim under consideration

For a nonempty finite score carrier `Fin m`, the Fisher–Souriau Hessian endomorphism and its canonical index-one Drazin inverse compose in either order to the score-centering projection. The kernel of the Hessian consists exactly of constant score vectors.

## Actual carrier and operations

- `fisherHessianEnd : (Fin m → ℝ) → Module.End ℝ (Fin m → ℝ)` in `lean/InfoGeometry/Synthesis/FisherSouriauGroupInverse.lean` is `Matrix.toLin'` of `fisherSouriauHessian`.
- `fisherSouriauHessian` is the finite log-sum-exp Hessian, with action `p_i * (x_i - souriauMomentMap s x)` established by `fisherHessianEnd_apply`.
- `centerScores` subtracts the unweighted arithmetic mean and is idempotent.
- The candidate inverse is `fisherHessianGroupInverseCandidate`; `fisherSouriauHessian_candidate_eq_drazinInverse` identifies it with `InfoGeometry.Singular.Drazin.drazinInverse`.

## Existing owner results

The owner proves the candidate group-inverse laws, both candidate compositions equal `centerScores`, the canonical Drazin identification, strict positivity of each attention weight, and normalization `attentionWeights_sum_eq_one`. The exact statements are in the owner source cited above; these are kernel-checked only after the current target build.

## Dependency and consumer trace

The owner is imported by `FisherSouriauGroupInverseAudit.lean`, `FisherSouriauGroupInversePermutation.lean`, `InfoGeometry/Synthesis/All.lean`, `InfoGeometry/All.lean`, and `InfoGeometry.lean`. The proposed results expose the already-established finite candidate laws at the canonical Drazin inverse and identify its harmonic kernel for downstream graded/colimit transport.

## Verified gap

The owner identifies the candidate with the canonical Drazin inverse but has no named theorem stating the two endomorphism compositions with that canonical inverse equal `centerScores`, nor a kernel characterization for `fisherHessianEnd` in terms of constant functions.

## Scope exclusions

This is a finite-dimensional statement on `Fin m`, with `m` nonempty. It does not prove spectral decomposition, five-grade or filtered-colimit transport, Dikin containment, self-concordance, or an infinite-dimensional Laplacian theorem.
