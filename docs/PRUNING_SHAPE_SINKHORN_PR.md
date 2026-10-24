# Constructive attention pruning and shape–Sinkhorn–detector contracts

## Review base and status

This additive change is based on PR #191, `feat/attention-identifiability`,
commit `c8960e2893dd8f0477e090ba3b6fb14269f40b74`. It does not merge or modify
its parents, main, dependency source, toolchain, or package pins. The earlier
pruning/Gramian/log-coupling delivery was a candidate archive, not a verified
PR. Those candidates are now submitted together with the shape–detector work.
No umbrella import is changed: consumers explicitly import the modules.

All five Lean modules require the scoped compilation and axiom check. Draft
status must remain until those checks pass and the dependency stack is ready.
Python checks and small-matrix examples do not certify Lean or a Python-to-Lean
refinement theorem. Workflow logs are the authoritative check result.

## Source-derived scope

- `Pasted text(20261023-072121).txt`: minimum-ratio homogeneous-kernel pruning.
- `Pasted text (2)(20261023-072126).txt`: Gramian inverse and finite Stein contracts.
- `Pasted text (3)(3).txt`: Tri-NMF marginals and doubly centered log interaction.
- `Pasted text(20261023-073850).txt`: five-factor shape–Sinkhorn–detector
  decomposition and symmetric bipartite lifting.
- `Pasted text (2)(20261023-083829).txt`: balanced-gauge log-domain scaling,
  two Gramian solves, and the parity-odd correction.

The new source preserves these constructions. Qualifications and implementation
changes relative to the notes are explicit below; the literal uploaded code
is not claimed to compile unchanged.

## Lean modules

`Routing.CaratheodoryPivotContracts` reuses the existing homogeneous decoder,
its kernel, and native affine independence. It records an actual minimum-ratio
pivot, preserves mass/value/nonnegativity, removes one working-set member, and
inducts until independence. Stopping merely at d+1 points is insufficient when
values are dependent. Actual positive support gives a positive step; a larger
working set can permit a zero step. The rational runtime stops on independence
and independently replays every pivot certificate.

`Canonical.GramianInverseContracts` reuses existing Drazin and MP predicates.
It builds A^T H as an MP inverse from an explicitly symmetric group inverse H
of AA^T, proves the CMP outer-inverse and core-recovery identities, and records
the exact projector-level orthogonality criterion. An oblique idempotent with
zero nilpotent part refutes the source prose's converse from vanishing
operator cross-Gramians. Commuting Gramians are not the same as normality.

`Canonical.FiniteSteinInverse` proves the finite residual identity
sum(a^m X b^m) - a sum(a^m X b^m) b = X-a^k X b^k.
It proves existence and uniqueness when the left factor is nilpotent, and
specializes to the left/right star-Gramians. This is a discrete Stein equation,
not the continuous Sylvester equation aW+Wb=X.

`Probability.BipartiteLogCoupling` includes rectangular marginal pushforward,
total mass, diagonal coincidence peaks, all six Frobenius orthogonality pairs,
and entrywise log-scaling invariance with positivity hypotheses. It does not
claim that two mixture components always produce nonzero interaction.

`Routing.ShapeSinkhornBipartite` adds supplied five-factor gain absorption,
actual native Birkhoff mixture existence, total mass, log-gain reconstruction,
balanced log gauge, native block-matrix symmetry and bistochasticity,
two-step Gramian splitting, the minus-one parity eigenvector, and the
parity-corrected reduced Poisson equation under explicit solved-system
hypotheses. The block representation is a finite matrix instance; it does not
replace Streaming.BipartiteGraphDirac's cochain/Dirac owner.

## Explicit qualifications to the new attachments

1. C=U S V^T is a model or supplied factorization. Arbitrary empirical C need
   not admit a specified low-rank positive-core factorization, and this whole
   factorization is not canonical or unique. Gain gauge fixing does not make
   U,V identifiable.
2. Finite Sinkhorn iterations preserve the gain reconstruction algebraically,
   but do not guarantee exact row and column normalization. The runtime returns
   the unaltered iterate, separate residuals and a convergence flag.
3. Symmetry of the doubled Laplacian does not justify a rank-one stationary
   correction for disconnected cores. B=I with K>1 is a counterexample. The
   solver checks bistochastic residuals and the numerical spectral gap of the
   two regularized Gramian systems, and rejects invalid inputs without changing
   B. Strictly positive exact B is a sufficient mathematical connectedness case;
   near-disconnected numerical B can still fail the gap check.
4. The minus-one parity mode is retained: delta=(mean(bS)-mean(bD))/2 and the
   reconstructed correction is (delta/2,-delta/2). Bipartiteness prevents ordinary
   powers of the lifted chain from converging even when the graph is connected.
5. The Lean reduced-solve theorem is conditional on its equations. Neither
   inverse existence, universal Drazin=MP, the unique stationary kernel, nor
   Sinkhorn convergence is smuggled into the theorem as a prose conclusion.
   In particular the source's block theorem proves symmetry/normality, not an
   imported, checked Drazin=MP theorem for this new operator.
6. Diagnostic names are numerical residuals, never `verify_lean_identities`.
   The code differentiates executed PyTorch operations; no custom surrogate or
   replacement backward pass is installed.
7. Generalized KL preserves actual observed zero counts via xlogy. No clipping
   or invented positive counts is used. Logits producing underflow/overflow are
   rejected. The module is float32/float64; tests and gradchecks use float64.
8. Feature encoding with U^T,V^T is not an inverse to U,V decoding. No claim of
   universal attention equivalence, causal Sinkhornization, KV eviction, training
   convergence, topological protection, or a measured performance gain is made.

## Checks and local commands

Authoring runtime: PyTorch 2.10.0+cpu. Locally passed: 12 exact rational pruning
tests (including 405 exhaustive cases), 15 shape/bipartite tests, and nine
exact algebra regression groups. The two gradchecks cover Sinkhorn scaling
and the solver on a bistochastic parameterization. CI repeats the runtime checks
before checking the full unchanged Lean import closure at the repository pins.
It audits every new declaration and rejects nonstandard axiom dependencies.
It never strips dependency imports/annotations, updates pins, or cleans caches.

```bash
python -m unittest discover -s tests -p test_certified_caratheodory.py -v
python -m unittest discover -s tests -p test_shape_sinkhorn_detector.py -v
python tools/exact_contract_regressions.py
python tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Routing.CaratheodoryPivotContracts \
  InfoGeometry.Canonical.GramianInverseContracts \
  InfoGeometry.Canonical.FiniteSteinInverse \
  InfoGeometry.Probability.BipartiteLogCoupling \
  InfoGeometry.Routing.ShapeSinkhornBipartite
```

These commands are sequential. Successful scoped checks do not imply a green
full-repository build. The exact-rational and floating-point implementations
are not proved equivalent to their Lean specifications by this PR.
