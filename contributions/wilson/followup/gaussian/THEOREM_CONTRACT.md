# Gaussian specialization followup

## Intake and source authority

This candidate follows the user's `Pasted text(20261124-150457).txt` and the
Gaussian/RG contribution request. It is grounded in upstream
`MathePhysics/4D_Wilson_Loop_RG` commit
`9a4492cc6bdf3338379123a085af59dfd8018a9c`, specifically `EffectiveForm.lean`
and `Convolution.lean`, and the previously prepared weighted matrix owners.

## Corrections to the supplied proposal

1. `EffectiveForm.lean` defines `effStiffness` using the plain Euclidean
   adjoint. It does not define `blockAdjoint`, `blockMatrix`,
   `effectiveHessian`, `minimizerField`, or `effectiveOperator`. The source
   comment states `Q*_k = L^(kd) Qᵀ` for the lattice adjoint; its exact lattice
   interpretation is not an already constructed Lean operator in this file.
2. `Convolution.lean` retains `s` and proves the coefficient
   `α*β/(β+s*α)`. Its comment identifies `s = L^(-d)` for the block average.
   An additional assumption `s = 1` would specialize this; it is not the
   existing theorem's normalization.
3. The supplied identity with `blockMatrix = w • (Qᵀ*Q)` counted the factor
   `w` twice. The corrected identity is
   `finePrecision A ((α*w) • 1) Q = A + α • ((w • Qᴴ)*Q)`.
4. The supplied noncommuting theorem did not prove positive definiteness,
   and its ordering comparison used the precision instead of its inverse.
   The candidate proves both `PosDef` hypotheses and compares the actual
   inverse occurring in the covariance formula.

## Exact construction and theorem scope

`WeightedCoarseGrainingSpecialization.lean` proves:

- For arbitrary finite index types, scalar positive fine/coarse precisions
  `β*I` and `α*I`, and `Q*Qᴴ = s*I`, the native `coarseCovariance` is
  `((β+s*α)/(α*β))*I`.
- For `s ≥ 0`, the native `coarsePrecision` is
  `(α*β/(β+s*α))*I`, using positivity and the previously proved Woodbury
  theorem.
- The matrix coisometry hypothesis transports to the exact hypothesis of
  upstream `integral_blockKernel_mul_blockKernel`. The resulting theorem
  retains the actual integral and the ordered composite averaging matrix.
- The adjoint bilinear identity for fine/coarse scalar weights `u,v` uses
  `(v/u)*Q*`; the algebraic identity only requires `u ≠ 0`. For positive
  weights this is the scaled-inner-product adjoint relation.
- The general matrix weighted-adjoint term contains the scalar `w` once.

`WeightedCoarseGrainingExamples.lean` proves for the explicit real matrices

```
A = [[2,1],[1,1]],  R = [[1,0],[0,3]],  Q = [[1,1],[0,1]]:
```

- `A.PosDef` and `R.PosDef`;
- exact nonsingular inverse formulas;
- `A*R ≠ R*A`;
- `Q*A⁻¹*Qᴴ ≠ A⁻¹*(Q*Qᴴ)`;
- `(coarsePrecision A R Q)⁻¹ = [[2,1],[1,7/3]]`;
- positive definiteness of the actual effective precision.

There are 14 public theorems and 14 requested axiom reports. The three example
matrices are concrete definitions, not additional assumptions. Both source
modules reuse the existing weighted owners; neither overwrites them.

## Boundaries

These are real, finite-dimensional matrix and scalar-kernel integration
results. The integral consumer in this specialization module uses the existing
scalar kernel. The combined Gaussian contribution supplies general normalized
matrix-weighted integration separately in `WeightedKernel.lean` and
`WeightedKernelConvolution.lean`. Neither the generic weighted-adjoint identity
nor the example proves model-specific gauge coercivity, a lattice refinement
relation, an RG error estimate, or a continuum-limit theorem.

## Validation

The final revised sources passed exact destination validation under unchanged
Lean **4.34.0-rc2** and Mathlib
`8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a` in GitHub Actions run
[`45458690593`](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45458690593),
job `138675000523`, source commit `0d848bd5`. The parent confirmed that these
two candidate owners are source-identical to that checked snapshot.

This check compiled the complete Gaussian package with warnings treated as
errors and checked a separate fresh axiom transcript for all **54** public
Gaussian theorems, including these **14** additions. Source-hash and unchanged
dependency-pin checks passed. The allowed foundations remain `propext`,
`Classical.choice`, and `Quot.sound`.

An independent semantic review by both the Gaussian integration worker and
the state-limit worker found no statement weakening, false lattice-model
identification, or hidden commutativity hypothesis.

The separate preliminary Lean **4.34.1** / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` check completed at
2026-11-24 18:39:30 UTC. All nine recorded dependency/owner/audit modules
compiled with zero warnings and zero errors. The fresh 14-report axiom
transcript passed the shared checker, and all recorded source hashes still
match the checked files. Receipts and complete logs are in `evidence/`, and
the parsed transcript result is in `axiom-audit.json`.

The exact local command was:

```bash
python3 wilson-contributions/check_candidate.py gaussian \
  GaussianBlockSpin.WeightedCoarseGrainingFollowupAudit \
  --source-root wilson-contributions/followup/gaussian \
  --output-name gaussian-followup --wait-for-build-lock
```

The shared compilation lock was released on completion. No second local run
was needed after the independent destination-version pass.
