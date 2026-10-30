# Noncommutative boundary pairing contract

Intake: 2026-10-27 conversation, forward/backward epistemic-compilation narrative.
The user's operative requirement is: “ignore the physics prose ... stay within
non-commutative matrix operator algebra and geometry”, with complete Lean proofs.
The intake also asserts exact identifications among Bayesian smoothing, weak
values, optical phase conjugation, thermal doubling and attention. These
identifications are not hypotheses or conclusions of this formalization.

## Carrier and existing owners

- `Matrix n n ℂ`, arbitrary finite index type, full multiplication and adjoint.
- Existing `InfoGeometry.Quantum.Choi.krausMap` from
  `lean/InfoGeometry/Quantum/ChoiCompletePositivity.lean` is the forward map.
  It is a complex linear map with value `Σ i, V i * X * star (V i)`.
- Backward propagation uses the same owner at the adjointed Kraus family.
- `Matrix.trace`, `Matrix.PosSemidef`, `MatrixOrder`, `CFC.sqrt`,
  `LinearMap.ker`, and the complete lattice of native submodules are reused.
- Existing `Quantum/KrausAmplificationCP.lean` supplies the amplification owner;
  this task does not rebuild it or claim a new CP equivalence.

Source search: full sparse checkout of repo-owned `lean/InfoGeometry`, searches
for krausMap, trace duality, forward/backward propagation, PSD sandwiches and
fixed submodules; read the Choi and Kraus-amplification owners, their imports,
and consumers. No claim of repository-wide novelty is made. Runtime Arango/
compiler DAG services are not present in this environment. The dependency
order below is source-level, not a purported fresh extraction of that graph.

## Exact theorem goals and dependency order

1. Native Kraus action -> single-step trace duality and PSD preservation.
2. Trace duality + trace nondegeneracy -> trace preservation iff backward
   unitality; invariant operators iff fixed points of the backward map.
3. Single-step duality -> finite-word duality -> pairing invariant at every
   cut of a finite ordered word. Composition order reverses on the dual side.
4. PSD + native square root -> positive sandwich -> its boundary trace;
   nonzero boundary weight -> trace-one normalization.
5. Hermitian factors -> product Hermitian iff factors commute. No commutation
   hypothesis is imposed on the sandwich or propagation theorems.
6. Backward fixed kernels -> intersection geometry -> antitone refinement
   under inclusion of operator constraints and union/intersection law.

These are logical dependencies, not physical time. Finite words encode ordered
composition; the submodule lattice orders actual invariant-operator constraints.
No arbitrary hand-authored 'causal' relation is advertised as compiler evidence.

## Boundary and anti-vacuity obligations

Kraus maps are not called trace-preserving channels without normalization.
Square-root sandwiches specify an operation, not a unique posterior. Their two
orders can differ. A positive normalized state requires positive nonzero trace;
no normalization result may silently accept zero weight or an empty carrier.
Fixed submodules alone do not establish a positive normalized fixed point,
uniqueness, convergence, contraction, EM dynamics, Bayesian calibration, or
semantic faithfulness of natural-language specifications. No optical error
cancellation, physical retrocausality, or universal error-correcting mechanism
is claimed. No scalar, diagonal, or commuting substitute is used for the full
operator carrier.

## Verification record (2026-10-27)

Risk: R2, finite representation-level extension of existing owners.
Disposition: **QA_BLOCKED; unverified proof candidates; no kernel acceptance**.

The generation, semantic-audit and QA roles were separate. The independent
semantic auditor passed the statements within the finite scope above. The
independent QA agent did not issue acceptance because compilation and axiom
inspection could not run.

- Base repository commit: `b143075bbf27e75860a1011e04423a0f227b7c41`.
- Source commit, local: `c46983fc3145ea3b64dadeff5922a2c879af8795`.
- Same source tree published as `46386ccdc09922014f48b20fe80537b1bf37871a`.
- Toolchain: official Lean 4.34.1, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`; Lake 5.0.0-src+5045d00.
- Pinned mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- `python3 tools/quality/proof_proxy_staged_gate.py`: PASS, including the
  installed pre-commit hook. QA independently passed the path-scoped check.
- Placeholder scan: no `sorry`, `admit`, custom axioms, `unsafe`, or `True`
  substitutes in the new theorem modules.
- `semantic_vacuity_gate.py` on the three theorem modules: no errors; one
  `trivial_surface` warning for `product_isHermitian_iff`. Classified as a
  legitimate short proof of the explicitly stated Hermitian-product equivalence.
- `python3 tools/run_locked_lake_build.py InfoGeometry.Quantum.KrausBoundaryAudit`:
  exit 2, refusing a concurrent build because the shared lock was occupied.
- The narrow file checker waited on that same lock for over 40 minutes without
  starting compilation. Its queued wait was cancelled with exit 130; the
  competing compiler and lock were left untouched.
- `KrausBoundaryAudit.lean` contains `#print axioms` for all 24 new theorem
  declarations. It has **not executed**; no axiom footprint is certified.
- The SOP's `tools/scripts/vacuity-linter.py` is absent; the available repository
  semantic-vacuity gate was used. The all-theorem axiom probe is the prepared
  fallback for the root-Lake-dependent axiom indexer.

GitHub CI also stopped before checking these theorems. In
[run 40522188126](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40522188126),
the baseline job failed path-dependency validation: Atlas was missing/untracked
and the GIFT gitlink was uninitialized. In
[run 40522188083](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40522188083),
the style job stopped at the existing case collision between
`Canonical/KRDualityCascade.lean` and `Canonical/KrDualityCascade.lean`.
These results are not evidence of theorem compilation.

QA source SHA-256 values (theorem sources unchanged by this record):

| File under `lean/InfoGeometry/Quantum/` | SHA-256 |
| --- | --- |
| `KrausBoundaryDuality.lean` | `8d3905c3777ccd647d63d47fbbf7073564598709f052085eb7165fe0d030cae7` |
| `PositiveBoundaryConditioning.lean` | `f0f66a956fafc68ea84f94d768d0e473af97e9ab06f0fa7eddb13a2eae4ec550` |
| `KrausInvariantGeometry.lean` | `f6eae329022e13bdb61f39627ebf9e199bd827802e49f72d0dc112c4a9da75fb` |
| `KrausBoundaryAudit.lean` | `e8b1a06d9b359e8c1fe6c999dc75c449fb339d0438ed8d649d4a586410d1fc42` |

Remaining acceptance obligations: compile the owner dependencies and all new
modules against the pinned toolchain, repair any elaboration errors, execute
the complete axiom probe, and obtain independent QA acceptance. Keep the PR
in draft status until those obligations are met.
