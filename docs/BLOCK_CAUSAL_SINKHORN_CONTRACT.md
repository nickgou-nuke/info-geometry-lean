# Block-causal log-Sinkhorn: source contract and limits

## Input and provenance

Based on the supplied `BlockCausalSinkhornAudit.lean` text dated 23 October 2026.
Inspected repository base: `ecccb38da69539e1ced7172f6d44cb1da0d97291`.
No existing owner or dependency pin is modified. The uploaded source is not
asserted to compile unchanged. Four focused modules separate its dependencies.

## Theorem dependency order

1. Finite real prefix log-partitions give positive denominators, nonnegative
   normalized weights, and zero future support.
2. Agreement on the entire prefix implies equality of weighted prefix sums.
3. Fixed finite log-Sinkhorn iterations act on latent indices only. Their final
   columns are exactly the existing `FiniteSoftmax.weight` at temperature one;
   its existing normalization theorem is reused.
4. The current-chunk score, both gains, finite core, and raw output agree for
   all inputs with the same prefix, for any fixed local solver function.
5. The future-input slice is constant. Native `HasFDerivAt` gives its zero
   derivative and zero pullback for any fixed continuous linear covector.
6. Pointwise encoders specialize this result to the actual pipeline on raw
   normed chunk inputs. Simultaneous replacement of the whole future suffix
   also has zero derivative.

## Readout fidelity

The supplied `blockCausalSinkhornChunkOutput` multiplies the calibrated detector
matrix by the solver output. It does not divide each detector row by its mass.
That raw definition is retained. The separate `normalizedChunkOutput` divides
by `detectorMass`; its explicit responsibility-sum formula, prefix invariance,
and encoded zero-derivative theorem are additional results, not silent edits
to the source's semantics. Positive detector responses and a nonempty channel
set imply positive mass. A nonzero mass suffices for sum-one normalization.

## Boundaries

- Chunk summaries have finite real entries. Empty/all-masked chunks represented
  by minus infinity are not in this carrier.
- The chunk index is causal; tokens within the current chunk can interact.
  There is no claim of strict token causality for chunks of length greater than
  one.
- Parameters, iteration count, solver, encoder family, and output covector are
  fixed. No future-dependent shared statistics, global stopping criterion, or
  retraining operation is included.
- The finite loop proves exact column sums after a column update, not exact row
  sums or membership in the Birkhoff polytope after a prescribed finite count.
- The trifactor equality holds even at zero iterations. It is separate from
  convergence and numerical residual estimates.
- `Psi` is a pure, fixed local map. No Poisson inverse, positivity, connectivity,
  conditioning, or solver correctness follows from its function type.
- Constant future slices need no differentiability of the full nonlinear
  pipeline, encoder, or solver. No claim of differentiability in past inputs
  or trainable parameters follows.
- A real Fréchet theorem is not a verified implementation of floating-point
  Autograd. Finite negative mask sentinels are not exact mathematical zero
  masks for unrestricted logits. Dropout/stateful execution needs its own
  fixed-randomness and state-locality contract.

## Verification

The scoped workflow compiles unchanged full repository dependencies and the
four new modules against the exact Mathlib and Lean pins. It reuses the source
closure resolver from `check_reviewed_prs.py`, retains its native combined-
environment enumeration and foundational-axiom allowlist, and invokes the
public `Lean.collectAxioms` API in Lean 4.34.1. The older audit helper accesses
collector internals that are no longer exported; the new runner does not rely
on them. The audit rejects nonstandard transitive axioms, unsafe or partial
declarations, including generated declarations visible in the imported environment. It does not invoke the root Lake package, strip unresolved
imports, modify dependencies, or delete caches. Its saved report, not this
text, is the verification evidence. No training loop is changed.
