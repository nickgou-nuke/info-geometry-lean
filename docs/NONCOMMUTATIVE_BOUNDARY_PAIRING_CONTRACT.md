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

Independent semantic review requested before coding; separate acceptance review
will check the final source and raw verification evidence. Verification status
is pending until commands and axiom footprints are recorded below.
