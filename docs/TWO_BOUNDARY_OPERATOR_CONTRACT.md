# Two-boundary operator geometry

## Intake and scope

Base: `cfbcbca21cf57a4614a9646768ba9356cf3cc6b0` on upstream `main`.
The input asks for native Lean/mathlib proofs extracted from prose about two
time boundaries, conjugate sectors, weak readouts and a thermal purification.
The accepted carrier is the full finite complex matrix algebra. No ambient
commutativity, simultaneous diagonalization, scalar proxy, spacetime model or
physical identification is assumed.

The supplied paper is Petit–Margnat–Zejli, *A bimetric cosmological model based
on Andreï Sakharov's twin universe approach*, EPJC 84:1226 (2024),
DOI `10.1140/epjc/s10052-024-13569-w`. Uploaded PDF SHA-256:
`16e3de8f2ca202be018a7629d46ea0d0e77f50278215a71312c193d1fab4c44c`.
It supplies context, not axioms for the finite operator theorems. The exact
two-boundary instrument formula is independently stated in Gammelmark,
Julsgaard and Mølmer, *Past quantum states*, arXiv:1305.0681. Weak readouts
are compared with Aharonov–Vaidman, arXiv:quant-ph/0105101. Thermal
purification is conditional on a chosen Hamiltonian and inverse temperature.

## Existing owners and minimal repairs

- `Quantum.ChoiCompletePositivity` owns `krausMap`.
- `Quantum.KrausBoundaryDuality` owns trace duality and ordered words.
- `Quantum.PositiveBoundaryConditioning` owns PSD trace pairings and the
  Hermiticity obstruction for products of Hermitian matrices.
- `Streaming.FiniteTwoBoundaryWeakFunctional` owns the pure-vector readout.
- `Quantum.FinitePartialTrace` is promoted from the existing `src` owner,
  retaining `FiniteAttentionCanonicalBridges` namespaces and consumers.
- `Canonical.FiniteMatrixGibbsFunctional` owns the full matrix CFC Gibbs weight.
- `OperatorAlgebra.SemilinearSheetGeometry` is promoted from the existing
  `src` owner; its real algebra equivalence conjugates coefficients and
  exchanges both matrix indices.

The canonical real-weighted unitary mixture is renamed to the already
established `src` name, removing its collision with the complex-weighted
owner. This is not a new construction. Ordered words use native `List.foldr`
with explicit definitional nil/cons equations, retaining both chronological
composition and backward pullback. This permits the strict owned-declaration
audit without local recursive execution companions. The unchanged
`KrausInvariantGeometry` consumer is included in the validation closure.
The existing diagonal marginal lemma now reuses the focused partial-trace
identity without its unused positivity and normalization hypotheses; this
strengthens an existing algebraic statement and has no repository callers.

## Exact theorem contracts

Let `ρ,E,A,K` be full complex matrices and `V : o → k → Matrix n n ℂ`.

1. **Instrument weights.** Set
   `w(a) = Re tr(krausMap (V a) ρ * E)` and `Z = ∑ a, w(a)`.
   PSD boundaries imply nonnegative weights. The branch amplitude is
   `sqrt E * V a i * sqrt ρ`; its Gram trace gives the branch weight.
   Positive normalization is equivalent to the existence of a nonzero
   branch amplitude. Under `Z > 0`, the normalized weights sum to one.
   For a trace-one input, an effect bounded by one and a complete instrument,
   the total success weight is at most one.

2. **Disturbance and order.** The exact normalizer defect is
   `Z - Re tr(ρ*E) = Re tr(ρ*(Φ*(E)-E))`. Ordered composition uses
   `W b j * V a i` when `V` acts first. Individual commutation is not inferred
   from vanishing sums or a single state's zero disturbance.

3. **Mixed readout.** Define `W(A) = tr(E*A*ρ)/tr(E*ρ)`. This is complex
   linear. Nonzero overlap gives `W(1)=1`. The representing normalized
   trace weight is `ρ*E/tr(E*ρ)`. For Hermitian boundaries, exchanging
   endpoints and adjointing the probe conjugates the readout. The native
   commutator measures its adjoint defect. At nonzero overlap, the ordered
   weight is Hermitian exactly when the boundaries commute. Native outer products recover the
   existing pure-boundary functional.

4. **Semilinear reversal.** With the existing involution `τ`, simultaneous
   transformation conjugates weak readouts. Reversed instrument weights use
   boundaries `(τ E, τ ρ)` and Kraus operators `τ(star K)`. Reversed trace
   preservation requires original unitality. No trace-one property of `E`
   is implicit.

5. **Purification.** Mathlib's `Matrix.vec` is column-first. The vector
   `vec Sᵀ` has second-factor marginal `S * star S`. Thus `S = sqrt ρ`
   purifies a PSD matrix and a trace-one input yields a normalized rank-one
   PSD idempotent. The doubled generator `H ⊗ 1 - 1 ⊗ Hᵀ` acts by the
   vectorized commutator. Gibbs annihilation is proved from CFC commutation,
   not assumed ambient commutativity.

These are target contracts, not a completion certificate. The final receipt
must identify the declarations actually proved and any target left open.

## Dependency order and acceptance

The mathematical dependency order is extracted from the checked declaration
types and proof values, restricted to the audited owners. It is a partial
order of the chosen Lean proofs, not a causal theory of cosmological events.
Constructor and recursor metadata are excluded from this syntactic type/value
graph; every owned declaration remains subject to the separate safety and
transitive axiom audit.
The canonical and `src` closures require separate artifact directories.
Pins remain Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Acceptance requires complete scoped native compilation, axiom enumeration,
an independent semantic audit and a distinct QA rerun. A scoped result does
not certify the repository's unrelated historical modules or physical claims.

Unclaimed: a cosmological boundary-value solution, entanglement generation,
thermalization, determination of physical constants, a dark-matter prediction,
singularity removal, or equivalence between a direct-sum sector carrier and
a tensor-product purification carrier without an explicit map.
