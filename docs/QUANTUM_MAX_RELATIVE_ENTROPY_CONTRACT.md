# Quantum max-relative entropy: theorem contract

## Frozen intake and scope

Source: Roberto Rubboli, Bartosz Regula, Mario Berta, Ludovico Lami and Marco
Tomamichel, *Entropic measures of quantum information*, arXiv:2611.08254v1,
5 November 2026. The supplied 84-page PDF has SHA-256
`fb2d0a2f51c848e662f8090f91d0a97181335f16345c5faf5d6ec0174334f5fb`.
Equation (150) and its following measurement-effect paragraph on printed page
32 are the implementation target. The page was checked in a rendered image.

Base: `nickgou-nuke/info-geometry-lean` main
`08c34e03f610b452e03422037949196dc7d92d6d`. Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged.

This contribution constructs the operator-domination definition of max-relative
entropy. It is not a formalization of the review's complete entropy hierarchy.
The generic order argument is instantiated on full complex matrices with the
native `MatrixOrder` Loewner order. No diagonal or commuting reduction is used.

## Exact carrier, operations and conventions

- The domination factor is the complete-lattice infimum in `ENNReal` of the
  strictly positive finite coefficients `c : NNReal` satisfying
  `rho ≤ (c : Real) • sigma`. Empty feasibility therefore has value infinity.
- Max-relative entropy is `ENNReal.log` of this factor, with values in `EReal`.
  The logarithm is natural: numerical values are in nats. A zero factor gives
  negative infinity, and an infinite factor gives positive infinity.
- The generic data-processing theorem uses an actual real-linear monotone map;
  it proves contraction of the infimum from transported feasible inequalities.
  It does not store the desired data-processing conclusion in a structure.
- Matrix specialization uses the already constructed complex-linear Kraus map,
  restricted to real scalars where needed. Kraus completeness is needed for
  normalized output states, not for transport of domination itself.
- Measurement effects are full matrices `E` with `0 ≤ E` and `E ≤ 1` in
  Loewner order. Their Born pairings use the ordered product and actual matrix
  trace. `ComplexOrder` keeps the trace's realness condition explicit.

## Existing owners and the missing implications

`Quantum.Choi.krausMap`, `Quantum.Choi.krausMap_posSemidef`, and
`Quantum.Choi.trace_krausMap_pairing` already construct the matrix operation,
positivity, and trace duality. `Quantum.BoundaryConditioning.trace_pairing_nonneg`
and `Quantum.BoundaryConditioning.krausMap_monotone` already own positivity of
the noncommutative trace pairing and Loewner monotonicity.

`OperatorAlgebra.NoncommutativeRenyi` already owns the CFC Petz, sandwiched and
Umegaki kernels. These are reused as neighboring infrastructure, not duplicated
or misreported as support-aware extended divergences with channel DPI.

A bounded repository search covered the canonical Lean filename inventory and
alternate content formulations of Dmax, domination gauges, trace tests and
measurement effects. It found commutative fold-capacity Dmax owners, but no
full-matrix Loewner domination factor or converse all-effects separation theorem.
This is bounded search evidence, not a claim about every ignored artifact.

The smallest substantive new implications are:

1. Feasible-factor transport implies contraction of the extended infimum and
   hence of its extended logarithm.
2. Trace tests against all positive operators recover Loewner order.
3. Normalized native rank-one projections reduce those tests to effects.
4. A positive effect that vanishes on `sigma` and is positive on `rho` obstructs
   every finite domination coefficient, forcing infinite max-relative entropy.

## Planned public statements

- Feasible upper bounds; positive infinity iff no positive finite coefficient is
  feasible; finite factor (and divergence strictly below positive infinity) iff
  such a coefficient exists. Two-sided divergence finiteness additionally uses
  the normalized-input lower bound; general inputs can have negative infinity.
- Monotonicity in the first argument; positive-linear-map data processing.
- A normalized monotone linear functional gives factor at least one, entropy
  nonnegative, and self entropy zero.
- Hermitian full matrices are ordered iff all PSD trace tests are ordered, and
  iff all measurement-effect trace tests are ordered.
- Existing Kraus maps satisfy max-relative entropy DPI; completeness preserves
  the trace-one hypotheses of the normalized corollaries.
- A concrete noncommuting qubit pair and support-separating effect use the
  existing Bloch density-matrix owner. Positivity, trace one, noncommutation,
  effect bounds, the two Born weights, and infinite divergence are explicit
  candidate theorem statements.

Statements remain candidates until the native compiler and declaration-axiom
audit run. Final review records the exact accepted statement set and evidence.

## Dependency order

Native PSD and trace laws precede positive trace pairing. Positive trace pairing
and native rank-one probes imply measurement separation. Native order and
linear maps independently give feasible-factor transport and infimum DPI.
Existing Kraus positivity supplies the matrix consumer. Measurement separation
then supplies finite-factor obstructions. These are mathematical dependencies;
paper section order and conceptual similarity do not create additional edges.

## Boundaries and open debt

No claim is made here about the inverse-on-support operator-norm equality in
the second part of (150), tensor additivity, the full converse support criterion,
the measured/prepared supremum or infimum constructions, Umegaki DPI, recovery
theorems, smooth entropies, infinite-dimensional extensions, or operational
asymptotics. The paper itself conditions the support-inverse formula on finiteness.

In particular, an equality of two extended divergences at infinity cannot by
itself justify a finite-domain equality characterization such as commutation or
recoverability. The claim ledger records such domain requirements separately.

## Independent acceptance

Root integrates the generic owner and concrete consumer. A separate candidate
author supplies the effect-order owner. The paper-audit agent performs semantic
A-A review; the repository-survey agent performs independent acceptance QA.
All builds, tests and gates remain serialized through maintained repository
wrappers and the shared build lock. Source scans, native compilation, the
declaration-axiom audit and root-package coverage are recorded separately.
Permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
