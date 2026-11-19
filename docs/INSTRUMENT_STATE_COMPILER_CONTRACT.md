# Instrument state compiler: theorem contract

**Fresh restoration — 17 November 2026.** This contract is reconstructed from
the retained task scope and the recovered owner sources. It is not a recovered
copy of the lost document and does not certify a native run. Compilation,
declaration axiom auditing and independent final acceptance remain pending.

## Inputs and scope

The original task supplied three mathematical streams concerning cyclotomic
operators, finite dyadic matrix stages, quantum instruments and GNS states.
The selected contribution consists of five focused owners, with a restoration
target of **47 public theorems and 13 public definitions**. Three private
GNS instance-family abbreviations and two local instances are counted separately.
No source claim about the entire streams follows from this finite selection.

| Owner | Contract |
|---|---|
| `InfoGeometry.Algebra.MatrixAlgebraDivisibility` | Actual unital matrix-algebra representations force dimension divisibility. |
| `InfoGeometry.Quantum.KrausCommutatorGeometry` | Fixed-observable hypotheses are connected to actual ordered Kraus commutators. |
| `InfoGeometry.Quantum.KrausFixedEffectCounterexample` | A concrete fixed positive qutrit effect lies outside the common Kraus commutant. |
| `InfoGeometry.Quantum.InstrumentHistory` | Complete time-dependent instruments construct compatible finite pointer states. |
| `InfoGeometry.Canonical.InstrumentHistoryGNS` | That constructed family instantiates the existing represented GNS state and a full-stage uniqueness theorem. |

## Algebraic representation contract

For a characteristic-zero field `K`, a finite-dimensional `K`-module `V`,
a finite index type `n`, a unital algebra homomorphism
`ρ : Matrix n n K →ₐ[K] Module.End K V`, and `i : n`, establish
`finrank K V = card n * finrank K (range (ρ (Matrix.single i i 1)))`.
The proof must use actual matrix units and algebraic projection trace;
self-adjointness of their images is not assumed.
For a nonempty finite source index type, deduce that a unital map
`Matrix n n K →ₐ[K] Matrix m m K` forces `card n ∣ card m`.
A prime divisor other than two excludes maps into every finite `2^k` stage;
the `12` and `24` instances use the prime `3`.
No converse construction or obstruction in a completion/weak closure is claimed.

## Kraus operator contract

Use the existing `Choi.krausMap` and the genuine complex matrix product.
Write the backward map as `Φ(X) = ∑ i, Kᵢ† X Kᵢ`.
The normalization `∑ i, Kᵢ† Kᵢ = 1` makes this backward map unital.
The additional normalization `∑ i, Kᵢ Kᵢ† = 1` supplies its trace preservation.
The commutator-energy argument must retain the products
`(X Kᵢ - Kᵢ X)† (X Kᵢ - Kᵢ X)` on the full matrix carrier.
For arbitrary `X`, prove that fixedness of `X` and `X†X` is equivalent to
commutation with every `Kᵢ`. For self-adjoint `E`, fixedness and either
`E²=E` or `E²=aE+bI` supply the square premise. Under both normalizations,
prove `Φ(X)=X` if and only if `X` commutes with every `Kᵢ`, for arbitrary `X`.
Fixedness of a general positive effect alone is not a commutation premise.

The explicit witness is on `Matrix (Fin 3) (Fin 3) ℂ`:
`K = [E₀₀, E₁₁, (3/5)E₀₂, (4/5)E₁₂]` and
`E = diag(0, 1, 16/25)`. Require positivity of `E` and `1-E`, completeness,
`Φ(E)=E`, and a nonzero ordered commutator. Also record failure of opposite
completeness and of `Φ(E²)=E²`. No generic fixed-point theorem is weakened
to accommodate this witness.

## History and GNS contract

The detailed hypotheses and normalization are in
`INSTRUMENT_HISTORY_CONTRACT.md`. The finite history density is the explicitly
selected diagonal matrix of actual branch traces, evaluated on every full
matrix observable. Completeness must prove compatibility; a compatible family
must not be assumed in place of constructing it. The existing filtered GNS
construction is instantiated on native `CStarMatrix` carriers. Uniqueness
requires agreement on the entire specified stage functional family, on the
same represented norm closure. Outcome probabilities alone are insufficient.

## Acceptance boundary

Preserve the recorded Lean/Mathlib pins and all maintained gates. Freeze the
final source snapshot, obtain independent mathematical review, then run fresh
native elaboration and all-declaration axiom auditing, with zero new-owner
warnings and only `propext`, `Classical.choice`, `Quot.sound` permitted.
Record strict source checks, static Gate4 and actual hook outcomes separately.
The root path-dependency preflight and required publication gate retain their
own status; a scoped native pass does not certify root integration.
