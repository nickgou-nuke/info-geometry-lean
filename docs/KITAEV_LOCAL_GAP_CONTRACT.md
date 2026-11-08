# Kitaev local-gap intake: operator contracts and proof boundaries

## Provenance and baseline

Input: `Pasted text(20261108-014520).txt`, received 2026-11-08, 30,764 bytes.
SHA-256: `d783ef4d978f37238511f0f68e605dad01fb9b83b47e18d844c2dfbdcaff0556`.
The original bytes and its single Lean block were frozen before implementation.
The supplied block advertises a complete seven-node classification but declares
four named theorems and a helper lemma. The exact submitted block was checked with Lean 4.34.1 and
`-DwarningAsError=true`: exit 1. Diagnostics include unused simp arguments and
a parser error at the semicolon-separated `Block2` fields, followed by missing
field errors. Repairing that syntax alone would not supply the stronger
operator, topological, or classification claims advertised in the prose.

Implementation baseline: upstream `main` at
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`, on the independent branch
`codex/kitaev-local-gap-rotor`. This task does not depend on PRs #297 or #299.
Lean and Mathlib pins remain those in the baseline repository.

The supplied lecture timecodes are attribution in the input, not verified
transcript evidence. Primary background sources include Kitaev's
[Periodic table for topological insulators and superconductors](https://arxiv.org/abs/0901.2686)
and the [2025 CMSA/MPIM workshop program](https://cmsa.fas.harvard.edu/event/mpqft25/).
These are background references, not substitutes for Lean proofs and not
verification of the attachment's particular lecture title or timestamps.

## Claim ledger

| Input claim | Exact disposition / intended native target |
| --- | --- |
| Annihilation by a convex combination proves a contractible gapped Hamiltonian fiber | Annihilation alone is insufficient. Construct an actual set of symmetric bounded real operators with a fixed kernel subspace and an explicit quadratic lower bound; prove nonemptiness, convexity and native `ContractibleSpace`. |
| This identifies the full phase space with projective infinity or an Eilenberg--Mac Lane space | Open here: no ground-state quotient, stabilization, classifying-space equivalence, or Eilenberg--Mac Lane construction follows from fiber convexity alone. |
| A scalar polynomial identity proves the operator centered-norm gap criterion | Replace it with an actual operator-norm/Loewner-interval equivalence for symmetric bounded operators, using native Rayleigh quotient results. |
| Square-first and truncate-first differ by a collar return | Reuse the existing ordered Peirce compression defect, then prove the skew-adjoint Gram factorization, positivity, exact C-star norm and zero-transfer criterion. |
| The return term is always nonzero | False without a transfer hypothesis. The zero-defect criterion must be proved and a nonzero example supplied. |
| The collar term universally heals an artificial boundary | No such general physical statement is inferred from the identity. Construct coordinate-projection sums, finite-propagation bounds, and an explicit finite skew-matrix example. |
| The doubled operator universally anticommutes with a fixed decoupler | Construct this on native full block matrices and prove all multiplication identities without assuming commutation of the input operator with other operators. |
| The polynomial rotor expression is already a homotopy | Construct real sine/cosine coefficients, continuity, endpoints and a genuine native `Path` in the normalized skew-matrix subtype. |
| Every original spectral interval is preserved by the rotor | False unless the interval contains the endpoint value 1. Prove bounds enlarged to `min(lower,1)` and `max(upper,1)`, with original-interval preservation under the extra endpoint condition. |
| Reassociating three `A0-A0` terms constructs a dimer suspension and its inverse | Not accepted: additive cancellation constructs neither a lattice shift, a map into a loop space, nor inverse homotopies. |
| The finite formulas prove `A_d ≃ Ω A_(d+1) ≃ KO_(d-2)` | Open here: no phase-space spectrum, locality-controlled suspension/restriction maps, or KO classification is supplied by those formulas. |
| A local-to-global bound has error `O(r²/R²)` | Open here: this requires quantitative localization/partition estimates, with constants and domains, beyond the finite-propagation identity. |

## Fixed-ground Hamiltonian fiber

Carrier: native bounded real operators `E →L[ℝ] E` on an appropriate real
inner product space, a native orthogonally complemented submodule `K`, and its
orthogonal projection `P_K`. The implemented fiber consists of operators `H` with:

1. native symmetry;
2. `H x = 0` for `x ∈ K`;
3. `δ * ‖x - P_K x‖² ≤ inner ℝ x (H x)` for every `x`.

Construct the member `δ • (1 - P_K)` and prove the fiber convex under real
convex coefficients. Native `Convex.contractibleSpace` then supplies actual
topological contractibility of this subtype. For `δ ≥ 0`, prove positivity;
for `δ > 0`, prove `ker H = K`. No commutation between two Hamiltonians is
assumed. The case `K = ⊤` is allowed; this does not assert a nonempty excited
spectrum. Existing owner inspected: `Analysis.RealPositiveOperatorGap`.
Native interfaces include `Submodule.starProjection`, positive/symmetric
continuous linear maps and the topology of convex subsets.

## Operator gap centering and corrected interpolation interval

For a symmetric bounded real operator `Q` and real `a ≤ b`, the proved
operator statement is

```
‖Q - ((a+b)/2) • I‖ ≤ (b-a)/2  ↔  a • I ≤ Q ∧ Q ≤ b • I.
```

The norm is the bounded-operator norm and the order is the native operator
order, with quadratic-form equivalents. No entrywise matrix norm is silently
substituted. For `0 ≤ u ≤ 1`, derive

```
min a 1 • I ≤ u • Q + (1-u) • I ≤ max b 1 • I.
```

If `a ≤ 1 ≤ b`, the original bounds are preserved. Native owners include the
Rayleigh-quotient characterization of the real symmetric operator norm and
positive-operator order.

## Square-first compression and finite locality

Existing authoritative owners:

- `Core.PeirceCompressionDefect.compression_adjoint_mul_defect`;
- `Core.PeirceCompressionDefect.compression_square_defect`;
- `Core.PeirceCompressionCStar.norm_compression_adjoint_square_defect`;
- `Core.PeirceCompressionCStar.compression_adjoint_square_eq_iff`.

For `p²=p=p*` and `a*=-a`, preserve the exact ordered identity

```
p * (-(a*a)) * p + (p*a*p) * (p*a*p)
  = star ((1-p)*a*p) * ((1-p)*a*p).
```

Prove native matrix positive semidefiniteness and the C-star norm/zero-transfer
corollaries on their actual respective carriers. For a coordinate subset,
construct its native diagonal matrix projection and derive the exterior-index
sum without exchanging coefficient multiplication order. For metric-indexed
finite matrices, prove propagation of a product is at most the sum of the
input propagation bounds, hence a square has propagation at most `2r`, and
prove disappearance of collar contributions sufficiently far inside.

A full real three-by-three example uses a skew two-site block and a third
zero mode. It must prove a nonzero vector in the global kernel, a square-first
unit compression at a rank-one coordinate projection, zero truncated first
operator, nonzero collar Gram, and actual `p*a ≠ a*p`. These are finite-matrix
facts, not a graphene/Ising bulk-boundary classification.

## Native doubled rotor and actual paths

Carrier: `Matrix (n ⊕ n) (n ⊕ n) ℝ`, constructed with native `Matrix.fromBlocks`.
Define

```
X(A) = [[0,A],[A,0]],   Y = [[0,I],[-I,0]],   D(A) = diag(A,-A).
```

Prove universal anticommutation, `Y²=-I`, `X(A)²=diag(A²,A²)`, skew-transpose
closure, and the unnormalized weighted-square identity by reusing
`Algebra.AnticommutingBalance.weighted_square`.

For `Aᵀ=-A` and `A²=-I`, construct native sine/cosine `Path` objects in
`{M | Mᵀ=-M ∧ M*M=-1}` with exact endpoints from `D(A)` or `X(A)` to `Y`.
The direct `D(A)` path uses its actual anticommutation with `Y`; no homotopy
is inferred merely from a change of basis. Construct normalized block Hadamard
orthogonality and its actual conjugation `H D(A) H = X(A)`. Include full-matrix
noncommutativity and the unnormalized endpoint counterexample (`-A²=4I`
initially, endpoint `-Y²=I`).

Existing related owners inspected include `Canonical.KitaevRotorMatrix`
(a different CAR boundary polynomial construction) and
`OperatorAlgebra.RealDoubledChiralKreinHadamard` (functional doubled-space
maps). Their names alone do not establish this matrix path. Existing Clifford
stabilization or `Quantum.RealKCategory` constructions are not treated as an
Omega-spectrum equivalence without an actual corresponding owner theorem.

## Implemented owners

| Native owner | Exact additional result |
| --- | --- |
| [`Analysis.FixedGroundHamiltonianFiber`](../lean/InfoGeometry/Analysis/FixedGroundHamiltonianFiber.lean) | Actual convex, nonempty, contractible operator fiber; positivity and exact kernel under the stated bounds. |
| [`Analysis.FixedGroundHamiltonianSpectrum`](../lean/InfoGeometry/Analysis/FixedGroundHamiltonianSpectrum.lean) | In finite dimension, every real spectral value of a fiber member, including every convex interpolation point, is zero or at least `δ > 0`. Reuses `RealPositiveOperatorGap.spectrum_gap_of_coercive_bound` and `ContinuousLinearMap.spectrum_eq`. |
| [`Analysis.RealOperatorGapCentering`](../lean/InfoGeometry/Analysis/RealOperatorGapCentering.lean) | Actual operator-norm / Loewner-interval equivalence and identity-mixture bounds. |
| [`OperatorAlgebra.SkewCompressionGap`](../lean/InfoGeometry/OperatorAlgebra/SkewCompressionGap.lean) | Ordered skew-compression Gram factorization, matrix positivity, exact C-star norm, and zero-defect / zero-transfer / commutation equivalences. |
| [`OperatorAlgebra.FinitePropagationCompression`](../lean/InfoGeometry/OperatorAlgebra/FinitePropagationCompression.lean) | Native coordinate cut, ordered exterior-index sum, propagation addition and interior vanishing. |
| [`OperatorAlgebra.SkewCompressionCounterexample`](../lean/InfoGeometry/OperatorAlgebra/SkewCompressionCounterexample.lean) | Actual real three-by-three skew example, nonzero kernel vector, square-first unit cut, zero first compression, and noncommutativity. |
| [`OperatorAlgebra.KitaevDoubledRotor`](../lean/InfoGeometry/OperatorAlgebra/KitaevDoubledRotor.lean) | Native block algebra, two genuine normalized `Path` constructions, orthogonal Hadamard conjugation, and the unnormalized endpoint counterexample. |

The seven owners are exposed through `InfoGeometry.lean` and
`InfoGeometry/AllExhaustive.lean`. The spectrum theorem is explicitly
finite-dimensional; contractibility and operator-norm centering do not impose
finite dimension. The matrix rotor uses the native finite matrix topology.
No unproved Matrix-to-continuous-operator identification is inserted between
the matrix and analytic branches.

## Dependency order and acceptance

The three mathematical branches have separate premises. Their actual chains
are: Peirce defect → skew Gram → positivity/locality/example; block algebra →
anticommutation → weighted square → normalized native path; orthogonal
projection and quadratic bound → convex nonempty fiber → contractibility and
kernel equality. Operator norm centering yields the corrected interpolation
bounds. There is no inferred edge from these finite/analytic results to a
KO-classifying spectrum.

Generation, semantic audit and acceptance are separate roles. Acceptance must
cover exact selected source compilation with warnings as errors, every owned
declaration including generated constants, separate type/value axiom
inspection, prohibited-proof checks, semantic review, import/export checks,
and the actual maintained Git hooks and root build. Permitted foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is not a promise
of a `[propext]`-only development.

## Integration boundary

The actual root-package build was attempted using the maintained wrapper
`tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail` with all
seven explicit new owners. It exited 1 during package resolution because
`external_refs/homotopy-hypothesis-lean4` is missing. The existing manifest
references this path as `HomotopyHypothesis`; it supplies no source revision
that this task can faithfully reconstruct. Neither dependency pins nor the
root package configuration were changed.

Consequently, selected strict source compilation and the root Lake build have
different outcomes. No successful root-package, default-target, or aggregate
import build is claimed. Publication is for review with this integration
blocker disclosed.

## Independent source verification

Final disposition: **kernel verified, accepted with the stated limited scope**.
Generation, semantic review, and acceptance were performed by separate roles.

- Pinned compiler: **Lean 4.34.1**, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Pinned Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`;
  its eight package pins were also checked.
- The maintained `tools/quality/check_operator_geometry.py` compiled the exact
  selected **11-module source closure** with `-DwarningAsError=true`: seven
  new owners and four unchanged dependencies, all compared against the base
  sources. The isolated acceptance closure did not use generator oleans.
- Initial strict screening identified two implicit tactic-context dependencies.
  The final repair explicitly supplies `hδ` to `nlinarith` and `hab` to
  `linarith`; exact inverse substitutions recover the initially audited bytes.
  All theorem statements are unchanged. The two repaired owners and their
  unchanged spectrum consumer were then independently recompiled and audited.
- The final combined audit covers **136 owned kernel declarations**, including
  **all 136 values**, separate type/value dependencies, private declarations,
  and 33 generated/anonymous declarations. It consists of 22 freshly audited
  constants in the three-module delta and 114 unchanged constants retained
  only after exact source and compiled-artifact hash checks.
- Source inventory: **103 named declarations**, comprising 84 theorems and
  19 definitions, with two private theorems included. The kernel inventory
  contains 117 theorem constants and 19 definitions.
- The only observed foundational axioms are `propext`, `Classical.choice`, and
  `Quot.sound`. No custom axiom, unsafe/partial declaration, `sorry`, `admit`,
  or `native_decide` is introduced.
- Strict OpenGauss screening: **zero violations, exit 0** on all seven final
  owners. Headers and all 14 aggregate import entries passed source checks.
- Semantic-vacuity gate: **zero errors, exit 0**, with the ten retained lexical
  warnings reviewed below. Compiler diagnostics for the checked sources are
  empty; this does not turn the lexical warning count into zero.

The explicit seven-target checker invocation, final source hashes, compiler
and verification-tool hashes, all declaration records, and root-build output
were preserved in the task verification record. Selected source verification
is separate from the failed root package resolution described above.



### Lexical warning review

The maintained semantic-vacuity scanner emits ten nonblocking
`trivial_surface` warnings for the short rotor proofs `offDiagonal_smul`,
`offDiagonal_anticommutes`, `oppositeDouble_anticommutes`,
`offDiagonal_square`, `oppositeDouble_square`, `oppositeDouble_transpose`,
`skewSwap_transpose`, `interpolate_transpose`, `hadamard_transpose`, and
`hadamard_orthogonal`. Each declaration was read together with its native
matrix definition and downstream consumers. They compute actual block
products, transpose/scalar compatibility, skew closure, or both Hadamard
orthogonality equations. The proof bodies reuse native matrix laws and the
previously proved square equation; they do not assume the conclusion.
They are accepted substantive intermediate results. The scanner finding is
retained rather than reported as zero warnings or suppressed by a gate change.
