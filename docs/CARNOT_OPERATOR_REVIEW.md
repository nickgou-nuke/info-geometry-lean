# Replacement thermal relaxation: review and validation

Date: 2026-11-18. Scope: the three selected canonical owners and their repository
import closure. This record does not certify all historical files or a complete
thermodynamic engine.

## Owners and roles

| Owner | New construction or result |
| --- | --- |
| `Quantum/ReplacementRelaxation.lean` | Existing replacement projection; full matrix relaxation family; composition and centered action; fixed-target return obstruction; positivity at every finite amplification; exponential time path and actual derivative. |
| `Quantum/ReplacementHamiltonian.lean` | Exact ordered derivation defects; stationary-target covariance; radial/star-trace orthogonality; combined linear generator; trace-energy readouts and finite control bookkeeping. |
| `Quantum/ReplacementGibbs.lean` | Actual CFC Gibbs target; skew generator `(-Complex.I) • H`; stationarity, covariance, radial pairing, and energy readouts. |

Generation and independent review used separate agents. The parent integrated
the candidates and runs decisive compiler/audit checks. Review read the actual
replacement, ancillary amplification, inner-derivation, cyclic trace,
functional-calculus Gibbs, normalized-density, and matrix-entropy owners.
The derivative API and its scalar conventions were also checked directly in
the pinned Mathlib source.

The coefficient carrier is complex matrices because the existing positive
channel and CFC Gibbs constructions use it. Rate, time, and physical convex
parameters are real. No associative binary representation of octonions,
Krein-to-positive identification, or real/internal-complex equivalence is
asserted by these files.

## Independent semantic disposition

PASS at source-review level, with finite/conditional/analytic scopes recorded
in `CARNOT_OPERATOR_CONTRACT.md`. The review explicitly checked:

- Noncommutative multiplication order and both commutator defect signs.
- Normalization as a separate condition from positive semidefiniteness.
- Arbitrary finite ancilla types in complete positivity.
- Actual differentiation of the matrix path, with normalization needed to
  express the derivative through the current-state generator.
- Hermitian Hamiltonian and its physical `-I` factor.
- No assumption that the input density commutes with the Hamiltonian.
- Open bath energy exchange retained in the formula.
- No universal system-entropy increase or closed GENERIC conclusion.
- Real finite-step energy parameter, trace-one input, and the entropy-unit
  convention in the explanatory Carnot ledger.

## Reproducible compiler surface

Pinned environment:

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Official Lean archive SHA-256:
  `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.

Use the maintained scoped checker with the pinned executable and Mathlib clone:

~~~bash
python3 -u tools/quality/check_clifford_dirac.py \
  --mathlib-root "$MATHLIB_ROOT" \
  --lean "$LEAN_BIN" \
  --output verification-replacement-thermal \
  --target InfoGeometry.Quantum.ReplacementRelaxation \
  --target InfoGeometry.Quantum.ReplacementHamiltonian \
  --target InfoGeometry.Quantum.ReplacementGibbs
~~~

Despite its historical filename, this maintained checker accepts the explicit
target list, copies each repository dependency from the current source tree,
serializes compilation under the shared build lock, and invokes the native
declaration axiom audit for the selected owners. Acceptance additionally checks
that all three selected owners have zero compiler warnings; the workflow makes
that check explicit.

The discovered closure has 56 repository modules and 51 existing direct Mathlib
roots. CI caches only the pinned runtime and dependency artifacts. It checks
the exact PR source head and uses fresh repository outputs with neither
`--incremental` nor `--skip-audit`.

## Current validation record

- Independent mathematical and documentation review: passed.
- Pinned dependency cache hydration: passed for the discovered union needed by
  this task and the three older proof repairs; no pins changed.
- Strict placeholder scan of all three new owners: passed.
- Warning-strict semantic-vacuity scan: exit 1, four heuristic warnings,
  individually reviewed below; no error-level findings.
- Focused workflow: YAML structure and all three embedded Python scripts
  parsed successfully; target and path coverage checked against the maintained
  closure helper.
- Exact-source kernel compilation and declaration axiom audit: pending.
- Actual staged pre-commit proof gate: passed for the initial draft and the parameter/norm repair.
- Root pre-push gate: queued under the shared build lock, separately from scoped verification.
- First focused CI attempt: inherited dependencies compiled, then the new relaxation
  owner exposed a reserved `λ` parameter and a missing matrix norm instance. The
  repair uses ordinary parameter names and Mathlib's scoped L² operator norm; its
  exact-source kernel result remains pending.
- Whole-root/default-target acceptance: not established.

This section must be updated from observed compiler/hook results before
reporting the contribution as kernel verified.

## Semantic-vacuity warning review

The warning-strict heuristic scan reports four short helper surfaces:

| Declaration | Actual statement | Disposition |
| --- | --- | --- |
| `relaxation_apply` | Evaluation of the newly defined linear map | Definitional API used in the composition, trace, and positivity proofs. |
| `generator_apply` | Evaluation of the combined linear operator | Definitional API used by trace preservation and energy balance. |
| `relaxation_one` | Parameter one yields the identity operator | Endpoint law for the full operator family. |
| `relaxation_of_trace_zero` | Every traceless matrix is scaled by the parameter | Nonempty operator subspace result; no diagonalization assumption. |

These are ordinary helper lemmas, not proof of the stronger thermodynamic
narrative. Their short proofs are retained, and the scan's warning-strict
exit is recorded rather than suppressed or evaded.

## Remaining obligations

A combined Hamiltonian-plus-relaxation trajectory, entropy or relative-entropy
monotonicity, heat-reservoir state, GENERIC degeneracy laws, driven Carnot
strokes/efficiency, reservoir-resolved NESS production, Weyl spacetime gauge,
Gromov–Witten volume, Wilson-loop transport, Goldstone modes, and causal
wavefront dynamics are not established here. The exact next mathematical
requirements are stated in the contract.
