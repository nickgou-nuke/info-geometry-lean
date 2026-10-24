# Hyperbolic Peirce extension: contract and verification

The incoming Stream 6 formula must use `Q = d+B` as its boost generator.
The supported sandwich has cross term `-uv • (d-B)`. Using `J=d-B`
with the same proposed inverse does not satisfy the hyperbolic inverse law.

The current shared owner `Canonical/PeirceHyperbolicOrbit.lean` already
constructs the general moving idempotent through `pairMatrixLinear`, with
expansion, idempotence, displacement square, and supported boost sandwich.
The existing `PeirceRotorAction` remains the elliptic owner. The planned
bridge preserves these carriers, completes the boost by `1-support` to an
ambient unit, and identifies diagonal elliptic compression with the existing
`UnifiedGeometryOperatorSignificance.kmsModularWeight s c` (in that order).
No spacetime signature, positive state, analytic KMS dynamics, geodesic, or
loxodromic classification follows from these ring identities alone.

## Parameter and generator boundary

`Canonical/HyperbolicParameterBoundary.lean` proves the exact integral
classification `u*u-v*v=1 ↔ (u=1 ∨ u=-1) ∧ v=0`. Thus integral parameters
cannot witness a nontrivial normalized boost. Actual noncommuting rational
2×2 matrices at `(u,v)=(5/3,4/3)` provide a two-sided boost inverse, a
nontrivial conjugated idempotent, and displacement square `(-16/9) • 1`.
They also refute the proposed inverse for the elliptic generator; this is
not a claim that the elliptic candidate has no inverse at all.

Parent locked session 81718 passed, 8,924 jobs, exit 0, log
`/tmp/hyperbolic-parameter-boundary.log`. Three stylistic linter warnings
were subsequently repaired without changing statements. The new companion
audit requests eight axiom reports and compiles two API examples.
Semantic review passed and the original owner passed strict screening.
Independent kernel QA session 64735 passed (8,925 jobs, exit 0), with eight
standard-three-axiom reports, two examples, zero source warnings, and zero
traps. Evidence: `/tmp/hyperbolic-parameter-boundary-qa.log`. This boundary
module is accepted with the stated limited algebraic scope.

The shared worktree now also contains `PeirceMatrixUnitCompletion.hyperbolicUnit`
and its ambient conjugation theorem, plus `RotorPeirceWeightCompression`.
Their source inspection closes the implementation-discovery questions above;
the boundary-module QA does not certify those separate owners.

## Independent next counterexample work

The `NonIsoConf3LogWedgeObstruction` full numerator classification remains
in progress. Independent semantic review confirms that, assuming the second
displacement has nonzero quadric, vanishing of every ambient numerator
coefficient is equivalent to vanishing displacement minors. The future
statement must retain all ambient coordinate pairs and must not confuse the
polynomial numerator with logarithmic forms without nonzero denominators.
