# Clifford–Peirce–Walsh verification results

## Scoped independent acceptance

The final mathematical owners and focused infrastructure changes received
**ACCEPTED_WITH_LIMITED_SCOPE** from the independent QA agent on 2026-11-12.
The checked source changes are based on
`a392af178af1fe2bcba2ba39eb405700c6ee103c`; their exact content identities are
recorded in [SOURCE_SHA256.json](SOURCE_SHA256.json).

The immutable [QA_RECEIPT.json](QA_RECEIPT.json) has SHA256
`dd0d27a7fe71ec2d81537e84d40943604dcbc800ee35eb88e18509150a5adceb`.
It contains the observed commands, exit codes, source-review and evidence
hashes, diagnostics, dependency revisions, and acceptance boundaries. Its
local `tmp/` paths identify the original execution evidence, not additional
files required by the reproduction commands below.

## Native Lean and axiom checks

Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` were used. The pinned compiler was
checked directly, and all nine selected dependency checkouts matched the
root manifest with clean tracked sources before and after verification.

The selected aggregate build completed successfully (3,106 Lake jobs),
followed by direct elaboration of both new owners and a fresh byte-identical
copy of the declaration audit. Every command and the outer launcher exited
with status 0. The aggregate audit and fresh audit agreed:

| Audited owner | Declarations |
|---|---:|
| `InfoGeometry.Clifford.OperatorValuedJonesWalsh` | 53 |
| `InfoGeometry.OperatorAlgebra.StarSymplecticSqueeze` | 45 |
| `InfoGeometry.Clifford.OperatorValuedJones` | 54 |
| `InfoGeometry.Algebra.IdempotentProjector` | 35 |
| `InfoGeometry.Geometry.AssociativeGaugeConnection` | 28 |
| `InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms` | 46 |
| **Total** | **261** |

Of these, **202 are theorem declarations, including generated/private
entries**. The audit checks actual originating modules, rejects introduced
axioms and unsafe/partial owner declarations, and collects transitive axiom
dependencies for every selected declaration. The observed axiom set was
exactly `propext`, `Classical.choice`, and `Quot.sound`.

Both new owners and the fresh audit produced **zero direct-compilation
warnings**. The aggregate retained four inherited lint warnings: an unused
simp argument in `OperatorValuedJones`, an unnecessary tactic-sequencing
operator in `Core.PeirceDecomposition`, and two unused section-variable
warnings in `AssociativeGaugeConnection`. The receipt preserves their exact
locations and messages.

## Source and infrastructure checks

Independent mathematical source review and the later audit-scope review
passed. Separate source reviews passed for the selected-package gate route
and pre-push consistency guards. The new theorem owners remained byte-identical
through the scope adjustment and final native checks.

Strict screening, strict refutation, static Gate 4, and the semantic-vacuity
gate passed. The static Gate 4 results are separate from native elaboration;
they reported zero proof holes, traps, and scope warnings. Two heuristic
advisories in `StarSymplecticSqueeze` remain recorded: simplification of
required zero/unit structure fields, and parameter use through unfolding in
`squeeze_mul`. Independent review found no mathematical defect in either case.

A second maintained build-lock lease ran separate Bash syntax checks for
`scripts/quality/post_build_gate.sh` and `.githooks/pre-push`, then the two
focused regression suites:

| Regression suite | Observed result |
|---|---:|
| `test_clifford_peirce_walsh_gate_routing.py` | 7 passed |
| `test_pre_push_ref_range.py` | 25 passed |
| **Total** | **32 passed** |

These tests exercise temporary Git repositories and command-recorder fixtures.
They verify routing, failure propagation, ref ranges, and committed-source
guards; they do not simulate Lean acceptance or certify a real publication.

The native phase protected 47 inputs across 28 fingerprint checkpoints; the
infrastructure phase protected 49 inputs across 10 checkpoints. All comparisons
matched, including the final independent reread.

## Scope and earlier interruption

This receipt covers the declared arbitrary-ring algebra, six complete owner
modules, and the tested infrastructure behavior. `All.lean` received source
checks; a whole-root umbrella build, unrelated optional dependencies, actual
publication gates, and remote CI are outside this receipt. Those publication
checks have their own outcomes and cannot be inferred from this acceptance.

The broader `PeirceParityClosure` and `PeirceParityTorsion` modules are
source-reviewed prior art. An earlier attempt importing that broader chain
was interrupted during dependency compilation and is archived as inconclusive.
No aggregate-build or axiom-audit success is attributed to it. The final
six-owner target retains every new declaration and directly includes the
Peirce-corner owner used by the construction.

The [theorem contract](../../docs/CLIFFORD_PEIRCE_WALSH_CONTRACT.md) states
the mathematical hypotheses and boundaries. Analytic transforms, physical
positivity, tensor identifications, and quadratic signatures require separate
constructions.

## Reproduction

From an independent checkout with the pinned prerequisites in
[README.md](README.md), run sequentially:

```bash
python3 verification/clifford-peirce-walsh/check.py
python3 verification/clifford-peirce-walsh/check.py env lean "$PWD/lean/InfoGeometry/Clifford/OperatorValuedJonesWalsh.lean"
python3 verification/clifford-peirce-walsh/check.py env lean "$PWD/lean/InfoGeometry/OperatorAlgebra/StarSymplecticSqueeze.lean"
python3 verification/clifford-peirce-walsh/check.py env lean "$PWD/lean/InfoGeometry/Canonical/CliffordPeirceWalshAudit.lean"
python3 verification/clifford-peirce-walsh/check.py env python3 -m unittest discover -s tests/quality -p test_clifford_peirce_walsh_gate_routing.py -v
python3 verification/clifford-peirce-walsh/check.py env python3 -m unittest discover -s tests/quality -p test_pre_push_ref_range.py -v
```

Build first when source dependencies have changed. The direct `env lean`
commands elaborate the named file against the available imported artifacts.
The maintained wrapper verifies pins and serializes execution through the
repository's shared build lock.
