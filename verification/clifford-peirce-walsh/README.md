# Clifford–Peirce–Walsh validation package

This package builds the canonical repository sources needed for the
operator-valued Jones coordinates and star-symplectic squeeze results, then
audits declarations in six named mathematical owners. Run its maintained
wrapper from the repository root:

```bash
python3 verification/clifford-peirce-walsh/check.py
```

With no arguments, `check.py` selects exactly
`build InfoGeometry.Canonical.CliffordPeirceWalshAudit`. This default comes from
the wrapper; the package's `lean_lib InfoGeometry` declaration is not marked
`@[default_target]`.

## Sources, toolchain, and dependency prerequisites

The [Lake configuration](lakefile.lean) sets `srcDir := "../../lean"`, so the
build reads the canonical files in this checkout rather than copies of their
proofs. Its own build artifacts live under this package's `.lake/build`.
Dependency checkouts and their existing artifacts are reused from the root
`.lake/packages` directory. The configuration sets
`enableArtifactCache := false`.

The selected [toolchain](lean-toolchain) is
`leanprover/lean4:v4.34.1`. It must be byte-identical to the root
[lean-toolchain](../../lean-toolchain). The direct Mathlib dependency is the
local path `../../.lake/packages/mathlib`; the selected
[manifest](lake-manifest.json) also records Mathlib's eight inherited
dependencies. Their revisions agree with the root
[manifest](../../lake-manifest.json):

| Checkout under the root `.lake/packages` | Required Git HEAD |
|---|---|
| `mathlib` | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| `plausible` | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| `LeanSearchClient` | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| `importGraph` | `e928b72544873815af278d38681b31c0293588e3` |
| `proofwidgets` | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |
| `aesop` | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| `Qq` | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| `batteries` | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| `Cli` | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |

Before invoking Lake, [check.py](check.py) compares every selected Git pin
with the root manifest, verifies the actual HEAD of all nine checkouts, and
rejects changes to their tracked files. The HEAD and tracked-file checks
include the path dependency `mathlib`. Untracked files are excluded from the
cleanliness check; ordinary generated build artifacts may remain in place.

The prerequisites are:

- An independent repository checkout, with the pinned Lean toolchain already
  available and `python3`, `git`, and `lake` on `PATH`.
- All nine dependency directories above already populated at the required
  revisions, without tracked modifications.
- Writable build directories. Compatible existing dependency artifacts can
  be reused; this wrapper does not install dependencies or invoke the root
  wrapper's Mathlib cache-hydration helper.
- Ordinary `.lake` and `.lake/packages` roots. The wrapper applies the
  repository integrity checks to both the repository and this package,
  rejecting linked Git worktrees and symlinked Lake roots.

For missing sources, toolchains, or compiled artifacts, follow the repository
[cache policy](../../WARNING_DO_NOT_RUN_CACHE.md) and
[runbook](../../RUNBOOK.md). Provisioning must preserve these pins and comply
with the environment's network access. This package supplies no dependency
installer or alternate fetch policy. Do not use `lake update`, cache deletion,
or a toolchain change as an incidental repair. Never run `lake clean` or make
dependency directories read-only.

## Reproducible commands and their coverage

Run commands from the repository root. Inspect active compiler processes as
required by the runbook. The wrapper waits for the maintained shared build
lock and keeps it across pin validation and the Lake subprocess; execute
checks sequentially through this entry point.

The explicit equivalent of the default command is:

```bash
python3 verification/clifford-peirce-walsh/check.py build InfoGeometry.Canonical.CliffordPeirceWalshAudit
```

For a focused owner check during development:

```bash
python3 verification/clifford-peirce-walsh/check.py build InfoGeometry.Clifford.OperatorValuedJonesWalsh
```

That command builds the specified owner and its dependencies; it does not
select the aggregate declaration audit. Substitute
`InfoGeometry.OperatorAlgebra.StarSymplecticSqueeze` to select the other new
owner.

Lake can reuse already checked build artifacts. After building the audit
target, a fresh elaboration of the audit command against those imported
artifacts can be requested with:

```bash
python3 verification/clifford-peirce-walsh/check.py env lean "$PWD/lean/InfoGeometry/Canonical/CliffordPeirceWalshAudit.lean"
```

The `env lean` form checks the named file using available imports; it does not
rebuild changed dependencies. Build the target first when owner sources have
changed. The wrapper forwards Lake's exit status; a nonzero exit is a failed
check. Record the exact command, checked commit and working-tree changes,
output, warnings, and exit result rather than inferring success from a
previous run.

## Declaration audit surface

The canonical
[CliffordPeirceWalshAudit.lean](../../lean/InfoGeometry/Canonical/CliffordPeirceWalshAudit.lean)
selects declarations by their originating module. It audits the complete
declaration sets of these owners, including private and generated declarations:

| Audited module | Mathematical surface |
|---|---|
| `InfoGeometry.Clifford.OperatorValuedJonesWalsh` | Linear synthesis and extraction, doubled identities, normalized equivalence, Peirce coefficient bridges, internal twists, and the integral boundary |
| `InfoGeometry.OperatorAlgebra.StarSymplecticSqueeze` | Star-form Lie subalgebras and unit groups, Hamiltonian blocks, clock/shift identities, and the faithful squeeze representation |
| `InfoGeometry.Clifford.OperatorValuedJones` | Existing native matrix generators and Jones synthesis |
| `InfoGeometry.Algebra.IdempotentProjector` | Idempotents, native Peirce corners, and the direct corner API used by the new lift |
| `InfoGeometry.Geometry.AssociativeGaugeConnection` | Leibniz endomorphisms, algebraic connection curvature, and gauge covariance |
| `InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms` | Native Lie–Jordan endomorphisms and their commutator identities |

The audit rejects missing or empty selected owners, axioms introduced by those
owners, unsafe or partial owner declarations, and any collected axiom
dependency outside `propext`, `Classical.choice`, and `Quot.sound`. Axiom
collection follows each selected declaration's dependencies recursively. The
audit does not select every unrelated declaration in the entire import graph.

Successful audit execution prints `AUDIT_OWNER` counts, `AUDIT_AXIOMS`,
`AUDIT_DECLARATIONS`, `AUDIT_THEOREMS_INCLUDING_GENERATED`, and
`AUDIT_SUCCESS: 6 owners`. Counts describe the compiled source revision and
are not fixed acceptance thresholds. Read theorem carriers and hypotheses
separately: the axiom audit cannot establish an interpretation stronger than
the declared Lean types. The task's
[theorem contract](../../docs/CLIFFORD_PEIRCE_WALSH_CONTRACT.md) records those
mathematical boundaries.

The broader `PeirceParityClosure` and `PeirceParityTorsion` owners are
source-reviewed prior art. They are not imported merely for this audit; their
full-Mathlib import chain is not needed by the new constructions.

## Relationship to repository acceptance and publication

A successful scoped run establishes the selected target and audit in this
package's pinned environment. It does not certify the root project's optional
dependencies, root or alternate-source default targets, registered test suite,
or every tracked Lean file.

The root [runbook](../../RUNBOOK.md) remains authoritative for broader
validation. The staged proof gate, `.githooks/pre-push`, and
`scripts/quality/post_build_gate.sh` retain their own required coverage and
incremental/full classification. This package does not replace or bypass
those gates. Compiler success, declaration-axiom inspection, source/proof
scans, semantic review, and publication checks are separate pieces of
evidence and should be reported at their actual scope.
