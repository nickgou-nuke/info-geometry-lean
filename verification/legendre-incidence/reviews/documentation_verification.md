# Independent review of documentation and verification sources

Date: 2026-11-24
Reviewer: `/root/incidence_grassmann_audit`
Mode: source/claims review only. No Lean, Lake, audit script, source screener, or test suite was executed by this reviewer.

## Reviewed snapshots

| File | SHA-256 |
| --- | --- |
| `docs/LEGENDRE_INCIDENCE_OPERATOR_AUDIT_20261124.md` | `5563880d90be08c14933891272c6213475bf4d19e068425ef6fd32b5dd4d490a` |
| `verification/legendre-incidence/README.md` | `0b04380637e3260cb3b317318503edcd9383edb14b58e9ad2593696f322c2fb1` |
| `verification/legendre-incidence/audit.py` | `1e22c135d33595c41b40da3de7df286582a41e9f8059af3140683467168ba1e2` |
| `.github/workflows/legendre-incidence.yml` | `f421001fd3d60d7fac887614ad9194a5c4b5d9d1214ead1689aa75f44387ae34` |

Supporting sources inspected included the four integrated owners, generated `LegendreIncidenceAudit.lean`, focused `check.py`, focused Lake configuration and manifest, maintained build-lock/integrity helpers, and pinned Lean/Lake command implementation.

## Assessment

No strengthened mathematical claim or present kernel-success claim was found. The documentation accurately describes the new theorem contracts and keeps local analytic facts, global convexity assumptions, finite-dimensional constructions, and unimplemented global geometry distinct. The workflow and documented commands are source-consistent with the pinned Lake implementation.

One minor documentation issue should be resolved before publication: the audit presently says a final review record **is maintained with the validation package**, but that package did not yet contain such a record when inspected. Existing review records are in the candidate directory. Add the final validation/review record as planned, or use prospective wording until it exists.

The last status paragraph explicitly says the first focused kernel build is queued and that successful kernel validation is not yet asserted. This is the correct current evidence boundary. The reported previous OpenGauss result and external PDF-page observations are retained root/other-reviewer evidence; they were not rerun or independently reinspected in this review.

## Declaration coverage

Static source enumeration gives:

| Integrated owner | Explicit public definitions and theorems |
| --- | ---: |
| `Twistor/FenchelContactIncidence.lean` | 21 |
| `Geometry/LegendreGraphGeometry.lean` | 24 |
| `Geometry/CotangentOperators.lean` | 27 |
| `Twistor/FenchelContactTransport.lean` | 41 |
| **Total** | **113** |

The generated audit has 113 `#print axioms` commands. A read-only textual comparison of the namespace-qualified declaration sequence against the generated command sequence produced no differences. The transport owner correctly contributes declarations to the existing `InfoGeometry.Twistor.FenchelContactIncidence` namespace rather than an invented module-named namespace.

All four owners currently use one explicit namespace and declaration forms recognized by `audit.py`. Thus the claim is correct for the reviewed sources. It counts explicitly written declarations; it does not purport to enumerate every generated recursor, equation theorem, transitive import declaration, or module-level instance from dependencies.

### Future scanner limitation

The inventory scanner is intentionally simple: it recognizes `def`, `abbrev`, `theorem`, `lemma`, and `structure` in the current layout. A future public `opaque`, `instance`, or `protected theorem`, or substantially different namespace/attribute syntax, would need deliberate scanner support or a fail-closed check. Likewise, its comment stripper is not a full Lean lexer for strings. None of these unsupported forms affects the present 113-declaration inventory. Avoid upgrading this script's description to a general Lean parser.

## Mathematical claim checks

### Contact and bounded conjugates

The audit distinguishes arbitrary `fStar` from the actual `Convex.fenchelConj f`. Its support inequality retains the bounded-above support-set hypothesis, and its actual derivative corollary uses global convexity plus a local `HasFDerivAt`. It correctly says that the latter derives attainment, boundedness, and equality. The nonzero homogeneous factors, dyad square, and Peirce products agree with the integrated owner.

### Hessian graphs and the native Grassmannian

The audit correctly separates unnormalized twistor neutral pairing from the normalized graph metric. Symmetric Hessian graphs are symplectically self-orthogonal; they are generally not null for the symmetric split form. Fixed para-grading invariance forces the graph map to vanish. The native Grassmannian index is identified as quotient rank, which agrees with the actual construction.

The C² statement uses only `ContDiffAt ℝ 2 f x` for the analytic local conclusion. Symmetry is derived from the native second-derivative theorem. Finite dimension is introduced only for dimension and Grassmannian packaging. Convexity and positivity are not added to these local tangent results. The prose does not promote them to global Legendre-coordinate invertibility or a manifold atlas.

### Operators, symmetry, and signs

The cotangent lift is described with the required negative dual. The graph-preservation equation is explicitly qualified as constant-`H` infinitesimal invariance, avoiding the missing metric-variation term of a position-dependent Killing equation. The algebraic quadratic Hamiltonian expansion and directional commutator identity have the correct Geometry signs; the opposite Quantum convention remains explicit.

### Contact superderivation and transport

The prose states the actual upper-corner parity and nonzero square-zero graded derivation, with `delta(P)=-D` as the nonvacuity witness. It correctly transports the actual Fenchel conjugate by equality of support sets, which does not require a boundedness premise for that equality. It does not remove boundedness from the separate inequality/support interpretation.

The explicit transvection is correctly described as a reference-cut change on the homogeneous carrier. The reference dyad has covector `(p,-1,0)` and the reference pair is expressly labeled an algebraic normal form. No fixed Zorn identification, star self-adjointness, lower supercharge, integrated flow, or physical supersymmetry is asserted.

### Existing source defects

The two named source-defect observations were spot-checked. `CoordinateFreeSouriauDerivation.CoordinateFreeSouriau` really quantifies its purported norm equation over every function, so the constant-zero/constant-one contradiction applies whenever the base has a point. `CoordinateFreeSouriau.ScalarDerivation` really uses the commutative-order product rule under only `[Ring F]`. The stated limitation of the conformal packet is consistent with its inherited equilibrium field. These observations do not claim that the stronger independent native owners share those defects.

## Verification script review

`audit.py` checks focused/root toolchain equality and Mathlib revision agreement, regenerates the expected audit text, rejects stale text, and compares the set of names reported by Lean with the exact current inventory. Only `propext`, `Classical.choice`, and `Quot.sound` are admitted in parsed axiom records.

The output parser agrees with pinned Lean `Lean/Elab/Print.lean`: its actual messages use either `'name' depends on axioms: [...]` or `'name' does not depend on any axioms`. The script correctly handles multiline axiom lists using the bracket-delimited regex.

The log parser does not itself establish the exit status or provenance of the log-producing process. In the checked workflow this is addressed by sequential execution with `set -euo pipefail`: a failed build or failed fresh Lean invocation stops the step before the audit can be accepted. Retain that ordering and exit-status gate. A standalone hand-supplied log remains evidence supplied to a validator, not an independently executed kernel check.

The broader nine-dependency agreement claim is enforced by `check.py`, not by `audit.py` alone. Its source compares all nine focused Git pins against the root and also checks the focused Mathlib requirement. The optional `--dependency-root` branch checks each reused checkout's revision and tracked cleanliness before and after execution. The README confines its checkout-integrity claim to this branch correctly.

## Commands and workflow

- The focused `lakefile.toml` reads canonical sources via `srcDir = "../../lean"`, specifies the four owner targets plus the audit, and places project outputs under the focused package's own Lake build directory.
- The default package directory `../../.lake/packages` agrees with the root dependency-cache path used by the workflow.
- The wrapper starts Lake with `cwd=ROOT` and `-d PROJECT`. Pinned `Lake.CLI.Main.lake.env` spawns its child without changing that working directory. Consequently the documented argument `env lean lean/InfoGeometry/Twistor/LegendreIncidenceAudit.lean` resolves to the intended canonical file; it should not be rewritten relative to the focused directory.
- Pinned Lake supports `--packages` through `Manifest.loadEntries`; the temporary package-location override approach is native to this runtime.
- The workflow installs the same currently pinned Lean 4.34.1 version, restores dependencies, builds before the fresh axiom-printing run, checks the resulting log, and separately runs the strict source screen. The shell pipeline correctly preserves failure status through `tee`.
- `permissions: contents: read`, the declared triggers, and the validation-log upload are consistent with a read/build verification workflow. The cache and toolchain strings are deliberately version-specific and should be updated when the pins change.
- The README could usefully state the wrapper's runtime prerequisites: Python 3.11 or later is required by `tomllib`, and the maintained `fcntl` build lock requires a POSIX environment. The present Ubuntu workflow fits those prerequisites; this is a documentation clarification, not a current workflow failure.

## Publication gate

Replace the queued-build paragraph with observed command results only after root's serialized run completes. Add or link the promised final review/validation record, retaining the exact validated revision and declaration count. If a Lean failure forces a change to any theorem statement, mathematical assumption, sign, or carrier, update the corresponding contract and request a targeted review. Nothing in this source review certifies an unexecuted build.
