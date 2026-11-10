# Majorana quartet verification record

## Scope

This record accompanies the
[theorem contract](PARAFERMION_QUARTET_CONTRACT.md) and its
[preserved input](PARAFERMION_QUARTET_SOURCE.md).
It concerns generic quartic CAR algebra, one explicit four-state re-encoding,
and the native finite matrix spectrum. It does not certify a condensation
transition, a many-body topological phase, braid dynamics, or an SYM mass gap.

Generation and acceptance were assigned to different agents. The root agent
independently read the complete candidate sources, the relevant existing
Majorana and fourth-root owners, and Mathlib's actual spectral-mapping,
diagonal-spectrum, and characteristic-polynomial declarations. Its semantic
audit passed for the hashes below. Independent kernel acceptance and final
repository gate results are recorded in the completion section.

## Exact source fingerprints

Baseline Git commit: `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.

| Source under `lean/InfoGeometry/` | SHA-256 |
| --- | --- |
| `Algebra/FourthRootClockShift.lean` | `176f71a98bd8503fb5fb97aab70eff5966165825dad7d44a7035a1b4d81f07dc` |
| `Algebra/FourthRootPeirceProjectors.lean` | `5f5f523a488dfa98d53adf91b749950b04da1072ef30b9fa39d95d8c24a293be` |
| `Algebra/MajoranaQuartic.lean` | `95acc66c49aedb378164b8bbdda822e0f8efbcd35454caf09458b5f86f256159` |
| `Algebra/MajoranaClockReencoding.lean` | `a7e04389a642b81b1630db1f61ca751b6559eb4b7064c89ac2fc6730a75ea70c` |
| `Quantum/MajoranaQuarticFour.lean` | `6effca651902a2ff56089a7541276fae0ec4437ffcccb02004600304cf28628b` |

The four focused owners contain 50 public named declarations, of which eight
were relocated verbatim from the existing projector owner. Definitions and
theorems are counted separately from kernel-generated auxiliary declarations
in the independent audit: 39 public theorems and 11 definitions. Thus 50 is not
a claim of 50 new theorems.

## Mathematical audit

### Generic operator result

`MajoranaQuartic` retains the actual noncommutative ring carrier. The quartet
square and star reversal use the CAR sign changes. The parity theorem assumes
anticommutation with each generator and concludes native `Commute` with the
quartet and its scalar Hamiltonian. The spectrum theorem is containment over a
field; it does not assume either allowed spectral value exists.

Self-adjointness of the generators and of the scalar coupling are explicit
premises. `MajoranaSystem` itself does not silently supply a star condition.

### Concrete re-encoding

`MajoranaClockReencoding` uses exactly the existing
`Quantum.MajoranaVacuumWickFour.gamma` matrices. Their CAR and star laws are
proved before constructing the existing `MajoranaSystem` interface. The clock
and shift are the original fourth-root matrices, not a replacement family.

Both inclusions in `adjoin_majorana_eq_clock_shift` use native `Subalgebra`
closure and the proved forward/inverse ordered polynomial formulas. The
noncommutativity witness evaluates a matrix entry after forming both matrix
products. It does not replace a matrix commutator with a scalar surrogate.

The unitary results prove the star/inverse equations. Fourth power one alone
is not used as a substitute for unitarity.

### Finite spectrum and parity

`MajoranaQuarticFour` instantiates the generic theorem and identifies the
actual fourfold product as `diag(-1,1,1,-1)`. Its Hamiltonian is
`diag(g,-g,-g,g)`. Native Mathlib `spectrum_diagonal` and
`Matrix.charpoly_diagonal` give the exact spectrum and polynomial.

The total two-site parity is `firstParity * secondParity = -quartet`; it is
conserved. The separate identity `degreeClock² = secondParity` must not be
interpreted as identifying this clock square with total parity.

The proved characteristic-polynomial factorization explains the two distinct
roots and their algebraic multiplicity two for nonzero coupling. No separate
`rootMultiplicity` or eigenspace-dimension theorem is claimed. At zero
coupling the roots coincide and the polynomial is `X^4`.

### Existing owner extraction

The following eight declarations retain their original fully qualified names,
statements, attributes, and proof bodies: `phase`, `phase_fourth`,
`cyclicShift`, `degreeClock`, `cyclicShift_fourth`, `degreeClock_fourth`,
`degreeClock_shift`, and `cyclicShift_fourth_ne_zero`.

They now live in `FourthRootClockShift` under the original
`InfoGeometry.Algebra.FourthRootPeirceProjectors` namespace. The older projector
module imports this focused owner. Its remaining source text is identical to
the baseline after accounting for the mandatory copyright header and added
import. The projector covariance proof remains in the older owner.

The extraction checker compares exact source blocks with the baseline Git
blob and checks that the remainder is unchanged. This is source-integrity
evidence. It is not described as a full compilation of the old 418-module
dependency graph.

## Toolchain and baseline

| Component | Observed value |
| --- | --- |
| Lean | `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` |
| Lake | `5.0.0-src+5045d00` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Official Lean archive SHA-256 | `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4` |
| Unmodified Lean executable SHA-256 | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |

All eight Mathlib dependency revisions were checked against its pinned
manifest. Cache hydration returned exit 0 for 8,908 files; a native
`import Mathlib` smoke check passed. No tracked dependency/toolchain pins were
changed.

This executor required a runtime-only `readlink`/`readlinkat` shim after the
official compiler was observed to fail locating `/proc/<own-pid>/exe`. The
shim redirects only that own-process executable-link spelling to
`/proc/self/exe`; the official Lean binary is unchanged.

The narrow verification rebuilt these five unchanged repository dependencies:

| Dependency | Result | Existing warning count |
| --- | --- | ---: |
| `Algebra.FiniteSpinAlgebra` | Strict compilation passed | 0 |
| `Algebra.CliffordBraidingInterfaces` | Strict compilation passed | 0 |
| `Volume.OrientedPfaffian` | Ordinary compilation passed | 4 |
| `Volume.MajoranaPfaffianFour` | Ordinary compilation passed | 23 |
| `Quantum.MajoranaVacuumWickFour` | Ordinary compilation passed | 4 |

Their source hashes were checked against Git and remained unchanged. Legacy
lint warnings were retained, while all four task-owned focused modules use
warnings as errors. No repository gate or linter policy was weakened.

## Commands and observed build boundary

All compiler/build/test jobs used `/tmp/info-geometry-build.lock`. Maintained
wrappers acquire that lock themselves and were not double-locked.

Generation smoke checks compiled the four focused modules with the exact
native compiler, an isolated artifact overlay, and:

```sh
flock /tmp/info-geometry-build.lock lean -DwarningAsError=true \
  -R <overlay> -o <module>.olean <module>.lean
```

All four final generation checks returned exit 0 with empty diagnostic output.
The independent acceptance run rebuilds these files in its own overlay and
inspects every module-owned kernel constant, including private/generated
constants, rather than only the public theorem list.

Before any Lean source promotion, the actual repository wrapper was run on
the unchanged older owner:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.FourthRootPeirceProjectors
```

It returned exit 1 before elaboration:

```text
error: HomotopyHypothesis: package directory not found:
  external_refs/homotopy-hypothesis-lean4
```

Thus a successful narrow kernel check does not certify the root Lake package,
the broad projector owner, or either repository umbrella. The ordinary root
build requires restoration of that existing local dependency. This change
does not invent a replacement package or alter its manifest entry.

## Independent acceptance

Disposition: `ACCEPTED_WITH_LIMITED_SCOPE`. The four focused owners passed
independent strict compilation; all five touched owner sources passed the
unchanged stock OpenGauss source screener. The edited older projector owner
has exact source-preservation acceptance only. Root-package and broad-owner
kernel acceptance remain blocked as described above.

The acceptance record SHA-256 is
`0de79053b71e83a755c67761226222723d16e0847ccd51979e1ca69021cc786b`.
Every promoted owner was compared byte-for-byte with its accepted candidate.

| Focused owner | Audited kernel constants |
| --- | ---: |
| `MajoranaQuartic` | 24 |
| `FourthRootClockShift` | 12 |
| `MajoranaClockReencoding` | 34 |
| `MajoranaQuarticFour` | 14 |
| Total | 84 |

The audit includes 73 theorem/auxiliary constants and 11 definitions. It
examines each checked type and value, including private and generated
declarations, and compares their dependency union with native
`Lean.collectAxioms`. Only `propext`, `Classical.choice`, and `Quot.sound`
occur. No owned unsafe, partial, or authored local-axiom constant occurred.

The initial characteristic-polynomial proof passed Lean but received a stock
T16 source warning classified as an error. The generator made the scalar
boundary explicit using a local equality over `Polynomial ℂ`, then consumed
it after the matrix characteristic-polynomial rewrites. The public theorem
statement is unchanged. Fresh strict compilation, stock screening, and the
complete axiom audit passed after that correction. No gate was altered.

Four nonblocking stock vacuity-regex findings (`s `, `k `, `i `, `U `) were
retained and inspected. Each parameter is explicitly used in its multiline
proof. They are lexical false positives, not evidence of unused hypotheses.
This is separate from the zero-warning compiler results.

## Repository integration gates

The accepted source bytes were promoted and exposed through
`InfoGeometry.lean` and `InfoGeometry.AllExhaustive`. The following integration
checks were executed sequentially under the shared lock:

| Check | Result |
| --- | --- |
| `python3 tools/quality/proof_proxy_staged_gate.py` | Exit 0, `proof_proxy_staged_gate: ok` |
| `python3 tools/quality/semantic_content_audit.py` with the five exact owner `--file-prefix` filters and `--gate` | Exit 0; five selected files; zero findings and zero blocking findings |
| `git diff --cached --check` | Exit 0 |

Tracked hooks were installed with `scripts/install_git_hooks.sh`; their
installation alone is not counted as an executed check. The actual commit
hook and pre-push outcomes belong to the accompanying pull request's
publication record, which is written after those commands run. This source
record certifies only the exact checks stated above. No repository-wide green
build, broad-owner compilation, or merge readiness is asserted.
