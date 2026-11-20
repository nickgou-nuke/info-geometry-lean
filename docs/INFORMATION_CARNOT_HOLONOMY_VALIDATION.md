# Carnot work holonomy: native validation

Date: 2026-11-18, Europe/Sofia.

This record extends the accepted information-Carnot checkpoint at remote
`c4d12dcea71455c2ad0885f90a36e4362d80cacb`, local
`7ddc3a1bc22f967feb48375a5a2d61c43c3a2258`, complete tree
`40ff0f6dc60c5d4c9097859bd8d782c16552f063`.
The preceding source, validation evidence and dependency pins were preserved.

## Claim review

The source audit separates exact density retracing from a nontrivial work
translation over the full density/Hamiltonian base. The construction and its
remaining mathematical boundaries are specified in
`INFORMATION_CARNOT_HOLONOMY_CONTRACT.md`.

Independent non-author review covered the density-path owner, the full matrix
connection and its actual derivative, and the cycle integration owner. Review
required an explicit closed path in the full base. The final cycle owner
constructs native affine/scale paths and matches both density and Hamiltonian
at all four junctions through native endpoint types. The connection transport
is the composition of four constructed horizontal stroke transports.

No ordinary homotopy-invariance premise, commutation premise, assumed work
budget, conclusion-storing structure field, external scalar imaginary unit,
authored axiom, proof hole, `native_decide`, or unsafe bypass was introduced.

## Exact runtime and build discipline

- Lean `leanprover/lean4:v4.34.1`, native commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The existing maintained `tools/quality/check_clifford_dirac.py` checker and
  complete generated all-owned declaration audit were used unchanged.
- One compiler owner used the canonical `/tmp/info-geometry-build.lock`.
  No competing native compilation or cache process was launched.
- An independent checkout with its own real `.git` was used; the accepted
  checkout and output were retained separately. No linked worktree or
  symlinked `.lake` was introduced.
- The final closure contains 48 repository modules and 60 native import roots.
  All 8,530 transitive Mathlib modules already had their required native
  artifacts. No additional cache hydration was needed.

## First native checkpoint: failed, evidence retained

The initial ten-target pass checked the accepted eight owners and the first
two holonomy owners. It resolved 47 repository modules. The 44 accepted
closure sources passed source, dependency, toolchain and compiled-artifact
fingerprint reuse. The existing split-quaternion dependency compiled.

The new source diagnostics were concrete Lean elaboration issues:

1. Two `omit` commands followed documentation comments, producing parser
   errors. Moving each command before its comment fixed the syntax without
   altering any proposition or proof.
2. The receiver of `workForm.flip` needed its matrix dimension specified.
   The failed definition caused the subsequent curvature elaboration errors.
3. The finite matrix witness needed explicit entry reduction and native
   split-quaternion product rewrites. Two unused simplifier arguments were
   removed. The matrix statements, ordered products and witness were retained.

The failed checker output and all 47 matching source snapshots were retained
as `verification-carnot-holonomy-pass1`. No axiom audit acceptance was claimed
for this failed pass. A `sorry` diagnostic emitted downstream of the failed
definition was a Lean error-recovery artifact, not an authored proof hole.

## Final local checkpoint: passed

The next maintained native check selected all eleven owners, including the
new cycle-integration owner. All 48 repository modules succeeded: 45 passed
the maintained fingerprint/artifact reuse checks, and all three new owners
compiled freshly. The full declaration audit ran freshly. That complete
passed source/evidence snapshot was retained as
`verification-carnot-holonomy-pass2`.

The actual installed pre-commit hook then rejected a `ring` step in the
connection-curvature proof under its T16 operator-tactic rule. No commit or
publication occurred. Although the preceding `change` had exposed real
scalar evaluations, the proof was improved to use the explicit native
additive identities `-a - (-b) = b - a = -(a - b)`. The proposition, ordered
matrix products, assumptions and gate were unchanged. Independent source
review and the staged proof gate passed on this replacement.

The final maintained eleven-target check then passed again. It reused 46
modules under the maintained fingerprints and freshly compiled the repaired
work-connection owner and dependent cycle owner. A fresh complete declaration
audit retained the same counts and axiom union below. This is the accepted
final source snapshot.

| Selected owner | Native warnings | Audited owned declarations |
| --- | ---: | ---: |
| `Thermo.RealMatrixGibbs` | 0 | 45 |
| `Thermo.RealMatrixCarnot` | 0 | 74 |
| `Thermo.RealDensityRadialFlow` | 0 | 52 |
| `Thermo.RealMatrixGibbsOrbit` | 0 | 15 |
| `Thermo.RealMatrixGibbsRadialChart` | 0 | 7 |
| `Thermo.GramMetriplecticNoReturn` | 0 | 19 |
| `Canonical.WeylEntropyScaleObstruction` | 0 | 2 |
| `Physics.MatrixTraceBimodulePairingNative` | 0 | 19 |
| `Thermo.RealMatrixCarnotStateLoop` | 0 | 31 |
| `Thermo.RealMatrixWorkConnection` | 0 | 73 |
| `Thermo.RealMatrixCarnotHolonomy` | 0 | 46 |
| **Total** | **0** | **383** |

The audit covers every declaration owned by these modules, including private
and generated constants. The 150 new owned declarations are not asserted to
be 150 separately authored theorems. The complete axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The import closure retains 70 existing native warnings outside the selected
owners: the previously recorded 35, plus 35 in the existing recovered
split-quaternion owner. All eleven selected owners have zero native warnings.

The three accepted new source SHA-256 values are:

| Source | SHA-256 |
| --- | --- |
| `RealMatrixCarnotStateLoop.lean` | `2b0fe56c921370ad96e46d5d679e9aaf2832e299747a1144c854bd50bed11295` |
| `RealMatrixWorkConnection.lean` | `d3e368fc7ada036251ddc7407b796abfd36bbdbccb05cea5303298ee56dc8a90` |
| `RealMatrixCarnotHolonomy.lean` | `b98f57df6b57d7f092b80806ace6708bd702cc82938ee4b46b85e0095823c328` |

Independent verification reconciled all 56 evidence-manifest entries, all
48 current/source-snapshot hashes, all 48 compiled artifact records, and all
four unchanged verification-helper hashes. All 44 accepted baseline source
hashes and the preceding 233 declaration counts remained unchanged.

The local report records the checkout's base revision plus the exact working
source hashes. It does not by itself certify a later Git commit or whole
repository build. No task-owned compiler remained running at completion.

## Source gates and CI coverage

Strict placeholder scans and the semantic error gate passed on all eleven
selected files. The heuristic scans retain 19 soft placeholder notices and
30 semantic supporting-API notices, with zero hard findings/errors. The two
new soft notices concern elementary scaling simplification and connection
fiber-coordinate independence; the fourteen new semantic notices concern
definitional application lemmas, constant-path/initial-value reductions,
alternation and vertical reproduction. Their actual source bodies were
reviewed. They are neither compiler warnings nor added axioms.

The existing information-Carnot workflow now selects the same eleven owners
for cache resolution, native checking and source gates. Static reconciliation
confirmed all three target lists agree, and every one of the 48 repository
closure paths is watched. The explicit zero-warning assertion for every
selected target, complete audit, exact-PR-head checkout and evidence upload
remain in place. Dependency pins, checker helpers and gate policies were not
changed.

At this committed-record checkpoint, remote publication and the exact new-head
CI run are pending. Their resulting head, complete tree, run and artifact
checksums will be recorded in the PR validation section without rewriting
this chronological checkpoint or changing accepted proof sources.

Verification is scoped to these owners and their complete import closure.
No whole-repository build, root pre-push acceptance, merge, Uhlmann transport
construction, general Souriau-manifold Stokes theorem, or finite-time engine
claim follows from this checkpoint.
