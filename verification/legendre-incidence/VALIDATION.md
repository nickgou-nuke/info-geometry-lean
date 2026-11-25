# Validation record

Date: 2026-11-24. Upstream baseline:
`fe24e350b08fdea04f74c0748ef9fd9417c47529`.

## Current disposition

**Focused kernel, axiom, and source validation passed.** The repaired source
was freshly built and audited by successful
[CI run 45361210176](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45361210176).
All four mathematical owners and the generated audit compiled, and the
separate fresh axiom run checked all 113 public declarations exactly once.
Only `propext`, `Classical.choice`, and `Quot.sound` were reported.

The PR remains a draft because the wider repository gates have independent
baseline failures listed below. This is a certificate for the focused import
closure and declaration inventory, not the whole repository. The final record
update changes documentation only; the checked Lean sources, audit script,
runner, manifests, and workflow remain unchanged from the successful run.

### Successful checked revision and commands

- PR head: `752875eaee124ada0faf40654e7b5e988a6b6004`.
- Actual GitHub checkout: merge commit
  `b66b51f8aa8b5bcd1557343b66ff059072faa669`, incorporating that head into the
  unchanged upstream baseline named above.
- Job: `138331442254`. Completed successfully on 2026-11-24.
- Focused source artifact cache: miss; the log explicitly records fresh builds
  of all four owners and the audit.

| Executed command | Observed result |
|---|---|
| `python3 verification/legendre-incidence/check.py exe cache get` | Exit 0; pinned artifacts hydrated; stability checks passed. |
| `python3 verification/legendre-incidence/audit.py` | Exit 0; 113 declarations in four owners. |
| `python3 verification/legendre-incidence/check.py build` | Exit 0; all five targets built; Lake reported 8,942 jobs. |
| `python3 verification/legendre-incidence/check.py env lean lean/InfoGeometry/Twistor/LegendreIncidenceAudit.lean` | Exit 0; fresh axiom output. |
| `python3 verification/legendre-incidence/audit.py --log legendre-incidence-axioms.log` | Exit 0; exact inventory and allowed foundational axioms only. |
| Strict OpenGauss screen on the four owners and audit | Exit 0; zero findings. |

The build and fresh axiom run both checked the same 60-file source and
configuration snapshot, SHA-256:

```text
0cf2bccd7742266e7de1b7ae5329bfd84e27b88f003f51657f94569c43f246c3
```

Both reported source/configuration/runtime stability passed. The successful
run used Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Lake 5.0.0-src+5045d00.

Preserved evidence:
[artifact 14905008070](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45361210176/artifacts/14905008070),
`legendre-incidence-validation.zip`, SHA-256:

```text
1568fc5a991f273efa57365d5837a732410087532d5e556ea018a7147e42b961
```

The only mathematical-source warnings observed in the successful run came
from unchanged `PeirceSpine/Supercharge.lean` tactics. All new owners completed
without a reported warning in that run.

## Executed source checks

| Check | Observed result |
|---|---|
| `python3 verification/legendre-incidence/audit.py` | Exit 0; 113 public definitions/theorems in four owners. |
| `python3 tools/infra/opengauss_screener.py --strict` on the four owners and `LegendreIncidenceAudit.lean` | Exit 0; zero findings. |
| `python3 tools/quality/proof_proxy_staged_gate.py` | Exit 0; also executed successfully by the tracked commit hook. |
| `git diff --check` and `git diff --cached --check` after review-file whitespace cleanup | Exit 0. |
| Python `ast.parse` on the focused `check.py` and `audit.py` | Syntax accepted; this is not a runtime test. |
| Independent graph/contact, operator/transport, documentation, and validation-runner reviews | Source approval with exact hypotheses and interpretation boundaries recorded in `reviews/`. |

The mathematical source inventory is 21 contact declarations, 24 graph
declarations, 27 cotangent declarations, and 41 transport declarations.

## Runtime and dependency observations

The recovered runtime reports Lean 4.34.1 and Lake 5.0.0-src+5045d00, with Lean
commit `5045d0056413266e57c625dcd7c365b10e377c52`. The available Mathlib source
has exact pinned HEAD `d13f23b723b8a846827a245b89c10fc7d3f11612` and clean tracked
sources. The focused manifest preserves all nine corresponding root pins.
No tracked toolchain or dependency revision was changed.

The initial local command selected
`InfoGeometry.Twistor.FenchelContactIncidence` through `check.py` with an
explicit existing package directory. It was launched before the runner's
provenance improvements. Its dependencies compiled, but the final Lean process
ended with code 137 and no theorem-elaboration error. That result is recorded
without attributing a specific operating-system cause. It does not establish
either success or a mathematical counterexample. That acceptance requirement
is now met by the successful focused build and fresh axiom run recorded above.

The current runner checks the actual runtime, exact dependency revisions,
workspace integrity, local overrides, and stable source/configuration hashes
under the same shared lock. Its output is designed to bind a compiler run to
the corresponding input snapshot. The original runtime-unavailable attempts
remain historical environment failures in the main audit; they are not Lean
counterexamples.

## First focused CI run and repairs

Run [45359832998](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45359832998)
checked head `4821565187c4043267b11602c295fec6639e32f7`. Its completed job was
`138326763022`; logs were preserved as artifact `14904221982`.

Pinned toolchain installation and Mathlib cache hydration succeeded. The
runner checked runtime and input stability successfully. The build snapshot
contained 60 source/configuration files, digest
`d07fbb63f19ee617c9a51680f00fff74d4296426b8d34eb6081cbc262f71c6c2`.

Three new owners compiled successfully:

- `InfoGeometry.Twistor.FenchelContactIncidence`
- `InfoGeometry.Geometry.LegendreGraphGeometry`
- `InfoGeometry.Geometry.CotangentOperators`

`FenchelContactTransport` failed at one scalar simplification and four
overly recursive `ext z` calls on homogeneous product domains. The source
repair adds `RingHom.id_apply` and uses explicit `LinearMap.ext` followed by
`intro z`, keeping the complete product argument. Definitions, noncommutative
order, and all transport theorem statements are unchanged.

The same patch follows three compiler lint suggestions: omit the unused
`NormedSpace` instance from homogeneous-point nonvanishing, omit the unused
finite-dimensional instance from the graph/source finrank equality, and
remove an unused `add_mul` simplifier. The two assumptions are safely
generalized; the Grassmannian construction still requires finite dimension.
The independent delta review is preserved in `reviews/ci_repairs.md`.

Lake returned exit 1 in this first run, and the fresh axiom check was not
reached. This partial build is not a certificate for the complete bridge.

## Wider repository CI boundaries

The following failures were inspected at the successful proof head. Each
comes from unchanged baseline files or prerequisites. The PR comparison at
that head contains 19 added files and no modifications to existing files.

| Gate and observed run | Exact blocker |
|---|---|
| [Post-Build Quality Gate 45361210351](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45361210351/job/138331442989) | The root build cannot load the existing required package directory `external_refs/homotopy-hypothesis-lean4`; Lake exits 1 before the post-build quality gate. The root dependency declaration and manifest are unchanged. |
| [Reviewed PR Integration 45361210700](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45361210700/job/138331445091) | Recursive submodule checkout exits 128 because baseline gitlink `external_ref/open-math-harness` has no URL entry in `.gitmodules`. Compilation and auditing are skipped. |
| [Lean style lint 45361210198](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45361210198/job/138331440948) | The case-sensitivity prerequisite finds existing `src/InfoGeometry/Physics/PellisfineStructure.lean` and `PellisFineStructure.lean`. Lean style checking does not proceed. |
| [Sorry Gate 45361210887](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45361210887/job/138331446860) | The repository-wide tracked-source threshold reports 878 findings in 91 forensic/fixture files; package and unclassified counts are zero. All 91 paths exist at baseline, and none is a PR file. The later quarantine command is not reached after this exit 1. |

These are specific inspected failures, not a classification of every
repository workflow. No root-gate success or whole-repository certificate is
claimed. The local tracked commit/source gates passed; publication used the
authorized GitHub draft workflow, with these broader acceptance boundaries
left visible rather than marked successful.

## Acceptance boundary

Source screening, mathematical review, compilation, and axiom inspection are
separate checks. The present draft does not claim an integrated Hamiltonian
flow, a global para-Kähler atlas or supermanifold, a quantization map, an
adjoint physical supercharge pair, or an intertwiner with a fixed Zorn cut.
The exact local analytic and algebraic contracts are in the main audit.
