# Validation record

Date: 2026-11-24. Upstream baseline:
`fe24e350b08fdea04f74c0748ef9fd9417c47529`.

## Current disposition

**Draft; complete kernel validation pending.** The complete source
implementation has independent mathematical reviews, an exact public
declaration inventory, and clean strict source screens. The first remote
focused CI run compiled three of the four new owners and found five proof
elaboration issues in the transport owner. The repairs described below are
source-reviewed and awaiting a fresh focused run. The first local Lake
invocation is still waiting for the maintained shared build lock, held by
another task; that job and lock have not been interrupted or bypassed.

The focused CI workflow builds the canonical source import closure, performs
a fresh axiom-printing run, checks every expected declaration exactly once,
and preserves its logs. Its actual result must replace the pending status
before this draft can be described as kernel-verified. A repository-wide
build and the root push gate have not completed; neither is claimed here.

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

The initial queued command selects
`InfoGeometry.Twistor.FenchelContactIncidence` through `check.py` with an
explicit existing package directory. It was launched before the runner's
provenance improvements. Final acceptance therefore requires the completed
focused build and fresh axiom run with the current runner, as documented in
`README.md`, even if that initial command subsequently succeeds.

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

## Acceptance boundary

Source screening, mathematical review, compilation, and axiom inspection are
separate checks. The present draft does not claim an integrated Hamiltonian
flow, a global para-Kähler atlas or supermanifold, a quantization map, an
adjoint physical supercharge pair, or an intertwiner with a fixed Zorn cut.
The exact local analytic and algebraic contracts are in the main audit.
