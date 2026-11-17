# Real overlap chirality and projector curvature: source review

## Decision and verification boundary

**Independent mathematical, source, and API review accepted the four candidate
snapshots listed below.** The accepted scope is finite noncommutative algebra,
native real endomorphisms, and finite real matrix readouts. This decision does
not certify the paper's measure-construction theorem.

Independent QA completed all 13 bounded source-owner commands with exit 0,
accepted four nonblocking heuristic findings, and passed the workflow static
check. The maintained native build attempt was **blocked before compilation**
by the shared build lock and exited 2. The native declaration/axiom audit
therefore remains unperformed for this source snapshot. No kernel pass,
compiler-warning count, audit count, remote CI run, or publication result is
inferred from source acceptance or the static checks.

Repository: `nickgou-nuke/info-geometry-lean`.
Base: `08c34e03f610b452e03422037949196dc7d92d6d` (`main`).
Working branch: `feat/real-overlap-projector-curvature`.
This change is independent of the pending hypersymplectic PR393 ancestry.

See the [theorem contract](REAL_OVERLAP_PROJECTOR_CURVATURE_CONTRACT.md) and
the [frozen intake](intake/2026-11-17-lattice-chiral-fermions.md) for the source
version, claim ledger, and analytic/geometric debt.

## Exact reviewed candidate manifest

These SHA-256 values identify the candidate source bytes accepted by the
independent reviewer. They are not a certificate for a later PR head or its
entire imported closure. Any subsequent source repair needs a new source
identity and corresponding review/verification record.

| Intended owner under `lean/InfoGeometry/` | Reviewed candidate SHA-256 |
| --- | --- |
| `OperatorAlgebra/OverlapChirality.lean` | `cad7b92702df2c43ebb681eccfe18d42961a060f518f95ef3afe46908b93be73` |
| `OperatorAlgebra/PeirceCurvatureTrace.lean` | `c0ed43a6bc0b16de77849542d8f8457e9d4ead10473d3fb1f9be63eddbb17d38` |
| `Quantum/RealChiralCurvature.lean` | `b4bcf4f271114cf1764664622e264f62f058f3bc3dcd2619dc51310f3ab7725e` |
| `Clifford/RealChiralCurvatureExample.lean` | `4f25fef2c67e852d48e60548c7ddc85b41829b1afabf4b5456d1af0ae61d5bb9` |

The source inventory is 754 Lean lines, 47 public theorems (16 overlap,
6 generic trace, 11 real phase, and 14 example), 3 private trace lemmas,
and 5 definitions. These are source-declaration counts, not a count of
kernel-accepted or axiom-audited declarations.

## Mathematical scope accepted by source review

### 1. Overlap chirality preserves operator order

The generic carrier is an arbitrary `[Ring A]`. With supplied involutions
`gamma * gamma = 1` and `sigma * sigma = 1`, the definitions are
`d = 1 + gamma * sigma` and `hat_gamma = gamma * (1 - d)`. The source derives
`hat_gamma = -sigma`, the modified square law, and
`gamma * d + d * gamma = d * gamma * d`.

The stronger reusable intermediate statement identifies the exact defect:
`hat_gamma * hat_gamma - 1 =
 -(gamma * (gamma * d + d * gamma - d * gamma * d))`.
For involutive `gamma`, this proves the equivalence between modified
involutivity and Ginsparg--Wilson. Neither commutation nor anticommutation
between `gamma` and `sigma` is assumed.

The mixed law is `d * hat_gamma = -(gamma * d)`. On native
`Module.End ℝ V`, it yields the existing-projector identities
`d * Cartan.Pminus hat_gamma = Cartan.Pplus gamma * d` and the opposite-sign
counterpart. The same file treats the actual native kernel: original
chirality preserves it, modified and original chirality agree there, and
an overlap zero mode satisfies exactly `sigma x = -(gamma x)`.

The star-ring statements use their explicit self-adjointness hypotheses.
No spectral sign or square-root operator is constructed from them.

### 2. Tangent traces use the existing Peirce owners

`PeirceCurvatureTrace` works over `[Ring A]` and `[AddCommGroup M]` with a
native additive homomorphism `τ : A →+ M` and explicit cyclicity
`τ (a * b) = τ (b * a)`. It does not require division by two, a field,
self-adjointness, or a differentiable family.

The existing tangent equation is `p * x + x * p = x`, with `p * p = p`.
The source reuses the existing double-commutator reconstruction to kill a
single tangent under `τ`. It reuses the even product of two tangents to
show that an ordered triple is again tangent, and hence has zero trace.
This is the algebraic cancellation used in the proof of the paper's
Lemma 5.1; it is not the full exterior-derivative or transgression theorem.

With the existing coefficient `F(p,x,y) = p * (x*y-y*x) * p`, cyclicity gives
the single-projector trace and the gauge contraction
`τ (F(p,x,[g,p])) = τ (g*x)`. Complementing the projector and negating both
insertions gives `τ (F(1-p,-x,-y)) = -τ (F(p,x,y))`. The complement identity
does not add unnecessary tangency assumptions.

### 3. The real phase functional is constructed on its correct domain

`Quantum.RealChiralCurvature.phaseTrace` is the finite real matrix functional
`κ_J(T) = (1/2) * Matrix.trace (J * T)`. Its restriction is an actual
`AddMonoidHom` on native `Subalgebra.centralizer ℝ {J}`. Cyclicity is derived
from centralizer membership and `Matrix.trace_mul_comm`; it is not a field
assuming the desired conclusion. Cyclicity on the entire ambient real matrix
algebra is not claimed.

The real consumers instantiate the generic trace lemmas with this functional.
No custom carrier, trace axiom, positivity assumption, or normalized-state
interpretation is introduced. The algebraic cyclicity theorem needs only the
commutation condition; a square-minus-one law is the separate condition that
identifies the intended phase axis.

The existing realification has
`trace (realify T) = 2 * (trace T).re` and
`internalJ = realify (i * 1)`. Consequently the half factor and phase
orientation fix the exact sign:

`κ_internalJ(realify T) = -(trace T).im`.

The source also covers every member of the internal-axis centralizer by
reusing `realify_unrealify_of_commute`. The faithful map in this statement is
the existing matrix representation, not the scalar functional `κ`.

For self-adjoint `p`, `x`, and `y`, the already-owned sandwiched curvature is
skew-adjoint, so its complex trace has zero real part. The comparison theorem
uses `realifyRingHom` and `map_projectorCurvature` to transport the actual
ordered operator. For idempotent `p`, the result is exactly the scalar
`i * trace (p * [x,y])` from equation (4.19), viewed through the real
readout. This derivation does not assume that the unsandwiched operator
`p * [x,y]` itself is skew-adjoint.

### 4. The nonzero witness retains the full real operator

The example uses the existing Gull--Doran operators on `Matrix (Fin 4) (Fin 4) ℝ`:
`J = realPhaseAxis`, `P = (1/2) • (1 + realSigma3)`,
`X = realSigma1`, and `Y = realSigma2`.

The source proves that `P` is a self-adjoint idempotent, that `X` and `Y` are
self-adjoint projector tangents, and that each commutes with `J`. It reuses
the existing Pauli anticommutation, square, and pseudoscalar laws to establish
the full identity `F(P,X,Y) = 2 • (J * P)`. The existing `J * J = -1` and
`trace P = 2` then give `κ_J(F(P,X,Y)) = -2`.

This is a four-dimensional real example. The general comparison theorem uses
the existing `n ⊕ n` indexing convention; the witness uses native `Fin 4`
coordinates. No additional reindexing equivalence between those conventions
is claimed.

## Owner reuse and exclusions

| Existing owner | Declarations used or boundary inspected |
| --- | --- |
| `Cartan/Involution.lean` | Native `Pplus`, `Pminus`; existing square and complement API retained |
| `Core/IdempotentTangent.lean` | `tangent_eq_double_commutator`, `tangent_iff_adjoint_square_eq_self`; no new Kato-generator API |
| `OperatorAlgebra/PeirceCompressionCurvature.lean` | `tangent_product_commutes`, `star_projectorCurvature_of_selfAdjoint`, `map_projectorCurvature` |
| `Clifford/ChiralProjectorBerryCurvature.lean` | Existing `commutator` and `projectorCurvature` definitions |
| `Quantum/Realification.lean` | `realifyRingHom`, `realify_mul`, `trace_realify`, `internalJ_eq_realify`, `realify_unrealify_of_commute` |
| `Clifford/GullDoranPseudoscalarBridge.lean` | Existing real phase/Pauli operators, square laws, anticommutations, and volume-product identity |
| Native Mathlib | `Subalgebra.centralizer`, `Matrix.traceAddMonoidHom`, `Matrix.trace_mul_comm`, `Matrix.trace_conjTranspose`, native matrix and endomorphism operations |

The existing Cartan and Gull--Doran imports contain historical complex matrix
declarations. The new real operators do not depend on an external imaginary
scalar in their definitions. Complex notation is used in the explicit
comparison against the existing faithful realification.

## Phase, Krein symmetry, and analytic debt

In this record, `J` denotes an internal real phase with `J² = -1`; a Krein
fundamental symmetry `K` instead has `K² = +1`. Repository identifiers may use
other letters for these roles. The two square laws are not interchangeable,
and the supplied overlap involutions are not automatically identified with a
particular Krein fundamental symmetry. Krein self-adjointness alone does not
provide the positive-Hilbert spectral hypotheses needed for a spectral sign.

The overlap and curvature owners are two reusable finite branches. This
change does not construct a smoothly varying overlap family and identify its
actual derivatives with the supplied tangent data. It also does not establish
a spectral gap, locality estimates, a solution of Kato's ODE, a determinant
line bundle or its connection, exterior integration/Stokes transgression,
all-loop integrability, or a gauge-invariant fermion measure. The stated
Standard Model construction and any continuum-limit consequence remain
outside this PR.

## Verification record at this snapshot

| Stage | Recorded status | Scope |
| --- | --- | --- |
| Source generation | Complete | Four candidate files at the hashes above |
| Independent A-A review | Accepted | Mathematical hypotheses, signs, existing API use, and source-level proof strategy |
| Source closure inventory | 16 repository modules and 25 Mathlib import roots in the QA workflow review | Navigation/build input inventory, not compilation |
| Bounded source-owner QA | All 13 commands exited 0; four heuristic findings reviewed | Static/source scope; not Lean kernel evidence |
| Workflow static QA | `PASS_AT_SOURCE_AND_SYNTAX_SCOPE` | Configuration/source inspection, not a workflow execution |
| Maintained native build attempt | Blocked before compilation; exit 2 | Shared build lock refused concurrent execution |
| Native all-owned-declaration/axiom audit | Not performed for this snapshot | Required; permitted foundations are `propext`, `Classical.choice`, `Quot.sound` |
| Remote workflow execution/publication | Pending receipt | Workflow source alone is not evidence of a run |
| Root Lake/whole-repository build | Not certified | Separate from the four-owner scope |

Independent QA's recorded verdict is
`PASS_AT_EXACT_SOURCE_SCOPE_WITH_REVIEWED_HEURISTICS`. Semantic-content
coverage was 4/4 selected owners, with zero read failures and zero findings.
The strict screener reported no violations; the placeholder audit reported
zero hard and two soft findings; the semantic-vacuity gate reported two
warnings and used `--fail-on error`. All four heuristic findings were reviewed
as nonblocking, with zero actionable source issues. The result is not described
as a warning-free lexical scan. The legacy vacuity and style checks had zero
findings.

Source-QA summary SHA-256:
`bca93de4bd1f39fb1b0315c6e0117d902caed9e4db51d2b79adc1a1392e0797d`.
Workflow source/syntax review receipt SHA-256:
`813b32565d0f96ffc7de6b4e5f123a3541a3392f8d853dbdfc001ae8a4ab297c`.
That QA receipt covers the exact four source hashes, the workflow and aggregate
import delta; it explicitly excludes final documentation, native compilation,
the axiom audit, tests, hooks, and publication acceptance.

The configured workflow is
`.github/workflows/real-overlap-projector-curvature.yml`, source SHA-256
`2fb60333cae4017858d45f22a0b45d2a9cef8060ca742b869d0345b6b54f13d1` at this
snapshot. It selects the four owners above, the repository source closure,
and the maintained native declaration audit. It checks exact source revision,
the unchanged Lean `4.34.1` / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins, and zero selected-owner
compiler warnings. Its source configuration has been inspected; execution
results must be recorded independently. No checker weakening, dependency-pin
change, or whole-repository certificate is part of this review.

### Observed native attempt

The maintained command selected all four owners:

```text
python3 tools/infra/run_locked_lake_build.py InfoGeometry.OperatorAlgebra.OverlapChirality InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace InfoGeometry.Quantum.RealChiralCurvature InfoGeometry.Clifford.RealChiralCurvatureExample
```

It started at `2026-11-17T14:15:55.422508+00:00` and completed at
`2026-11-17T14:15:55.520005+00:00`, with return code 2. The wrapper reported
that `/tmp/info-geometry-build.lock` was held by recorded owner
`clifford-dirac`, PID `6`, and refused a concurrent build. No selected module
was compiled by this attempt. This is an execution block, not an observed
Lean proof error.

Native-attempt receipt SHA-256:
`2de762eb141fa36fbe99cc9c8300588e579e055980e2689b2a8fee130ca22ad8`.
Build-log SHA-256:
`81d2b8dd3bf1ecf0fab1d93b8b9c8bba2fea81cb1188f6f43a9a009f7dbf05f5`.
The receipt records source revision before commit as
`08c34e03f610b452e03422037949196dc7d92d6d`. Successful native compilation
and axiom acceptance remain outstanding; a later run needs its own receipt.

### Installed commit hook

The installed `.githooks/pre-commit` invoked the maintained
`tools/quality/proof_proxy_staged_gate.py` and returned
`proof_proxy_staged_gate: ok` for implementation commit
`d317a75658c1e4c4ee0e8aacbcf5b7b1d7165129`. The staged check included the four owners and the
`All.lean` import update. This is a source gate; native and root-package
acceptance remain outstanding as recorded above.
