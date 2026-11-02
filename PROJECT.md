# Historical CAS proof-refactor campaign

This page records the CAS-assisted refactor campaign whose later milestones
were dated 2026-09-22. It is a project history and navigation aid, not the current
repository-wide architecture, operating policy, or build-status report. Start
with [README.md](README.md), [AGENTS.md](AGENTS.md), and
[docs/README.md](docs/README.md) for those roles.

The file inventory and runner behavior below were source-reviewed on 2026-11-03
at commit `214f7bcf733eaf4720913bc2c082936f2480d3fc`. The historical milestone
outcomes were not re-executed or independently re-certified in that review.

## Campaign objective and current implementation

The campaign aimed to reduce costly elaboration in selected Lean modules by
using exact small-example calculations and reusing existing structural
theorems. Its historical label was “CAS O(1) Optimization.” The present source
supports narrower descriptions:

| Component | Current source and scope |
|---|---|
| Graph matrix diagnostic | [cas_dirac_laplacian_certificate.py](scripts/cas_dirac_laplacian_certificate.py) constructs exact rational matrices and asserts block/trace identities for a fixed chain, triangle, and digon. |
| Lean graph owner | [DiracLaplacian.lean](lean/DAG/DiracLaplacian.lean) contains the graph examples, arithmetic definitions, and graph-Dirac theorem statements targeted by the runner. |
| Fock bridge | [NoncommutativeFockBridge.lean](lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean) reuses projector and CAR declarations from its imported owners through Lean proof terms. CAS references in comments do not themselves import certificates into Lean. |
| Integration source | [DAG.lean](lean/DAG.lean) is the aggregate whose Dirac import is checked. |
| E2E runner | [e2e_cas_o1_suite.sh](tools/e2e_cas_o1_suite.sh) combines two owner builds, source-pattern checks, the fixed CAS examples, import/elaboration checks, and two timing thresholds. |
| Compiler serialization | [run_locked_lake_build.py](tools/infra/run_locked_lake_build.py) and [run_locked_lean.py](tools/infra/run_locked_lean.py) provide shared-lock entrypoints. The E2E runner uses the build wrapper in tier 1 but still makes direct unlocked Lean calls in tiers 3 and 4. |

There is no asymptotic O(1) proof in the timing test. `rfl`, `exact`, and the
absence of selected tactics do not establish a general complexity bound. The
runner measures two fixed files with a **35-second timeout** and a separate
**15-second maximum passing elapsed time**. Its proposition checks use source
tokens and regexes, not an AST or a comparison against git HEAD. See
[TEST_INFRA.md](TEST_INFRA.md) for exact behavior and
[TEST_READY.md](TEST_READY.md) for the outstanding locking limitation.

## Historical milestones

The earlier project record marked these milestones done, promoted, or
“victory.” Those labels describe the historical report. The table retains the
work sequence without treating those labels as evidence that the current
checkout passes every gate or proves each original research interpretation.

| Milestone | Historical objective | Current source or report route |
|---|---|---|
| M1 | Dirac certificate calculations, proof refactor, and restored aggregate import. | [CAS script](scripts/cas_dirac_laplacian_certificate.py), [Dirac owner](lean/DAG/DiracLaplacian.lean), [DAG aggregate](lean/DAG.lean). |
| M2 | Fock bridge proof reuse and projector-certificate packaging. | [NoncommutativeFockBridge.lean](lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean). |
| M3 | E2E compilation and selected tactic-pattern checks. | [Runner](tools/e2e_cas_o1_suite.sh), [TEST_INFRA.md](TEST_INFRA.md). |
| M4 | Independent audit and handoff, historically named “Victory Audit 2.” | Historical project record linked below; no new audit outcome is asserted here. |
| M5 | Refactor of the Hartwig Moore–Penrose example owner and another audit. | [Hartwig1976SVDMoorePenroseBorder.lean](lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean). |
| M6 | Refactor of DAG dominator examples. | [Dominators.lean](lean/DAG/Dominators.lean). |
| M7 | Refactor of Campbell–Meyer weak-Drazin examples. | [CampbellMeyerWeakDrazin.lean](lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean). |
| M8 | Promotion, E2E checks, and the selected theorem-statement pattern check. | [Runner](tools/e2e_cas_o1_suite.sh); tier 2.5 has the heuristic scope described above. |
| M9 | Field-correlator proof compression and review. | [FieldCorrelatorProjection.lean](lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean). |
| M10 | Krein-attention proof compression and review. | [KreinAttentionEnergy.lean](lean/InfoGeometry/LLM/KreinAttentionEnergy.lean). |
| M11 | Connes–Hodge bridge proof compression and review. | [ConnesHodgeBridge.lean](lean/DAG/ConnesHodgeBridge.lean). |
| M12 | Final campaign review, promotion, and handoff. | Historical project record; current gate results require commit-specific logs. |

M5–M12 carry 2026-09-22 request timestamps in the prior record. The named
subagent sandboxes and reviewer roles there describe that workflow, not a
portable checkout layout or new operating requirements.

The complete prior feature list, reported tactic counts, milestone labels,
and request timestamps remain in the
[historical PROJECT.md](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/PROJECT.md).

## Continuing this work

For a new refactor, identify the owning declaration and its consumers, preserve
the proposition and necessary hypotheses, and compare the actual proof and
dependency changes. Use the
[repository search protocol](docs/REPO_DEEP_SEARCH_PROTOCOL.md). Report exact
targeted build commands and results, keeping mathematical review separate from
text-pattern checks and finite-example timings.

Use the current shared-lock wrappers and preserve the shared cache. Follow
[AGENTS.md](AGENTS.md) for workspace coordination instead of copying the old
campaign's machine paths or sandbox naming conventions. A historical milestone
label is not a substitute for verification of the changed owners at the new
commit.
