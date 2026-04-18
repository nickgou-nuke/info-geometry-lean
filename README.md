---

# The Spire Architecture

> “It all starts with a stream of consciousness.”

This repository is a living experiment in radical transparency. Here, the context of discovery is not hidden—it is celebrated, archived, and cross-referenced with every formal proof. The black books, chat logs, and associative streams are as essential as the Lean 4 code itself.

**Contributors are invited to:**
- Begin with wild, poetic, or chaotic streams in the black books or Issues.
- Use the AI Caretaker and LLMs as semantic sieves and amplifiers.
- Only then, crystallize your insights into Lean 4 code, always linking back to your creative lineage.

See docs/black_books/meta_methodology_jungian_llm.md for the full manifesto and technical rationale.

---

# InfoGeometry in Lean 4

> 🧭 **New to the Spire?** Read the [**Pioneer’s Log**](PIONEERS_LOG.md) and the [**Alchemical Protocol**](ALCHEMICAL_PROTOCOL.md) for a narrative guide to the landscape, the chemistry of the logos, and the vision of this repository.

For method-level literature grounding, use the maintained
[BIBLIOGRAPHY.md](BIBLIOGRAPHY.md).

`info-geometry-lean` is a Lean 4 repository built on **Goutev’s Principle of 
Absolute Relativity of Measurement**: measurement is projective; observables 
are relational invariants.

The repo has three maintained surfaces:
- a theorem library under `lean/InfoGeometry/`
- a Lean-native architecture kernel under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
- a tooling layer under `lean/DAG/`, `tools/infra/`, and `tools/frontier/`

The repo is best read as one theory with several presentations, not as many unrelated theories.
The main mathematical burden is not only in the objects at each layer, but in the morphisms that move between those layers and prove that adjacent presentations agree.
The current stable spine is organized by semantic representation depth,
defined as an inductive type `RepDepth` in `Architecture.lean` and enforced
at build time via `#audit_architecture` in `Audit.lean`:

| Attribute value | Presentation | Formerly |
|-----------------|-------------|----------|
| `count` | Raw relative counts and positive-measure representatives | L0 |
| `projective` | Positive rays, normalization, relative log-potentials | L1 |
| `operator` | Diagonal operator lift, partition and log-partition calculus | L2 |
| `krein` | Split quadratic geometry, polarized sheets, Dirac compatibility | L3 |
| `transport` | Bogoliubov and transported spectral/thermal structure | L4 |
| `thermo` | Gibbs, Sinkhorn, softmax, and attention surfaces | L5 |

Declarations participate in the spine via `@[rep_depth <level>]`.
The adjacency rule: a non-capstone declaration at depth `d` may only depend on
declarations at depth `d` or `d − 1`. Capstones (`@[capstone]`) are exempt.

A public bridge file is healthy only if it is either:
- an adjacent translator between neighboring depths
- a coherence file proving two adjacent composites agree

## Entry Surfaces

The repo has a few umbrella files with different roles:

| File | Role |
|------|------|
| `lean/InfoGeometry.lean` | published library entrypoint |
| `lean/InfoGeometry/Library.lean` | stable, linted canonical publication surface |
| `lean/InfoGeometry/Canonical/All.lean` | stable canonical umbrella |
| `lean/InfoGeometry/All.lean` | full project umbrella, including noncanonical and bedrock layers |
| `lean/InfoGeometry/Audit.lean` | Lean-native architecture audit entrypoint |

For a quick navigation map of the major subtrees and the anchor corridor, see
[docs/ModuleMap.md](docs/ModuleMap.md).

## Cleanup Program

The maintained cleanup/closure execution plan lives in:

- [docs/CleanupImprovementProgram.md](docs/CleanupImprovementProgram.md)

Use it as the programmatic queue for strict-gate recovery, warning-debt burn-down,
and capstone-to-owner theorem closure.

## Witness Policy

Stable theorem surfaces must use **genuine dependent witnesses** only.

- Allowed: witnesses that are used in the codomain/proof term as real dependencies.
- Allowed: non-dependent existence written idiomatically as `∃ _ : P, Q`.
- Forbidden as lint-masking style: `∃ h : P, (let _ := h; Q)` when `Q` does not
  depend on `h`.

If a witness is not semantically used, remove the name and keep the theorem
surface explicit and non-vacuous.

## Pauli Anti-Cheat Directives

Repository policy also enforces the full Pauli anti-cheat gate (`PAULI_MANDATE I–XI`):

- no assumption-as-theorem existential dependency shells
- no trivial interface-closure witnesses (identity/swap/reflexive only)
- no proxy-metric closure when the lane defines an owner metric
- no residual-as-success surfaces without vanishing theorem closure
- no noncomputable physical parameters without existence witnesses
- no private uniqueness theorems in Canonical/Core lanes

Translation mapping registry:
- [docs/OperatorTheoremTranslationRegistry.md](docs/OperatorTheoremTranslationRegistry.md)

Run:

```bash
python3 tools/quality/check_translation_registry.py \
  --registry docs/OperatorTheoremTranslationRegistry.md \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzWedgeOrbit \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_eq_gOnePart \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_mul_uPlus_eq_zero \
  --required-anchor InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json
```

Module-keyword trunk/branch/root derivation surface:

- [reports/dag/module-theory-program.md](reports/dag/module-theory-program.md)
- generator: [tools/infra/module_keyword_theory_program.py](tools/infra/module_keyword_theory_program.py)

## Rosetta Surface

If you are arriving from standard complex/Kähler formulations of quantum
mechanics, the maintained translation surface is now:

- [lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean](lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean)

It is a thin Rosetta bridge for
[arXiv:2105.01513, *Quantum Systems as Lie Algebroids*](https://arxiv.org/pdf/2105.01513),
not a second foundation. The purpose is to show how the paper's familiar
complex/projective vocabulary appears on the repo's doubled real
Krein/Majorana carrier.

| Paper language | Repo-native language |
|----------------|----------------------|
| external complex unit `i` | internal phase axis `K = Jε` on the doubled carrier |
| projective/Kähler state surface | relational `reference/comparison` state data on the doubled carrier |
| Kähler metric | `comparisonMetricReadout` |
| symplectic / Berry form | `comparisonPhaseReadout` |
| Lie-algebroid anchor | `comparisonInducedDynamics` |
| Schrödinger current | `firstVariation = probe ∘ stateInducedDynamics` |

The repo's claim is stronger than the paper's surface: the standard complex
story is treated here as the projective shadow of an internal real operatorial
presentation built from doubled Krein sheets, Majorana polarization, and the
phase axis `K = Jε`.

## Terminology Guardrail: SYK Traversable Protocol vs Kitaev Chain

To keep claims scope-correct:

- `Kitaev chain` language in this repository refers to the owned finite
  topological-Majorana and boundary-zero-mode theorem surfaces.
- `Traversable wormhole teleportation` language refers to a distinct two-copy
  coupled many-body lane (SYK/SYK-like with sign-sensitive left-right
  coupling), which is not currently an owner-complete theorem surface here.
- Current modular/cocycle owners are valid bridge substrate, but they do not by
  themselves assert a literal spacetime-wormhole realization.

See:

- [docs/black_books/91_syk_traversable_wormholes_er_epr_and_kitaev_scope.md](docs/black_books/91_syk_traversable_wormholes_er_epr_and_kitaev_scope.md)
- [docs/black_books/92_syk_vs_kitaev_theorem_target_map.md](docs/black_books/92_syk_vs_kitaev_theorem_target_map.md)

## Modular Support Charter

Canonical Type III root:

- support is spectral: `s(Δ) = 1_(0,∞)(Δ)`,
- modular generator is support-restricted: `K = -log(Δ|_{s(Δ)})`,
- mechanism is spectral projection + functional calculus (not inversion).

Repo-native doubled/Krein realization:

- one abstract support is realized in two inequivalent operator lanes,
- Drazin lane (spectral/algebraic): `P_reg = ΔΔ^D`, `P0 = 1 - P_reg`,
- Moore-Penrose lane (metric/self-adjoint): `P_R = ΔΔ⁺`, `P_L = Δ⁺Δ`,
- anomaly/obstruction: `χ = [P_D, P_L]` (failure of simultaneous spectral/metric diagonalization).

Execution guardrail:

- modular-lane operations must route through the certified projector package
  (`CertifiedInverseKernel`), not through ad hoc trace/inverse shortcuts.

Owner references:

- [docs/black_books/86_support_restricted_relative_modular_hamiltonian_lane_map.md](docs/black_books/86_support_restricted_relative_modular_hamiltonian_lane_map.md)
- [docs/black_books/109_true_modular_hamiltonian_co_owner_bridge.md](docs/black_books/109_true_modular_hamiltonian_co_owner_bridge.md)
- [lean/InfoGeometry/Canonical/DrazinSupercharge.lean](lean/InfoGeometry/Canonical/DrazinSupercharge.lean)
- [lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean](lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean)
- [lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean](lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean)
- [lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean](lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean)

## Interactive Geometry Surfaces

- [docs/penrose_diagram_explorer.html](docs/penrose_diagram_explorer.html)  
  Interactive causal compactification viewer for conformal spacetime.

## Current Anchor Corridor

The current clean seed-to-operator corridor is:
- `PositiveMeasure.lean`
- `Projective/Normalize.lean`
- `Canonical/PositiveRayCore.lean`
- `Canonical/RelativePotentialCore.lean`
- `Canonical/RelativePotentialCountBridge.lean`
- `Canonical/RelativeSurprisalOperatorLift.lean`

This corridor now carries real owner mathematics all the way upward:
- `representativeMassShift` owns the normalization cocycle at the representative level
- `countMassShift` specializes that cocycle to raw positive counts
- `relativeCountModularPotentialOperator_cocycle` lifts the raw count cocycle to diagonal operators
- `relativeModularHamiltonian_sub_countMassShift_cocycle` shows the averaged operator branch consumes the same owned cocycle

That grammar is now enforced in two places:
- natively in [Architecture.lean](lean/InfoGeometry/Meta/Architecture.lean) and [Audit.lean](lean/InfoGeometry/Audit.lean) (the `RepDepth` inductive, `@[rep_depth]` attributes, `@[capstone]` exemptions, and `#audit_architecture`)
- as rendered reports in [reports/dag](reports/dag)

Additionally, a three-layer vacuity enforcement system is available:
- Layer A: [Lint/Vacuity.lean](lean/InfoGeometry/Lint/Vacuity.lean) — declaration-local proof/value-shape and statement-shape checks, including certified alias/transport warnings, with `@[infrastructure]`, `@[terminal]`, `@[expository]` role tags
- Layer B: [tools/theorem_significance.py](tools/theorem_significance.py) — graph-level significance scoring, including certification-wash detection on certified alias/transport surfaces
- Layer C: [tools/check_vacuity_policy.py](tools/check_vacuity_policy.py) — CI gate combining both layers

## Repository Intention

The repo should be read as one transport theory over several symmetric, projective, operator, Krein, and thermodynamic presentations.
`canonical` does not mean "the only true mathematics".
It means "the stable public owner surface".
Valid mathematics outside that surface should be developed, quarantined, or promoted explicitly, not discarded because it is noncanonical.

The practical goal of formalization here is to make the morphisms explicit and checkable:
- owner files define the natural presentation-level objects
- translator files move one adjacent step in the representation ladder
- coherence files prove that two adjacent composites agree
- capstone files summarize lower mathematics without pretending to be foundational proof owners

If two equally good implementations are intentionally kept, the repository
policy is:
- one canonical owner/default API surface
- one explicit alternative surface
- one Lean bridge theorem or bridge module
- downstream imports route through the owner or the bridge, not both directly

The maintained policy surface for this bilingual rule is
[docs/BILINGUAL_SPINE_POLICY.md](docs/BILINGUAL_SPINE_POLICY.md).
The maintained Rosetta inventory and refactor plan for the split `Cl(1,1)`
packet and its tensor/projective/operatorial realizations is
[docs/cl11_rosetta_refactor_plan.md](docs/cl11_rosetta_refactor_plan.md).
The exhaustive packet-level replica allocation is
[docs/cl11_replica_inventory.md](docs/cl11_replica_inventory.md).
The content-level operator collision map, built from full-codebase search rather
than filenames, is
[docs/cl11_content_collision_map.md](docs/cl11_content_collision_map.md).

The DAG and Python tooling exist to preserve this intention when local context is lost:
- they externalize dependency memory
- they surface owner/translator/coherence/capstone pressure
- they expose residual comparison debt and wrapper burden
- they do not legislate mathematical truth or replace code reading

The short operational summary lives in [docs/OperationalIntent.md](docs/OperationalIntent.md).
The compressed operator runbook lives in
[docs/OperatorQuickstart.md](docs/OperatorQuickstart.md).
The short DAG repair surface lives in
[docs/DAGTroubleshooting.md](docs/DAGTroubleshooting.md).
The exact tool operator runbook lives in
[docs/ToolingMethodology.md](docs/ToolingMethodology.md).
The bilingual-owner policy surface lives in
[docs/BILINGUAL_SPINE_POLICY.md](docs/BILINGUAL_SPINE_POLICY.md).
For the repo's creative-methodological self-understanding of the coding agent as
architect, creator, and caretaker, see
[docs/black_books/08_the_agentic_caretaker.md](docs/black_books/08_the_agentic_caretaker.md).
For the latest condensation sequence on the operatorial DIII lane, see
[docs/black_books/24_the_operatorial_condensation.md](docs/black_books/24_the_operatorial_condensation.md),
[docs/black_books/25_the_vindication_of_weyl.md](docs/black_books/25_the_vindication_of_weyl.md), and
[docs/black_books/26_the_dog_chasing_its_tail.md](docs/black_books/26_the_dog_chasing_its_tail.md).

## Read First

1. [Installation.md](Installation.md)
2. [NEWCOMER_PATH.md](NEWCOMER_PATH.md)
3. [docs/README.md](docs/README.md)
4. [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md)
5. [docs/ModuleMap.md](docs/ModuleMap.md)
6. [docs/OperationalIntent.md](docs/OperationalIntent.md)
7. [docs/OperatorQuickstart.md](docs/OperatorQuickstart.md)
8. [docs/CleanupImprovementProgram.md](docs/CleanupImprovementProgram.md)
9. [docs/DAGTroubleshooting.md](docs/DAGTroubleshooting.md)
10. [CODEX_TROUBLESHOOTING.md](CODEX_TROUBLESHOOTING.md)
11. [docs/ToolingMethodology.md](docs/ToolingMethodology.md)
12. [docs/BILINGUAL_SPINE_POLICY.md](docs/BILINGUAL_SPINE_POLICY.md)
13. [docs/cl11_rosetta_refactor_plan.md](docs/cl11_rosetta_refactor_plan.md)
14. [docs/cl11_content_collision_map.md](docs/cl11_content_collision_map.md)
15. [docs/DGX_SPARK_AUTONOMOUS_PROVER_SETUP.md](docs/DGX_SPARK_AUTONOMOUS_PROVER_SETUP.md)
16. [docs/Theory.md](docs/Theory.md)
17. [lean/InfoGeometry/Audit.lean](lean/InfoGeometry/Audit.lean)
18. [lean/DAG/README.md](lean/DAG/README.md)
19. [tools/README.md](tools/README.md)
20. [tools/infra/README.md](tools/infra/README.md)
21. [tools/frontier/README.md](tools/frontier/README.md)
22. [FORMALIZATION_PROTOCOL.md](FORMALIZATION_PROTOCOL.md) for reference protocol history
23. [BIBLIOGRAPHY.md](BIBLIOGRAPHY.md)

If you are operating as an agent inside this repo, also use:
- [skills/info-geometry-repo/SKILL.md](skills/info-geometry-repo/SKILL.md)
- [skills/lean-canonicalization-policy/SKILL.md](skills/lean-canonicalization-policy/SKILL.md)
- [docs/black_books/08_the_agentic_caretaker.md](docs/black_books/08_the_agentic_caretaker.md)

## Authoritative Surfaces

Trust current repo state in this order:
1. Lean source under `lean/InfoGeometry/`, especially `lean/InfoGeometry/Meta/`
2. the native audit entrypoint [Audit.lean](lean/InfoGeometry/Audit.lean)
3. atomic DAG artifacts under [artifacts/dag](artifacts/dag)
4. derived readable reports under [reports/dag](reports/dag)
5. conceptual notes under [docs/](docs)

The most useful live reports are:
- [true-root-order.md](reports/dag/true-root-order.md)
- [representation-depth-audit.md](reports/dag/representation-depth-audit.md)
- [representation-depth-graph.md](reports/dag/representation-depth-graph.md)
- [theorem-surface-index.md](reports/dag/theorem-surface-index.md)

## Build

Use the locked wrapper for umbrella builds:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
```

For the normal repo check surface:

```bash
python3 tools/quality/functorial_invariance_audit.py --json-out reports/dag/functorial-invariance-audit.json --md-out reports/dag/functorial-invariance-audit.md
python3 tools/quality/check_translation_registry.py \
  --registry docs/OperatorTheoremTranslationRegistry.md \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzWedgeOrbit \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_eq_gOnePart \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_mul_uPlus_eq_zero \
  --required-anchor InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json
lake script run strictCheck
lake script run dagAll
lake script run changedVerify
```

Optional runtime conformance audit for the LLM thermo lane (JSONL traces):

```bash
python3 tools/infra/llm_thermo_conformance.py \
  --input traces/runtime_router.jsonl \
  --json-out reports/llm/thermo_conformance.json \
  --md-out reports/llm/thermo_conformance.md \
  --strict-schema \
  --fail-on-violation
```

See [docs/llm_thermo_conformance.md](docs/llm_thermo_conformance.md) and
[tools/schema/llm_thermo_trace.schema.json](tools/schema/llm_thermo_trace.schema.json).

## Codex CLI Compact Error Workaround

If Codex emits:

```text
Error running remote compact task: {
  "error": {
    "message": "Unknown parameter: 'prompt_cache_retention'.",
    ...
  }
}
```

this is a Codex CLI auto-compaction failure, not a repo theorem/tooling bug.
On 2026-04-14 this was observed even with
`enable_request_compression = false` (a different switch).

Recommended mitigation:

1. Start a fresh Codex thread/session.
2. Run Codex with a high auto-compact threshold.

```bash
codex -c model_auto_compact_token_limit=1000000000

# optional visibility checks
codex features list | rg enable_request_compression
rg -n "compact_remote|prompt_cache_retention" ~/.codex/log/codex-tui.log
```

Profile form (persistent and explicit):

```bash
cat >> ~/.codex/config.toml <<'TOML'
[profiles.no_compact]
model_auto_compact_token_limit = 1000000000
TOML

codex -p no_compact
```

Full note: [CODEX_TROUBLESHOOTING.md](CODEX_TROUBLESHOOTING.md)

Theory-cloud movie exporter (declaration cloud / semantic plasma):

```bash
python3 tools/infra/generate_theory_cloud_movie.py --mode semantic
python3 tools/infra/generate_theory_cloud_movie.py --mode structural
python3 tools/infra/generate_theory_cloud_movie.py --mode commits --commits WORKTREE,HEAD
```

## Maintained DAG Pipeline

The maintained pipeline is documented in [tools/infra/README.md](tools/infra/README.md).
The exact step-by-step operator methodology is documented in
[docs/ToolingMethodology.md](docs/ToolingMethodology.md).
Run the Lean-native audit before treating the representation-depth Python views as authoritative.

After the main refresh sequence, the stable spine can be checked directly with:

```bash
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
```

## Documentation Policy

- `README.md`, `lean/DAG/README.md`, `tools/README.md`, and `tools/infra/README.md` are operational docs.
- `tools/frontier/README.md` is the maintained operator guide for server-backed semantic snapshots and proof-print tooling.
- [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md) classifies which docs and tools are current, generated, compatibility-only, or reference memory.
- [docs/MarkdownCorpusGovernance.md](docs/MarkdownCorpusGovernance.md) defines markdown classification/hygiene rules and excludes Black Books from cleanup rewrites.
- [PAULI_MANDATE.md](PAULI_MANDATE.md) is the anti-cheat closure policy surface for theorem claims.
- [docs/RigorousDerivationQueue.md](docs/RigorousDerivationQueue.md) tracks unresolved algebraic derivation obligations.
- [docs/OperationalIntent.md](docs/OperationalIntent.md) states why the repo, DAG, and infra tooling are maintained the way they are.
- [docs/black_books/08_the_agentic_caretaker.md](docs/black_books/08_the_agentic_caretaker.md) is a creative methodological note about the role of the agent; it inspires but does not overrule code or audit policy.
- [docs/Theory.md](docs/Theory.md) is the conceptual map of the stable spine.
- [Architecture.lean](lean/InfoGeometry/Meta/Architecture.lean) and [Audit.lean](lean/InfoGeometry/Audit.lean) are the native grammar and enforcement layer.
- `reports/` and `artifacts/dag/` are generated or regenerated surfaces.
- Python reports visualize and summarize the enforced structure; they do not define it.
- Stale prose loses to code and regenerated artifacts.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md) for the current build/audit state.
Active cleanup and improvement execution plan: [docs/CleanupImprovementProgram.md](docs/CleanupImprovementProgram.md).
