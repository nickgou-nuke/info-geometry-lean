# Documentation Map

This directory is mixed:

- a small set of hand-maintained operational docs
- a larger set of conceptual, synthesis, backlog, and reference-memory notes
- one generated doc surface under `docs/auto/`

Lean source is still the truth surface. These docs exist to help orientation, not to override code.

The maintained operational framing is:
- the Lean corpus is the validation surface
- theorem-graph and audit tooling are navigation and closure infrastructure, not proof
- exploratory archives and black-book material are theorem-candidate substrate, not authoritative theorem surfaces
- unresolved claims should appear either as proof-carrying Lean contexts or as explicit closure debt

## Foundational Theory

The repository's core theoretical axiom is **Goutev’s Principle of Absolute 
Relativity of Measurement**:

- [Goutevs_Principle.md](Goutevs_Principle.md) — The formal manifesto.
- [LIBER_NOVUS_MATH.md](LIBER_NOVUS_MATH.md) — Methodology for exploratory-to-formal mathematical development.
- [WORKBENCH.md](WORKBENCH.md) — Practical playbook for Socratic exploration and formal handoff.
- [OperatorTheoremTranslationRegistry.md](OperatorTheoremTranslationRegistry.md) — One-to-one translation registry from external theorem surfaces to doubled-real operator-native Lean anchors.
- [NameEquivalenceRegistry.md](NameEquivalenceRegistry.md) — Curated alias/equivalence registry merged into the maintained equivalence dictionary.
- [black_books/](black_books/) — The "Black Books": exploratory source material and theorem-candidate substrate. Useful for discovery and translation, but not proof.
- [black_books/08_the_agentic_caretaker.md](black_books/08_the_agentic_caretaker.md) — Essay on the repository agent's exploratory and caretaker role under kernel authority.
- [black_books/09_science_after_coding.md](black_books/09_science_after_coding.md) — Essay on dialogue-driven exploration, distillation, and formal handoff to Lean.
- [black_books/18_multilingual_logos_pauli_jung.md](black_books/18_multilingual_logos_pauli_jung.md) — Chapter on multilingual docstrings, exploratory generation, and closure discipline.
- [black_books/24_the_operatorial_condensation.md](black_books/24_the_operatorial_condensation.md) — The phase-transition chapter where operatorial closure supersedes manifold-first narration.
- [black_books/25_the_vindication_of_weyl.md](black_books/25_the_vindication_of_weyl.md) — The ray-first reformulation tying gauge/curvature/anomaly to compiled closure lanes.
- [black_books/26_the_dog_chasing_its_tail.md](black_books/26_the_dog_chasing_its_tail.md) — The mass-as-coupling and localized-vortex witness chapter on the DIII lane.
- [black_books/52_kramers_pairs_krein_majorana_type_iii_lightcone.md](black_books/52_kramers_pairs_krein_majorana_type_iii_lightcone.md) — External-science synthesis chapter for Kramers/Krein/Majorana/Type-III/apex language.
- [black_books/52native_krein_hestenes_real_doubled_translation.md](black_books/52native_krein_hestenes_real_doubled_translation.md) — Repo-native doubled-real translation of chapter 52.
- [black_books/55_external_approval_real_all_translation.md](black_books/55_external_approval_real_all_translation.md) — Active roadmap for real modular/type-III closure in owned canonical files.
- [black_books/90_burg_stein_spectral_shadow_of_log_det_rn_lane.md](black_books/90_burg_stein_spectral_shadow_of_log_det_rn_lane.md) — Finite-dimensional Burg/Stein spectral closure of the log-det RN/Connes lane, with theorem anchors.
- [black_books/91_first_quantization_of_probability_dictionary.md](black_books/91_first_quantization_of_probability_dictionary.md) — Compiled density-ratio/surprisal/expectation substitution dictionary (`λ -> Δ`, `-log λ -> K`, expectation pairing).
- [black_books/93_typeiii_operator_owner_queue.md](black_books/93_typeiii_operator_owner_queue.md) — Build-ordered Type III operator owner queue, including the new Pedersen–Takesaki interface lane and next owner targets.
- [black_books/94_logdet_burg_modular_hamiltonians.md](black_books/94_logdet_burg_modular_hamiltonians.md) — SPD Burg/Stein owner lane (`tr - log det - n`) and its strict bridge boundary toward modular Hamiltonian/Type III lanes.
- [black_books/95_penrose_twistors_geometry_of_infinity.md](black_books/95_penrose_twistors_geometry_of_infinity.md) — Twistor/conformal compactification synthesis: projective incidence, infinity twistor as metric selector, and Penrose-diagram causal compactification.
- [black_books/96_operational_penrose_surfaces_for_a_research_repository.md](black_books/96_operational_penrose_surfaces_for_a_research_repository.md) — Operational Penrose-diagram correctness contract: model semantics, causal trichotomy, boundary components, and interaction-grade invariants.
- [black_books/97_signed_particle_representation_wigner_monte_carlo.md](black_books/97_signed_particle_representation_wigner_monte_carlo.md) — Signed-particle quantum mechanics summary (Wigner phase-space, SPMC postulates, source/annihilation mechanism, and application lanes).
- [black_books/98_signed_particle_reinterpretation_krein_modular_bridge.md](black_books/98_signed_particle_reinterpretation_krein_modular_bridge.md) — Structural reinterpretation of signed-particle Wigner mechanics as a Krein/modular projector-shadow bridge.
- [black_books/99_multiple_representations_of_one_information_geometric_reality.md](black_books/99_multiple_representations_of_one_information_geometric_reality.md) — Multi-representation taxonomy chapter across Hilbert/projective/Wigner/hydrodynamic/stochastic/Krein/conformal lanes with strict equivalence-vs-analogy guardrails.
- [black_books/102_fractal_cantor_graph_metric_clifford_theorem_target_map.md](black_books/102_fractal_cantor_graph_metric_clifford_theorem_target_map.md) — Translator/intake charter for Cantor/fractal + Clifford + graph-metric research, with theorem-target map and strict Pauli guardrails.
- [black_books/103_the_redline_of_knowledge_processing_and_the_higher_category_spine.md](black_books/103_the_redline_of_knowledge_processing_and_the_higher_category_spine.md) — Structural homology doctrine and redline pipeline (plural exploration, singular closure, kernel-gated memory residue).
- [black_books/104_higher_categorical_view_practical_two_categorical_skeleton.md](black_books/104_higher_categorical_view_practical_two_categorical_skeleton.md) — Practical higher-categorical framing of objects/morphisms/coherence across physics, LLM, research packets, and proof closure.
- [black_books/105_math_behind_physics_inspired_routing_llm_architecture.md](black_books/105_math_behind_physics_inspired_routing_llm_architecture.md) — Mathematical substantiation of the physics-inspired routing spine (sparse MoE optimization, graph transport, Clifford lane split, fractal sparsity, and typed coherence).
- [black_books/106_architectural_symmetries_from_spectral_regularization_to_causal_compactification.md](black_books/106_architectural_symmetries_from_spectral_regularization_to_causal_compactification.md) — Unified operator/geometric compactification chapter linking Drazin spectral regularization, Lean functional calculus admissibility, twistor infinity structures, and the Operator Penrose Analogue.
- [black_books/107_operator_penrose_analogue_repo_native_krein_doubled_hestenes.md](black_books/107_operator_penrose_analogue_repo_native_krein_doubled_hestenes.md) — Repo-native translation of the Operator Penrose Analogue into doubled real/Krein/Hestenes owner language (projector package, support-restricted log lane, and closure guardrails).
- [black_books/108_unbounded_modular_machinery_repo_native_translation.md](black_books/108_unbounded_modular_machinery_repo_native_translation.md) — Unbounded modular translation chapter: affiliated `Δ`, spectral support, support-restricted unbounded `-log Δ`, and the bridge obligations between canonical and surrogate projector lanes.
- [black_books/108_unbounded_modular_translation_queue_for_operator_penrose_unification.md](black_books/108_unbounded_modular_translation_queue_for_operator_penrose_unification.md) — Queue-style theorem-target chapter for the unbounded modular/operator-Penrose unification lane.
- [black_books/109_true_modular_hamiltonian_co_owner_bridge.md](black_books/109_true_modular_hamiltonian_co_owner_bridge.md) — Co-owner bridge charter: keep `K = -log Δ` as owner meaning and prove doubled/Krein/Hestenes equality forms by theorem.
- [black_books/110_spectroscopic_multimodal_reconstruction_doctrine.md](black_books/110_spectroscopic_multimodal_reconstruction_doctrine.md) — Spectroscopic reconstruction doctrine: presentations as probing channels, coherence as cross-modality calibration, and obstructions as line splitting.
- [black_books/111_spectroscopic_audit_pipeline_and_gauge_vacuum.md](black_books/111_spectroscopic_audit_pipeline_and_gauge_vacuum.md) — Spectroscopic audit dictionary and formal reference-state/gauge framing for owner, translator, coherence, and obstruction lanes.
- [black_books/112_digital_spectrometer_formalization_epistemology.md](black_books/112_digital_spectrometer_formalization_epistemology.md) — Digital-spectrometer formalization doctrine: invariant response identity, pipeline vocabulary, and lane-local vacuum/gauge semantics.
- [black_books/113_reference_state_and_gauge_in_informational_supergravity.md](black_books/113_reference_state_and_gauge_in_informational_supergravity.md) — Reference-state and gauge closure doctrine for informational-supergravity lanes: engineered vacuum, representational frame, and invariance/obstruction discipline.
- [black_books/130_oracle_vs_socratic_ai_discovery_pressure.md](black_books/130_oracle_vs_socratic_ai_discovery_pressure.md) — Governance doctrine distinguishing exploratory Socratic pressure from kernel-closure authority.
- [black_books/131_the_transmutation_of_the_complex_mask.md](black_books/131_the_transmutation_of_the_complex_mask.md) — Paradigm-shift chapter translating complex-field theorem language into doubled-real Krein/Hestenes operator language.
- [black_books/112_considering_alignment_reference_state_gauge_and_digital_spectrometer.md](black_books/112_considering_alignment_reference_state_gauge_and_digital_spectrometer.md) — Alignment chapter formalizing reference state, gauge transforms, doubled response spectra, and the repo as a digital spectrometer with kernel-gated closure.
- [black_books/67_the_external_analogy_doctrine.md](black_books/67_the_external_analogy_doctrine.md) — Respect external frameworks as heuristics, but keep canonical truth strictly owner-native and Lean-verified.
- [Theory.md](Theory.md) — How the principle maps to the repo presentations.
- [Theory_Highway_Prognosis.md](Theory_Highway_Prognosis.md) — The project's roadmap and trajectory.
- [SEMANTIC_POTENTIAL.md](SEMANTIC_POTENTIAL.md) — Multi-agent exploratory generation surface.

## Modular Support Charter

For modular/support-sensitive work (especially Type III-facing lanes), use the
dual-projector owner package as the execution surface:

- [black_books/94_logdet_burg_modular_hamiltonians.md](black_books/94_logdet_burg_modular_hamiltonians.md) — Charter narrative and guardrails (`Δ`-first, support-restricted log lane).
- [lean/InfoGeometry/Canonical/MoorePenrose.lean](../lean/InfoGeometry/Canonical/MoorePenrose.lean) — Metric/self-adjoint projector lane and spectral-vs-metric anomaly surface.
- [lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean](../lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean) — Unified projector/anomaly kernel routed by downstream modules.
- [lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean](../lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean) — Drazin regular/defect projector algebra and Krein compatibility transport.
- [lean/InfoGeometry/Canonical/DrazinSupercharge.lean](../lean/InfoGeometry/Canonical/DrazinSupercharge.lean) — Projector-controlled regular restriction and support package theorems.
- [lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean](../lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean) — Theorem-level co-owner bridge from Tomita/relative modular owner surfaces to doubled real/Krein/Hestenes presentation.
- [lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean](../lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean) — Support-restricted regular-core bridge package for modular Hamiltonian surfaces on `Preg`.
- [lean/InfoGeometry/Canonical/SpectroscopicGauge.lean](../lean/InfoGeometry/Canonical/SpectroscopicGauge.lean) — Translator/coherence scaffold for gauge-relative response packets (`PotentialDatum` + analyzer + probe) and obstruction/anomaly readouts.
- [lean/InfoGeometry/Canonical/SpectroscopicGaugeKMSBridge.lean](../lean/InfoGeometry/Canonical/SpectroscopicGaugeKMSBridge.lean) — Downstream compatibility bridge tying spectroscopic gauges to the owned `Dynamics.UnruhKMS` modular-flow lane (without rerooting KMS ownerhood).

Guardrail: modular-lane operations should route through this package rather than
raw textbook support narration.

## What Is Current

Use these first when you want the current repo state:

The practical entry stack is:
- [README.md](../README.md) for the formal architecture and validation workflow
- [NEWCOMER_PATH.md](../NEWCOMER_PATH.md) for the shortest technical route into the repo
- [OperationalIntent.md](OperationalIntent.md) for the representation ladder and current live trunks
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md) for trust order and documentation status

- [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
- [CleanupImprovementProgram.md](CleanupImprovementProgram.md)
- [reports/pauli-seal-audit.json](../reports/pauli-seal-audit.json) — Mandatory Pauli-seal gate output (anti-mask, connectivity, axiom-surface, density, anti-trivial-unification).
- [reports/dag/functorial-invariance-audit.md](../reports/dag/functorial-invariance-audit.md) — Mandatory Core-to-canopy functorial reachability and isomorphism corridor audit.
- [reports/dag/module-theory-program.md](../reports/dag/module-theory-program.md) — Module-keyword trunk/branch/root synthesis report with literature context + theorem packets.
- [tools/infra/module_keyword_theory_program.py](../tools/infra/module_keyword_theory_program.py) — Programmatic module-keyword extractor and theorem-packet generator.
- [README.md](../README.md)
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [OperationalIntent.md](OperationalIntent.md)
- [OperatorQuickstart.md](OperatorQuickstart.md)
- [MarkdownCorpusGovernance.md](MarkdownCorpusGovernance.md)
- [ClosureDebtLedger.md](ClosureDebtLedger.md)
- [LOCAL_TOOLCHAIN_ARCHITECTURE.md](LOCAL_TOOLCHAIN_ARCHITECTURE.md)
- [information_symmetry_breaking_explorer.html](information_symmetry_breaking_explorer.html) — Interactive Cartan \(k/p\) phase explorer for defect excitation and Sinkhorn damping trajectories.
- [DAGTroubleshooting.md](DAGTroubleshooting.md)
- [CODEX_TROUBLESHOOTING.md](../CODEX_TROUBLESHOOTING.md)
- [BILINGUAL_SPINE_POLICY.md](BILINGUAL_SPINE_POLICY.md)
- [cl11_rosetta_refactor_plan.md](cl11_rosetta_refactor_plan.md)
- [cl11_replica_inventory.md](cl11_replica_inventory.md)
- [cl11_content_collision_map.md](cl11_content_collision_map.md)
- [AGENTIC_HANDOVER_POLICY_2026-04-15.md](AGENTIC_HANDOVER_POLICY_2026-04-15.md)
- [AGENTIC_PERSONAS_2026-04-15.md](AGENTIC_PERSONAS_2026-04-15.md)
- [DGX_SPARK_AUTONOMOUS_PROVER_SETUP.md](DGX_SPARK_AUTONOMOUS_PROVER_SETUP.md)
- [tools/prompts/agentic_handover_policy_2026-04-15.md](../tools/prompts/agentic_handover_policy_2026-04-15.md)
- [tools/prompts/agentic_personas_2026-04-15.md](../tools/prompts/agentic_personas_2026-04-15.md)
- [projective_mathlib_canonicalization_plan.md](projective_mathlib_canonicalization_plan.md)
- [ToolingMethodology.md](ToolingMethodology.md)
- [CandidateBridgePacketContract.md](CandidateBridgePacketContract.md)
- [LeanTrail.md](LeanTrail.md)
- [LeanTrailBlueprint.md](LeanTrailBlueprint.md)
- [Theory.md](Theory.md)
- [ModuleMap.md](ModuleMap.md)
- [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
- [lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
- [lean/DAG/README.md](../lean/DAG/README.md)
- [tools/README.md](../tools/README.md)
- [tools/infra/README.md](../tools/infra/README.md)
- [tools/infra/generate_theory_cloud_movie.py](../tools/infra/generate_theory_cloud_movie.py)
- [tools/prompts/agentic_autotheory_prompts_2026-04-15.md](../tools/prompts/agentic_autotheory_prompts_2026-04-15.md)
- [tools/prompts/README.md](../tools/prompts/README.md)
- [../.agents/workflows/README.md](../.agents/workflows/README.md)
- [../artifacts/leantrail/README.md](../artifacts/leantrail/README.md)
- [RigorousDerivationQueue.md](RigorousDerivationQueue.md)

These are the maintained hand-written entry surfaces.

## What Is Generated

Only the following doc surface under `docs/` is script-owned:

- [docs/auto/index.md](auto/index.md)

Its owning scripts are:

- [tools/docs/generate_auto_docs.py](../tools/docs/generate_auto_docs.py)
- [tools/docs/update_repo_docs.py](../tools/docs/update_repo_docs.py)

Related generated artifacts also live under:

- [reports/dag/](../reports/dag/)
- [artifacts/dag/](../artifacts/dag/)
- [artifacts/leantrail/](../artifacts/leantrail/)

Do not hand-edit generated surfaces unless the generator itself is being repaired.

## What Is Reference Memory

Everything else in `docs/` should be treated as reference memory unless this page
or [RepositoryMemoryMap.md](RepositoryMemoryMap.md) explicitly promotes it.

That includes:

- synthesis notes such as `welding_theorem_synthesis.md`, `*_synthesis.md`
- diagnostics and backlog notes such as `analytic_closure_backlog.md` and `apex_*.md`
- active closure trackers such as
  `krein_hestenes_closure_tracker_2026-04-13.md` and
  `active_closure/kramers_krein_modular_tracker.md`
- niche conceptual overlays such as `causal_apex_binding.md`
- future infra blueprints such as `private_reviewer_chat_blueprint.md`
- glossaries and indexes such as `keyword_index.md` and `lawful-flow-glossary.md`
- methodology side-docs such as:
  [CARETAKER_REQUIREMENTS.md](CARETAKER_REQUIREMENTS.md),
  [METHODOLOGY_OF_THE_SPIRE.md](METHODOLOGY_OF_THE_SPIRE.md),
  [RED_BOOK_OF_PASSAGE.md](RED_BOOK_OF_PASSAGE.md),
  and [deep-research-report-1.md](deep-research-report-1.md)

These files can still be useful, but they must be re-audited against Lean source
before being used as live policy.

## Recommended Read Path

For current repo structure:

1. [README.md](../README.md)
2. [CleanupImprovementProgram.md](CleanupImprovementProgram.md)
3. [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
4. [OperationalIntent.md](OperationalIntent.md)
5. [OperatorQuickstart.md](OperatorQuickstart.md)
6. [LOCAL_TOOLCHAIN_ARCHITECTURE.md](LOCAL_TOOLCHAIN_ARCHITECTURE.md)
7. [DAGTroubleshooting.md](DAGTroubleshooting.md)
8. [CODEX_TROUBLESHOOTING.md](../CODEX_TROUBLESHOOTING.md)
9. [BILINGUAL_SPINE_POLICY.md](BILINGUAL_SPINE_POLICY.md)
10. [cl11_rosetta_refactor_plan.md](cl11_rosetta_refactor_plan.md)
11. [ToolingMethodology.md](ToolingMethodology.md)
12. [LeanTrail.md](LeanTrail.md)
13. [DGX_SPARK_AUTONOMOUS_PROVER_SETUP.md](DGX_SPARK_AUTONOMOUS_PROVER_SETUP.md)
14. [Theory.md](Theory.md)
15. [ModuleMap.md](ModuleMap.md)
16. [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
17. [tools/infra/README.md](../tools/infra/README.md)

For the current count/projective/operator trunk:

1. [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
2. [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
3. [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
4. [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
5. [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
6. [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

For the corrected phase-space/generalized-metric trunk:

1. [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
2. [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
3. [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
4. [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)
5. [PhaseSpacePolarizedBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean)
6. [PhaseSpaceRecompositionBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean)

## Rule

If a doc and Lean source disagree, trust Lean source.

## Consistency Pass (2026-04-16)

Repository-wide checks were run across all files under `docs/`:

- markdown links resolve;
- referenced Lean file paths resolve; and
- stale path references were corrected where needed.

Files updated in this pass:

- `docs/CODEBASE_STATUS.md`
- `docs/README.md`
- `docs/RepositoryMemoryMap.md`
- `docs/ModuleMap.md`

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [CODEBASE_STATUS.md](CODEBASE_STATUS.md) for the current build/audit state.
