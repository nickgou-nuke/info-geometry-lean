# 7-Day Proving Itinerary (Locked Diagnostics)

> Status: `historical handover`
> Audited: 2026-05-02
> Note: Workflow history and packet memory, not current repository authority.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

This plan is scoped to the current owner graph and avoids new ontology.
All closure runs must be lock-managed and produce diagnostic artifacts.

## Global guardrails

- No `axiom`, `sorry`, or parallel theory surfaces.
- No new primitive definition of `G` from `(K, ε)`.
- First close comparison bridges already in-owner.
- Every day ends with locked build + DAG/policy checks.

## Day 1 — Baseline freeze and observability

Goal:
- Freeze a reproducible baseline for theorem traffic and policy status.

Files:
- `lean/InfoGeometry/Audit.lean`
- `lean/InfoGeometry/Canonical/All.lean`
- `artifacts/dag/index/meta.json`

Commands:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/theorem_significance.py \
  --decls artifacts/dag/index/decls.jsonl \
  --edges artifacts/dag/index/edges.jsonl \
  --out reports/dag/theorem-significance.json \
  --md reports/dag/theorem-significance.md
python3 tools/check_vacuity_policy.py reports/dag/theorem-significance.json
python3 tools/infra/canonical_policy_lint.py
```

Checkpoint:
- `InfoGeometry.All` passes lock build.
- Baseline vacuity + significance reports saved in `reports/dag/`.

## Day 2 — DPD/Wedge compatibility traffic

Goal:
- Ensure `DPDWedgeCompatibility` is the single comparison entry point.

Files:
- `lean/InfoGeometry/Canonical/DPDWedgeCompatibility.lean`
- `lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- `lean/InfoGeometry/Canonical/ModularSpectralWedge.lean`

Theorem targets:
- `two_smul_dilationGap_eq_wedgeSign`
- `dilationGap_eq_half_wedgeSign`
- `projected_supercharge_eq_commutator_PD_wedgeSign`
- `projected_supercharge_eq_neg_commutator_PZero_wedgeSign`

Checkpoint command:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.DPDWedgeCompatibility
```

Success condition:
- All 4 theorem surfaces compile and are consumed by at least one downstream bridge.

## Day 3 — Active conjugation quarantine

Goal:
- Seal the active-sector doctrine: `J_act = J (1 - P_D)` and apex annihilation.

Files:
- `lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean`
- `lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean`

Theorem targets:
- `activeModularConjugation_eq_modular_j_mul_active`
- `activeModularConjugation_mul_P_D_eq_zero`
- `P_D_mul_activeModularConjugation_eq_zero` (under explicit commutation hypothesis)

Checkpoint command:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.ModularSpectralConjugationBridge
```

Success condition:
- No global claim `J = K ∘ ε`; only active-sector equality is exported.

## Day 4 — Generator-identification closure (Unruh target)

Goal:
- Close `canonicalSeedFlowEqUnruhTarget` through generator identification only.

Files:
- `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean`
- `lean/InfoGeometry/Dynamics/UnruhKMS.lean`
- `lean/InfoGeometry/Canonical/ProjectorEquivariance.lean`

Theorem targets:
- generator bridge lemma(s) reducing flow equality to exponential equality
- final closure theorem:
  - `canonicalSeedFlowEqUnruhTarget`

Checkpoint commands:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.ModularSuperchargeClosure
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

Success condition:
- Final theorem closes without introducing extra physical assumptions beyond existing compatibility interfaces.

## Day 5 — Kramers/Majorana capstone comparison

Goal:
- Tie abstract `Θ` symmetry lane to intrinsic `u ↦ K u` lane via explicit comparison theorems.

Files:
- `lean/InfoGeometry/Canonical/KramersMajoranaCompatibility.lean`
- `lean/InfoGeometry/Canonical/KramersPhaseAxisReduction.lean`
- `lean/InfoGeometry/Canonical/ModularKramersBridge.lean`

Theorem targets:
- coincidence/reduction/divergence criteria between abstract and intrinsic Kramers constructions
- preservation/closure on fixed Majorana submodule under phase axis and grading

Checkpoint command:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.ModularKramersBridge
```

Success condition:
- No duplicated Kramers ontology; one comparison bridge surface.

## Day 6 — Type III core interface (no speculative stack)

Goal:
- Add/strengthen interface-level theorems from DPD obstruction lane to continuous core readout.

Files:
- `lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean`
- `lean/InfoGeometry/Canonical/OperatorAlgebraAQFTPackage.lean`
- `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean`

Theorem targets:
- well-typed lift of obstruction readout into semifinite/core interface
- explicit statement of what is proved vs. what remains interface-only

Checkpoint command:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.TypeIIIContinuousCoreReal
```

Success condition:
- No fake concrete implementation for unresolved Type III analytics.

## Day 7 — Debt burn-down and release gate

Goal:
- Convert structural progress into policy-clean release evidence.

Commands:
```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/theorem_significance.py \
  --decls artifacts/dag/index/decls.jsonl \
  --edges artifacts/dag/index/edges.jsonl \
  --out reports/dag/theorem-significance.post.json \
  --md reports/dag/theorem-significance.post.md
python3 tools/check_vacuity_policy.py reports/dag/theorem-significance.post.json
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_semantic_flow_report.py
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
```

Release criteria:
- Locked `InfoGeometry.All` build passes.
- No new policy violations in canonical/bridge surfaces.
- Measurable reduction in `V2/dead-public-theorem` concentration in targeted files.
- Updated closure notes recorded in `docs/active_closure/translation_tracker.md`.

## Recommended execution order (daily)

1. Implement theorem changes.
2. Targeted locked build for touched module.
3. Umbrella locked build (`InfoGeometry.All`) before day close.
4. DAG + policy diagnostics.
5. Record residual blockers explicitly.
