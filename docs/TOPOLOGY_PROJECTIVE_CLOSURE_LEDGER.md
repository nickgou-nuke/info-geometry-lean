# Topology / Projective Closure Ledger

This ledger records the current end-state in a theorem-honest form.  It is a
manifest for stabilization and review, not a claim that the physical
interpretation has been proved in Lean.

## Separate Finite Readouts

These are adjacent finite constructions, not an equivalence or causal chain:

```text
Klein/Plücker incidence   |   thermodynamic commutator   |   DAG-edge commutation
```

In the compiled Lean surface this means only:

- finite Delaunay/Pachner word equivalences preserve the Rohozhkin matrix when
  the equivalence is supplied explicitly;
- `CausalNonequilibriumFlow` records finite ring-level transition data;
- entropy production is the commutator
  `P_forward * P_backward - P_backward * P_forward`;
- equality with `d_ln_Q` is conditional on an explicit commutator premise;
- there is no Lean theorem identifying these ring-level facts with BCFW
  residue balance or a physical scattering amplitude.

## Kernel-Native Core

The following surfaces are kernel-native finite algebraic content:

- `InfoGeometry.Topology.ThermodynamicGauge`
  - `entropy_production_eq_commutator`
  - `de_rham_potential_equals_entropy_production_of_commutator`
  - `entropy_production_eq_zero_iff_detailed_balance`
  - `gauge_field_covariance`
  - finite Wilson-word helpers and explicit trace readbacks
- `InfoGeometry.Topology.GrandUnificationLinker`
  - `dag_edge_commutes_with_symmetric_mixed` follows from the two explicit
    intertwining equations for the DAG edge and the split generators.
  - `nilpotent_sandwich_zero` proves the symmetric mixed-product sandwich
    identity from one square-zero hypothesis in an associative ring.
  Neither statement is a mass-shell or BCFW theorem.
- `InfoGeometry.Projective.MacaulayTrackBIngestion`
  - the ingested integer `1296` agrees with the Lean candidate polynomial
    evaluation `tateMotivePolynomial 3`;
  - current source uses `*Certificate` boundary records for provenance and
    candidate-rank data, so it is build-clean but not strict proof-surface
    clean under the audit rules below.

## Conditional Content

These statements are allowed only as theorem premises or explicit data
comparisons:

- entropy production equals `d_ln_Q`;
- a Wilson-loop trace equals a Bost-Connes or zeta scalar;
- a finite point count is the actual external Macaulay2 D-module result;
- a Delaunay/Pachner flip is a physical scattering transition;
- a finite DAG-edge commutation identity is a BCFW residue theorem.

## Open Closure Debt

The following are not closed Lean theorems:

- physical amplituhedron volume equals the configuration-space cohomology;
- Bost-Connes partition values equal Wilson-loop curvature traces;
- Rohozhkin/Delaunay flips are analytically identical to plabic graph moves;
- the candidate Tate motive polynomial is the full de Rham cohomology
  certificate for the quadric complement;
- the whole repository is zero-debt.

At the time this ledger was written, broad proof-debt scans still reported
hundreds of `sorry`/`admit`/`axiom` hits under `lean/InfoGeometry`.  Closure
claims should therefore be made per-lane, not globally.

The strict proof-surface scan also currently flags certificate-style APIs in
the Track B ingestion and Wilson/Bost-Connes scaffolding.  Those files are
acceptable as explicit evidence boundaries only if the project intentionally
permits proof-carrying records there; otherwise they should be flattened into
ordinary definitions plus theorems with explicit hypotheses.

## Stabilization Guardrails

- Do not hide mathematical claims in structures named `*Certificate`,
  `*Witness`, `*Bridge`, or `*Interface`.
- Do not encode proof debt as fields with names such as `_True`, `_valid`,
  `_certificate`, `_law`, `law_holds`, or `recovery_law`.
- Prefer theorem statements with explicit hypotheses over proof-carrying
  packets.
- Keep finite algebraic Wilson-word lemmas separate from analytic Wilson-loop
  and Bost-Connes claims.

## Smoke Checks

Use:

```bash
bash tools/ci/smoke_import_spikes.sh
```

For an additional local proof-surface scan of the active Wilson/linker files:

```bash
STRICT_PROOF_SURFACE=1 bash tools/ci/smoke_import_spikes.sh
```

If the strict scan fails, do not start `tools/infra/evolution_worker.py` in
this checkout. It is disabled here; patch the owner source directly and verify
with `lake env lean` / locked build instead.
