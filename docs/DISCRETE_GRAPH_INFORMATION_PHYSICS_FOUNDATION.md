# Discrete Graph Information Physics Foundation

This note records the repo-native owner surfaces for the discrete graph
information-physics lane.  It is intentionally a routing document, not a new
universal theorem.

## Authority boundary

```text
Lean source and kernel checks are proof authority.
Arango/SCC overlays are derived navigation and audit context.
Numerical spectra are diagnostic priors.
LLM prompts are proposal context only.
```

No Hodge, Dirac, Drazin, Moore-Penrose, or Gromov-Witten graph diagnostic may
be promoted as a proof claim without a Lean owner theorem or an explicit witness
context.

## Existing owner surfaces

Graph Hodge/Dirac/chiral operators:

```text
lean/DAG/TwoComplex.lean
lean/DAG/GraphHodge.lean
```

These own finite two-complexes, boundary maps, combinatorial Laplacians, Betti
summaries, graph Dirac matrices, chiral gradings, and chiral anticommutation
checks.

Singular support operators:

```text
lean/InfoGeometry/Singular/MoorePenrose.lean
lean/InfoGeometry/Singular/Drazin.lean
```

Moore-Penrose is the metric/support projector lane.  Drazin is the
spectral/core projector lane.  Their mismatch is interpreted only through the
explicit projector/anomaly owner surfaces.

Real Majorana/Krein/Clifford carrier:

```text
lean/InfoGeometry/Core/MajoranaLiftPacket.lean
lean/InfoGeometry/Krein/DoubledSpace.lean
lean/InfoGeometry/Krein/PolarizedSector.lean
lean/InfoGeometry/Clifford/HestenesDirac.lean
```

This is the real doubled carrier lane: no complex scalar collapse is required
for the Hestenes/Majorana interpretation.

Gromov-Witten/Erlangen localization and counting packets:

```text
lean/InfoGeometry/GromovWittenErlangen/*.lean
lean/InfoGeometry/Probability/HomologicalProbability.lean
```

These route projective/Gromov-Witten-style counting and localization through
explicit Drazin/Frobenius/Erlangen witness packet (Native Closure Mandated: Closure Debt)s.  Graph proximity alone is
not a Gromov-Witten invariant.

Arango causal cone context:

```text
tools/infra/arango_causal_chiral_cone_prompt.py
tools/infra/hydrated_dag_to_lean_graph.py
tools/infra/paperproof_bidirectional_cone.py
```

These produce bounded causal/prompt/visualization artifacts.  They are not proof
objects.

## Local lightcone spectral filter

```text
tools/infra/lightcone_spectral_filter.py
```

The local filter consumes a bounded slice, normally produced from Arango or the
hydrated SCC DAG, and builds a small matrix with orientation:

```text
dependency -> user
```

It computes numerical Schur/Drazin projector diagnostics and a symmetric local
Hodge Laplacian.  It is deliberately guarded by `--max-nodes` and must not be
used as a dense full-repository operator.

Interpretation:

```text
strict acyclic flow       -> nilpotent / transient Drazin behavior
recurrent local structure -> nonzero spectral core
Hodge harmonic signal     -> connected/harmonic local obstruction diagnostic
```

A strict finite DAG can have trivial Drazin spectral core while still having a
meaningful Hodge connected-component harmonic signal.  That is expected.

## Tactic-transition operator enrichment

```text
tools/infra/enrich_tactic_path_with_lightcone_spectrum.py
```

Drazin becomes most informative on tactic-transition telemetry, where repeated
failures, loops, timeouts, absorbing success sectors, and stall sectors create a
singular local operator.  The enrichment pass attaches local lightcone context
to `reports/training/tactic_path_ranking.jsonl` and applies only a conservative
sampling multiplier.

Default multiplier:

```text
final_operator_sampling_weight
  = sampling_priority
  * (1 + alpha * normalized_core_weight)
  * (1 + beta  * normalized_harmonic_weight)
  * (1 - gamma * normalized_nilpotent_residue_weight)
```

Default constants are intentionally small:

```text
alpha = 0.10
beta  = 0.05
gamma = 0.10
```

This keeps verified Lean success/failure labels dominant.

## Operational doctrine

```text
DAG topology gives causal/homological structure.
Tactic-transition telemetry gives the singular operator.
Drazin filtering belongs on recurrent/stall transition structure.
Hodge/Dirac features can be projected from bounded DAG + tactic graph context.
Lean remains proof authority.
```
