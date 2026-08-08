# AQL Network Repair Report

Ran against local ArangoDB via `tools/lean_graph/aql_query.py`:

```bash
python3 tools/lean_graph/aql_query.py \
  --endpoint http://127.0.0.1:8529 \
  --database info_geometry \
  --username root \
  --password ''
```

Note: `/home/goutev/.config/arango/env.sh` is absent, so explicit flags were used. ArangoDB is listening on `127.0.0.1:8529`, database `info_geometry`.

## Refresh performed

The global Arango graph was stale with respect to the new thermodynamic modules, so I imported the targeted syntax/env bridge for:

- `ThermodynamicNetworkSpine.lean`
- `ThermodynamicLorentzBoost.lean`

Commands:

```bash
lake env lean --run tools/lean_graph/DumpLeanGraph.lean \
  ThermodynamicNetworkSpine.lean ThermodynamicLorentzBoost.lean \
  > /tmp/thermo_syntax.jsonl

python3 tools/lean_graph/join_syntax_env.py \
  --syntax-jsonl /tmp/thermo_syntax.jsonl \
  --env-json proof_graph.json \
  --include-syntax-tree \
  > /tmp/thermo_bridge.jsonl

python3 tools/lean_graph/import_arango.py /tmp/thermo_bridge.jsonl \
  --execute \
  --host http://127.0.0.1:8529 \
  --database info_geometry \
  --user root \
  --password ''
```

Import result:

```text
joined 9 syntax records; matched 9 against 13108 env records
executed: bridge_records=9 lean_decls=9 matched_syntax_env=9 syntax_only=0 syntax_roots=9 syntax_nodes=802 references=89 ast_child=793 has_syntax=9
```

Post-refresh AQL counts:

```json
{
  "lean_decls": 3336,
  "syntax_nodes": 454708,
  "references": 8880,
  "has_syntax": 2132
}
```

## Output files

- `tools/lean_graph/out/aql_conductors.json`
- `tools/lean_graph/out/aql_dangling.json`
- `tools/lean_graph/out/aql_module_wires.json`
- `tools/lean_graph/out/aql_thermo_after_ingest.json`
- `tools/lean_graph/out/aql_spine_neighborhood.json`

## AQL-confirmed thermodynamic spine

AQL now sees:

```text
ThermodynamicNetworkSpine.closed_thermodynamic_network_spine
```

with direct dependency neighborhood including:

- `ThermodynamicLorentzBoost.equivariant_lorentz_boost_signature`
- `ThermodynamicTKKBridge.formalChiralParityIndex_zero`
- `ThermalBoostLorentzSuperalgebra.lorentzBoost_zero`
- `ThermalBoostLorentzSuperalgebra.gamma_zero`
- `ThermalBoostLorentzSuperalgebra.qOfRapidity_zero`
- `ThermalBoostLorentzSuperalgebra.safeDispersionFactor_zero`
- `DiracCuntzCrystalDispersion.masslessDiracCuntzEnergySq_zero_rapidity`
- `KTheoryChernConfinementSignature.chernParity_zero`
- `NonAbelianBrillouinKleinBottle.bkbFold_involutive`
- `NonAbelianBrillouinKleinBottle.bkbLaneTransition_involutive`

The spine itself remains a top-level capstone with no direct inbound users yet. That is expected until it is wired into a higher publication/certificate module.

## AQL top conductors before/around repair

From `aql_conductors.json`, highest declaration conductors in ArangoDB:

1. `AlgebraicCuntzQuotient.S` — used_by 43, deps 15
2. `AlgebraicCuntzQuotient.T` — used_by 43, deps 15
3. `AlgebraicCuntzQuotient.CuntzAlg` — used_by 93, deps 4
4. `BogoliubovSU3ParafermionProofChain.su3_color_action_all_commutators` — used_by 10, deps 26
5. `BogoliubovWeylChemicalPotential.frameWeylQ` — used_by 19, deps 7

## AQL top dangling ends

From `aql_dangling.json`, high-dependency zero-inbound capstones include:

1. `GellMannParafermionRealizationRoutesSynthesis.gellmann_parafermion_realization_routes_synthesis` — 60 deps
2. `TopologicalColorCrystalFormal.topological_color_crystal_formal_synthesis` — 53 deps
3. `CurryHowardLambekColimit.curry_howard_lambek_colimit_synthesis` — 49 deps
4. `HolographicGaugeSymmetryUniqueness.holographic_gauge_symmetry_uniqueness_synthesis` — 48 deps
5. `BogoliubovSU3ParafermionWeld.bogoliubov_su3_parafermion_synthesis` — 45 deps

## AQL thick module wires

From `aql_module_wires.json`:

1. `SupergradedCuntzBdG -> AlgebraicCuntzQuotient` — 114 edges
2. `ChiralTensorRecoupling -> ChiralCausalCone` — 101 edges
3. `BogoliubovSU3ParafermionProofChain -> GellMannSU3` — 90 edges
4. `ComplexStarCuntzRedesign -> AlgebraicCuntzQuotient` — 74 edges
5. `ColorCARStandardModel -> ChiralCausalCone` — 63 edges

## Completed next repair: color/parafermion/Cuntz bus spine

Added and built:

```text
ColorParafermionCuntzBusSpine.lean
```

Main theorem:

```lean
ColorParafermionCuntzBusSpine.closed_color_parafermion_cuntz_bus_spine
```

It packages existing closed finite theorem objects from the thick bus:

```text
GellMannParafermionRealizationRoutesSynthesis
BogoliubovSU3ParafermionWeld
BogoliubovSU3ParafermionProofChain
GellMannSU3
SupergradedCuntzBdG
AlgebraicCuntzQuotient
```

Targeted AQL bridge import:

```text
joined 1 syntax records; matched 1 against 13109 env records
executed: bridge_records=1 lean_decls=1 matched_syntax_env=1 syntax_only=0 syntax_roots=1 syntax_nodes=46 references=78 ast_child=45 has_syntax=1 decl_root=1
```

Important tooling note: `aql_query.py` gives loaded `ARANGO_*` environment variables precedence over explicit flags. For the local empty-password DB, run AQL with these variables pinned:

```bash
export ARANGO_URL=http://127.0.0.1:8529
export ARANGO_DATABASE=info_geometry
export ARANGO_DB=info_geometry
export ARANGO_USERNAME=root
export ARANGO_USER=root
export ARANGO_PASSWORD=''
export ARANGO_PASS=''
```

AQL files for this repair:

- `tools/lean_graph/out/aql_color_bus_neighborhood.json`
- `tools/lean_graph/out/aql_color_bus_dangling_check.json`

AQL confirms the new spine has `deps_count = 78` and directly uses:

- `GellMannParafermionRealizationRoutesSynthesis.gellmann_parafermion_realization_routes_synthesis`
- `BogoliubovSU3ParafermionWeld.bogoliubov_su3_parafermion_synthesis`
- `BogoliubovSU3ParafermionProofChain.bogoliubov_su3_parafermion_proof_chain`
- `BogoliubovSU3ParafermionProofChain.su3_color_action_all_commutators`
- `BogoliubovSU3ParafermionProofChain.theoremBackedColorParafermionBraidingSocket`
- `BogoliubovSU3ParafermionWeld.frame_affine_gl1_gl2`
- `BogoliubovSU3ParafermionWeld.bdgParafermionPlus4_sq`
- `GellMannSU3.gl1_comm_gl2`
- `AlgebraicCuntzQuotient.T_mul_S`
- `AlgebraicCuntzQuotient.partition_one`

Dangling-check impact:

```text
GellMannParafermionRealizationRoutesSynthesis.gellmann_parafermion_realization_routes_synthesis — used_by 1, deps 60
BogoliubovSU3ParafermionWeld.bogoliubov_su3_parafermion_synthesis — used_by 1, deps 45
BogoliubovSU3ParafermionProofChain.bogoliubov_su3_parafermion_proof_chain — used_by 1, deps 34
ColorParafermionCuntzBusSpine.closed_color_parafermion_cuntz_bus_spine — used_by 0, deps 78
```

So the previous high-dependency capstones are no longer zero-inbound in AQL.

## Final certificate layer

Added and built:

```text
FiniteSpinePublicationCertificate.lean
```

Main theorem:

```lean
FiniteSpinePublicationCertificate.finite_spine_publication_certificate
```

This consumes both graph-repair spines:

- `ThermodynamicNetworkSpine.closed_thermodynamic_network_spine`
- `ColorParafermionCuntzBusSpine.closed_color_parafermion_cuntz_bus_spine`

AQL import result:

```text
joined 1 syntax records; matched 1 against 13110 env records
executed: bridge_records=1 lean_decls=1 matched_syntax_env=1 syntax_only=0 syntax_roots=1 syntax_nodes=175 references=113 ast_child=174 has_syntax=1 decl_root=1
```

AQL inbound check:

```text
ThermodynamicNetworkSpine.closed_thermodynamic_network_spine — used_by 1, deps 44
ColorParafermionCuntzBusSpine.closed_color_parafermion_cuntz_bus_spine — used_by 1, deps 78
FiniteSpinePublicationCertificate.finite_spine_publication_certificate — used_by 0, deps 113
```

So the two repaired spines are no longer dangling; the single intended top-level capstone is now the finite publication certificate.
