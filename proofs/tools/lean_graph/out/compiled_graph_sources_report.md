# Compiled Theory Graph Sources

ArangoDB/AQL audit over the compiled Lean graph.

Stored edge convention:

```text
A --references--> B   means   A depends on B
```

Therefore **graph-theory sources** are declarations with no incoming `references` edges: nobody in the compiled graph currently depends on them. In proof-development language, these are usually capstones/unconsumed declarations, not primitive seeds.

## AQL query

```aql
FOR d IN lean_decls
  LET incoming = LENGTH(FOR e IN references FILTER e._to == d._id RETURN 1)
  LET outgoing = LENGTH(FOR e IN references FILTER e._from == d._id RETURN 1)
  FILTER incoming == 0
  SORT outgoing DESC, d.module, d.name
  RETURN {
    name: d.name,
    module: d.module,
    kind: d.kind,
    incoming: incoming,
    outgoing: outgoing,
    graph_role: outgoing == 0 ? 'isolated_source' : 'source_capstone_or_unconsumed'
  }
```

Full source list:

```text
tools/lean_graph/out/aql_compiled_graph_sources.json
```

Summary:

```text
tools/lean_graph/out/aql_compiled_graph_source_summary.json
```

## Counts

```text
source_count:             4811
nonisolated_source_count: 4698
isolated_source_count:     113
```

By kind:

```text
theorem: 2657
def:     2154
```

## Top source modules

```text
SplitClifford                         161
SupergradedCuntzBdG                   148
QuadraticConfiguration3               103
PenroseSpinTilingConfig               102
JaynesLDDPGNSColimit                   94
NonIsoConf3DeRhamCooperad              92
TrainsumQuanticsTensorTrainsDigest     86
NonIsoConf3OrlikSolomon                78
JaynesLeanColimitBridge                71
NonIsoConf3QuadricD4Model              70
ThermodynamicTKKBridge                 70
TripotentCliffordColimit               70
WallpaperHolographicSelectionRules     68
QuaternionQuanticsBackendDigest        67
HillWheelerProjection                  65
```

## Highest-dependency graph sources

These are source/capstone declarations with no inbound users and many outgoing dependencies.

```text
113 deps  FiniteSpinePublicationCertificate.finite_spine_publication_certificate
 58 deps  ModularRadonNikodymJacobianBridge.de_rham_alpha_beta_forbidden_cone_clock_synthesis
 56 deps  ModularRadonNikodymJacobianBridge.modular_rn_jacobian_chemical_derham_tkk_synthesis
 56 deps  PenroseQuadricTopologySynthesis.penrose_quadric_topological_compilation
 53 deps  TopologicalColorCrystalFormal.topological_color_crystal_formal_synthesis
 52 deps  EntropicChiralDeRhamDictionary.entropic_chiral_deRham_dictionary_synthesis
 49 deps  ChemicalPotentialDeRhamG0Bridge.chemical_potential_derham_g0_synthesis
 49 deps  CurryHowardLambekColimit.curry_howard_lambek_colimit_synthesis
 48 deps  HolographicGaugeSymmetryUniqueness.holographic_gauge_symmetry_uniqueness_synthesis
 48 deps  SuperconductingHolographicResonator.superconducting_holographic_resonator_synthesis
 46 deps  ThermodynamicTKKBridge.thermodynamic_tkk_bridge_synthesis
 43 deps  FinalSpectroscopicSynthesisAudit.final_spectroscopic_synthesis_audit
 43 deps  TopologicalAndreevPump.topological_andreev_pump_synthesis
 40 deps  ConformalScaleRecurrence.conformal_scale_recurrence_synthesis
 39 deps  CuntzBoundarySolderRealization.cuntz_boundary_solder_realization_synthesis
 39 deps  Mirror31PSLnQFlowToy.mirror31_ps_lnq_flow_toy_synthesis
 38 deps  ClebschGordanPenroseNonequilibriumSpinGraph.cg_penrose_nonequilibrium_spin_graph_synthesis
 38 deps  MetamaterialQuasicrystalBloch.metamaterial_quasicrystal_bloch_synthesis
 38 deps  StimulatedScatteringAmplituhedron.stimulated_scattering_amplituhedron_synthesis
 37 deps  ChemicalPotentialTKKGradeZero.chemical_potential_tkk_g0_rank32_environmental_synthesis
```

## Interpretation

With the stored orientation `theorem -> prerequisites`:

```text
graph source = no inbound users = top/capstone/unconsumed declaration
graph sink   = no outgoing deps = primitive/base dependency seed
```

So the main graph source of the current compiled theory is:

```lean
FiniteSpinePublicationCertificate.finite_spine_publication_certificate
```

The complete set of 4811 graph sources is in the JSON file above.
