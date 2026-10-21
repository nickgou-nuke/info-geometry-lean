# GitHub keywords from the declaration DAG

This is a source- and declaration-graph-based keyword proposal for the
repository GitHub page. It is not a claim that every prose theme in the
repository is a completed mathematical theory.

## Evidence boundary

The inventory searched repository-owned `lean/` and `proofs/` recursively.
The local declaration index used was:

```text
artifacts/dag/index/decls.jsonl
artifacts/dag/index/edges.jsonl
```

The index is navigation evidence with unknown freshness unless its generation
metadata is tied to the current source, toolchain, and olean state. A bounded
read-only live query was later run against the default AST/AQL endpoint
(`infogeometry`, `127.0.0.1:8530`) for the terms `clifford`, `krein`,
`modular`, `souriau`, `kms`, `cuntz`, `colimit`, `bogoliubov`, `fisher`,
`metriplectic`, `onsager`, `zorn`, `octonion`, `triality`, and `grassmannian`.
It scanned 171,308 declaration records and performed zero writes. The live
query confirms owner-module corridors, but it does not establish theorem
correctness or current source freshness.

Declaration names were grouped by concept term. For each group we recorded
declaration count, module breadth, theorem/definition mix, and inbound edge
count (dependents). Fingerprints and hash clusters were used only to locate
owners; they do not establish equivalence or semantic depth.

## Strongest owner-backed concepts

The following concepts have broad declaration coverage and multiple owner
modules in the local DAG:

| Concept | Declarations | Modules | Representative owner corridors |
| --- | ---: | ---: | --- |
| Zorn matrices | 4386 | 125 | `Algebra.ZornVectorMatrix`, `Algebra.KingdonSplitOctonion`, `Canonical.ZornSpinor` |
| Clifford algebra | 2638 | 99 | `Clifford.Cl55SpinorChirality`, `Clifford.Clifford55`, `Clifford.Cl11TensorTower` |
| Souriau thermodynamics | 2419 | 33 | `Canonical.CoordinatelessSouriauKMSBridge`, `SouriauOperatorialLogPotential`, `SouriauCoadjointOrbitMetriplecticTheorem` |
| Modular theory/flow | 2065 | 114 | `Canonical.HestenesKreinModularGeometry`, `SouriauTomitaModularFlowBridge`, `OperatorAlgebra.ModularChiralMirror` |
| Krein geometry | 1906 | 83 | `Krein.KreinSpace`, `SouriauKreinMetriplecticContext`, `OperatorAlgebra.KreinIsotropicCone` |
| Thermodynamics | 1284 | 45 | `OperatorAlgebra.OperatorThermodynamics`, `AmariSouriauThermodynamicGauge` |
| Cuntz algebras | 1188 | 23 | `Algebra.CuntzN`, `Algebra.CuntzTensorQuotient`, `Topology.CuntzCantorSpectralTriple` |
| Split octonions | 1134 | 24 | `OperatorAlgebra.SplitOctonionMultiplication`, `Algebra.KingdonSplitOctonion` |
| KMS states | 1072 | 28 | `Canonical.CoordinatelessSouriauKMSBridge`, `Canonical.BostConnesKMS`, `Canonical.SouriauTomitaModularFlowBridge` |
| Tomita--Takesaki | 973 | 14 | `OperatorAlgebra.TomitaCartanSplit`, `Canonical.TomitaTakesaki` |
| Bogoliubov transformations | 596 | 19 | `Canonical.BogoliubovTransport`, `Canonical.BogoliubovFockSuper`, `Quantum.RealMajorana` |
| Metriplectic systems | 449 | 5 | `Canonical.SouriauCoadjointOrbitMetriplecticTheorem`, `Canonical.SouriauKreinMetriplecticContext` |
| Fisher information | 413 | 27 | `Canonical.CoordinatelessSouriauKMSBridge`, `Geometry.LegendreHessianInverse` |
| Entropy/thermodynamic potentials | 359 | 43 | `Canonical.BekensteinBound`, `Geometry.LegendreHessianInverse`, `SouriauCoadjointOrbitMetriplecticTheorem` |
| Colimits | 251 | 10 | `NCG.CategoricalInductiveColimitKMSBridge`, `Algebra.PrimonColimitAlgebra`, `Canonical.UHFInductiveColimitBoundary` |
| Triality | 251 | 12 | `Canonical.Triality`, `Physics.D4Triality`, `Quantum.SplitTrialityKernel` |
| Jordan structures | 238 | 21 | `Algebra.JordanCayleyInversionOsQ`, `Canonical.JordanKKTData` |
| Onsager reciprocity | 106 | 7 | `Canonical.OnsagerReciprocity`, `Canonical.OnsagerCasimirJ`, `Physics.FiniteOnsagerGram` |

The declaration counts above are index counts, not theorem-quality scores.
Generated constructors, instances, and recursors are included in the raw
counts; owner inspection remains necessary before making mathematical claims.

## Selected primary GitHub topics

This is the selected 14-topic set for the repository page:

```text
lean4
mathlib
formalized-mathematics
information-geometry
fisher-information
category-theory
colimits
clifford-algebra
krein-space
modular-theory
tomita-takesaki
kms-states
onsager-reciprocity
```

Optional secondary discovery keywords, if more topics are desired:

```text
souriau-thermodynamics, cuntz-algebra, car-algebra, zorn-matrices,
split-octonions, bogoliubov-transformations, metriplectic-systems,
jordan-lie-algebra, entropy, thermodynamic-potentials, gns-construction,
triality, hestenes-geometric-algebra, direct-limits, tensor-towers
```

## Keywords that need qualification

These terms occur in source or graph records but should not be presented as
fully established repository capabilities without owner-level review:

- `Sato-Grassmannian`: only a small declaration corridor was identified;
  distinguish it from finite Grassmannian and Clifford constructions.
- `Berezinian`: the identified corridor is a relative-modular shadow, not
  automatically a full Berezinian line bundle or supermanifold theorem.
- `amplituhedron`: keep positive-Grassmannian and arithmetic/KMS lanes
  separate unless an explicit proved map exists.
- `Klein-bottle`, `Möbius`, and `causal-cone`: use only for the concrete
  topology/representation owners that have been kernel-checked.
- `quantum-gravity`, `black-hole`, and similar physical labels: do not imply
  a physical theorem when the owner proves only a finite algebraic model.

## Reproducibility

To regenerate a current audit, first search source recursively, then inspect
the graph read-only. Record the exact source scope, graph generation or
freshness status, query, limits, and owner files. Do not refresh live `decls`
or `edges` merely to obtain keywords: the legacy refresh path can truncate the
collections.

The reusable bounded cross-concept query is implemented by
`tools/infra/astaql_concept_bridge.py` and documented in
`skills/astaqlhash-concept-bridge/SKILL.md`. It reports total/selected seed
counts, declaration fingerprints, direct bounded type/value paths between
selected declarations, and paths to shared prerequisites. Exact fully qualified seed names are supported for
reproducible theorem-to-theorem probes; optional module-prefix filters narrow
pattern searches. Non-compiler edge kinds are excluded. Its
smoke output records `authority`, bounds, query SHA-256, query statistics, and
`writesExecuted = 0`. An empty intersection is a bounded search result, not
evidence that a semantic bridge is absent; inspect seed diagnostics, then
inspect owner files.
