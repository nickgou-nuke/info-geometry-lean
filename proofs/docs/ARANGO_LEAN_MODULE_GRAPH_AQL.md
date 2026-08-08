# ArangoDB/AQL Lean module import graph

This document creates and queries the repository-level Lean module graph generated at:

- `docs/lean_module_graph.json`
- `docs/LEAN_MODULE_GRAPH.dot`
- `docs/LEAN_MODULE_GRAPH.svg`

The graph models local Lean imports:

```text
lean_modules/{ModuleA} --lean_imports--> lean_modules/{ModuleB}
```

where the edge means:

```text
ModuleA imports ModuleB
```

## Import/create graph

Preferred importer, no `python-arango` dependency:

```bash
cd /home/goutev/auto
python3 proofs/tools/lean_graph/import_module_graph_arango.py

# write to local ArangoDB
python3 proofs/tools/lean_graph/import_module_graph_arango.py --execute \
  --url http://localhost:8529 \
  --database info_geometry \
  --user root \
  --password ''
```

Creates:

```text
vertex collection: lean_modules
edge collection:   lean_imports
graph:             LeanModuleImportGraph
```

Environment overrides:

```bash
export ARANGO_URL=http://localhost:8529
export ARANGO_DB=info_geometry
export ARANGO_USER=root
export ARANGO_PASSWORD=''
export ARANGO_MODULE_GRAPH=LeanModuleImportGraph
```

## AQL smoke checks

```aql
RETURN {
  modules: LENGTH(FOR m IN lean_modules RETURN 1),
  imports: LENGTH(FOR e IN lean_imports RETURN 1)
}
```

Expected from the generated graph at creation time:

```text
modules = 457
imports = 502
```

## Top imported modules

```aql
FOR e IN lean_imports
  COLLECT target = e._to WITH COUNT INTO c
  SORT c DESC
  LIMIT 30
  LET m = DOCUMENT(target)
  RETURN { module: m.name, category: m.category, importedBy: c, path: m.path }
```

## Modules importing the most local modules

```aql
FOR e IN lean_imports
  COLLECT source = e._from WITH COUNT INTO c
  SORT c DESC
  LIMIT 30
  LET m = DOCUMENT(source)
  RETURN { module: m.name, category: m.category, imports: c, path: m.path }
```

## Category edge graph

```aql
FOR e IN lean_imports
  LET s = DOCUMENT(e._from)
  LET t = DOCUMENT(e._to)
  COLLECT fromCategory = s.category, toCategory = t.category WITH COUNT INTO c
  SORT c DESC
  RETURN { from: fromCategory, to: toCategory, imports: c }
```

## Immediate dependencies of a module

Bind variable:

```json
{ "module": "GellMannParafermionSolder" }
```

AQL:

```aql
LET start = DOCUMENT(CONCAT('lean_modules/', @module))
FOR v, e IN 1..1 OUTBOUND start lean_imports
  SORT v.name
  RETURN { imports: v.name, category: v.category, path: v.path }
```

## Immediate users of a module

```aql
LET start = DOCUMENT(CONCAT('lean_modules/', @module))
FOR v, e IN 1..1 INBOUND start lean_imports
  SORT v.name
  RETURN { importedBy: v.name, category: v.category, path: v.path }
```

## Transitive dependency closure

```aql
LET start = DOCUMENT(CONCAT('lean_modules/', @module))
FOR v, e, p IN 1..20 OUTBOUND start lean_imports
  OPTIONS { uniqueVertices: 'global' }
  SORT LENGTH(p.edges), v.name
  RETURN { depth: LENGTH(p.edges), module: v.name, category: v.category, path: v.path }
```

## Reverse impact cone: what depends on this module?

```aql
LET start = DOCUMENT(CONCAT('lean_modules/', @module))
FOR v, e, p IN 1..20 INBOUND start lean_imports
  OPTIONS { uniqueVertices: 'global' }
  SORT LENGTH(p.edges), v.name
  RETURN { depth: LENGTH(p.edges), module: v.name, category: v.category, path: v.path }
```

## Shortest path between two modules

Bind variables:

```json
{ "from": "WeylSU3ColorSymmetry", "to": "GellMannSU3" }
```

AQL:

```aql
LET source = DOCUMENT(CONCAT('lean_modules/', @from))
LET target = DOCUMENT(CONCAT('lean_modules/', @to))
FOR v, e IN OUTBOUND SHORTEST_PATH source TO target lean_imports
  RETURN { module: v.name, category: v.category, edge: e.kind }
```

For reverse conceptual paths, use `ANY SHORTEST_PATH`:

```aql
FOR v, e IN ANY SHORTEST_PATH source TO target lean_imports
  RETURN { module: v.name, category: v.category, edge: e.kind }
```

## Current finite algebraic spine query

```aql
LET finiteSpine = [
  'FiniteMatrixElementDuality',
  'KreinCuntzShadow',
  'GNSQuotientFinite',
  'SpectralSquashCayleyDKT',
  'QSuperCuntzRegularization',
  'QSuperRegularizationRosetta',
  'QRootOfUnityTruncation',
  'QuadraticConfiguration3',
  'NonIsoConf3OrlikSolomon',
  'NonIsoConf3QuadricD4Model',
  'NonIsoConf3QuadricD4PointCount',
  'NonIsoConf3QuadricD4EPolynomial',
  'GrothendieckGromovWittenYangBaxter',
  'TKKJordanPairSocket',
  'AmariChentsovFierzTorsion'
]
FOR name IN finiteSpine
  LET m = DOCUMENT(CONCAT('lean_modules/', name))
  LET out = LENGTH(FOR e IN lean_imports FILTER e._from == m._id RETURN 1)
  LET inc = LENGTH(FOR e IN lean_imports FILTER e._to == m._id RETURN 1)
  RETURN { module: name, category: m.category, imports: out, importedBy: inc, path: m.path }
```

## Current weld spine query

```aql
LET spine = [
  'HestenesCuntzPhaseSpace',
  'GaugeUHFLift',
  'WeylGaugeColimitWeld',
  'WeylColimitCanonicalLimit',
  'RescaledPhaseVolumeCanonical',
  'BogoliubovWeylChemicalPotential',
  'BogoliubovSU3ParafermionProofChain',
  'GellMannParafermionSolder',
  'WeylSU3ColorSymmetry',
  'WeylSolderedParafermionSymmetry',
  'BogoliubovBraidGraphWeld'
]
FOR name IN spine
  LET m = DOCUMENT(CONCAT('lean_modules/', name))
  LET out = LENGTH(FOR e IN lean_imports FILTER e._from == m._id RETURN 1)
  LET inc = LENGTH(FOR e IN lean_imports FILTER e._to == m._id RETURN 1)
  RETURN { module: name, category: m.category, imports: out, importedBy: inc, path: m.path }
```

## Find all modules by theme/category

```aql
FOR m IN lean_modules
  FILTER m.category == @category
  SORT m.name
  RETURN { module: m.name, path: m.path, imports: m.localImportCount }
```

Example bind variable:

```json
{ "category": "Gauge / Standard Model color" }
```

## Orphans / standalone modules

Modules with no local imports and no local users:

```aql
FOR m IN lean_modules
  LET out = LENGTH(FOR e IN lean_imports FILTER e._from == m._id RETURN 1)
  LET inc = LENGTH(FOR e IN lean_imports FILTER e._to == m._id RETURN 1)
  FILTER out == 0 AND inc == 0
  SORT m.name
  RETURN { module: m.name, category: m.category, path: m.path }
```

## Delete/recreate

```aql
FOR e IN lean_imports REMOVE e IN lean_imports
```

```aql
FOR m IN lean_modules REMOVE m IN lean_modules
```

Then rerun:

```bash
python3 proofs/tools/lean_graph/import_module_graph_arango.py --execute
```
