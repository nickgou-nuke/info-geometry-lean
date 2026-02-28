# Graph-Driven Refactor Plan

## Snapshot

- Module graph: `docs-map/module_graph.json`
- Total modules in graph: **237**
- Buildable modules: **230**
- Non-buildable modules: **7**
- Stable-closure size from `InfoGeometry, InfoGeometry.Library, InfoGeometry.Canonical.All`: **212**

## Region Health

| Region | Total | Buildable | Non-buildable |
|---|---:|---:|---:|
| Analysis | 2 | 2 | 0 |
| Architecture | 1 | 1 | 0 |
| Archive | 3 | 0 | 3 |
| Assumptions | 7 | 7 | 0 |
| Axioms | 1 | 1 | 0 |
| Basic | 1 | 1 | 0 |
| Canonical | 87 | 87 | 0 |
| Cartan | 2 | 2 | 0 |
| Causal | 2 | 2 | 0 |
| Clifford | 12 | 12 | 0 |
| Convex | 8 | 8 | 0 |
| Core | 11 | 11 | 0 |
| Cramer | 1 | 1 | 0 |
| Degree | 1 | 1 | 0 |
| EntropicInference | 1 | 1 | 0 |
| EntropicInferenceTest | 1 | 1 | 0 |
| ExponentialFamily | 12 | 12 | 0 |
| Fenchel | 1 | 1 | 0 |
| Geometry | 3 | 3 | 0 |
| GrandCanonical | 1 | 1 | 0 |
| Information | 1 | 1 | 0 |
| Jordan | 3 | 3 | 0 |
| KL | 3 | 3 | 0 |
| Krein | 13 | 13 | 0 |
| LLM | 4 | 4 | 0 |
| Library | 1 | 1 | 0 |
| MaxEnt | 11 | 11 | 0 |
| OptimalTransport | 1 | 1 | 0 |
| PositiveMeasure | 1 | 1 | 0 |
| Potential | 3 | 3 | 0 |
| Prequantum | 4 | 4 | 0 |
| Projective | 12 | 12 | 0 |
| Quantum | 1 | 1 | 0 |
| RegularizedKL | 1 | 1 | 0 |
| RegularizedKLTest | 1 | 1 | 0 |
| Renyi | 1 | 1 | 0 |
| Root | 1 | 1 | 0 |
| SLT | 1 | 1 | 0 |
| Singular | 4 | 0 | 4 |
| SuperUnified | 1 | 1 | 0 |
| Thermal | 1 | 1 | 0 |
| Thermo | 6 | 6 | 0 |
| TransformationGroups | 1 | 1 | 0 |
| Twistor | 1 | 1 | 0 |
| auto_blueprints | 1 | 1 | 0 |
| generalizedKL | 1 | 1 | 0 |

## Highest-Priority Repair Set (Non-Archive)

- `InfoGeometry.Singular`
- `InfoGeometry.Singular.CartanWiring`
- `InfoGeometry.Singular.Drazin`
- `InfoGeometry.Singular.MoorePenrose`

## Archive Non-Buildable Set

- `InfoGeometry.Archive.Drafts.Degree_pre_assumptions_extraction`
- `InfoGeometry.Archive.Drafts.New_pre_assumptions_extraction`
- `InfoGeometry.Archive.Drafts.Projective_LogSum_pre_assumptions_extraction`

## Error Cause Buckets

- `symbol-drift`: 2
- `syntax-or-notation-drift`: 1
- `non-buildable-modules-without-diagnostics`: 4

## Diagnostics Consistency

- Current non-buildable modules missing diagnostics: **4**
  - `InfoGeometry.Singular`
  - `InfoGeometry.Singular.CartanWiring`
  - `InfoGeometry.Singular.Drazin`
  - `InfoGeometry.Singular.MoorePenrose`

## Buildable Modules Outside Canonical and Outside Stable Closure

- `InfoGeometry.Cartan`
- `InfoGeometry.Cartan.Involution`
- `InfoGeometry.Causal.Cones`
- `InfoGeometry.Causal.MirrorAlignment`
- `InfoGeometry.Clifford.CartanInstance`
- `InfoGeometry.Clifford.Cl11Matrix`
- `InfoGeometry.Clifford.Decomposition`
- `InfoGeometry.Clifford.MatrixCompat`
- `InfoGeometry.Clifford.TowerMatrix`
- `InfoGeometry.Krein.Dilation`
- `InfoGeometry.Krein.DoubledSpace`
- `InfoGeometry.Krein.Grading`
- `InfoGeometry.Krein.Representation`
- `InfoGeometry.Krein.Superphysics`

## Compatibility Aliases Outside Stable Closure

- `InfoGeometry.SuperUnified`
- `InfoGeometry.generalizedKL`

## Short-Name Duplicates (Potential De-dup Targets)

- `CartanDecomposition`:
  - `InfoGeometry.Canonical.CartanDecomposition`
  - `InfoGeometry.Krein.CartanDecomposition`
- `Core`:
  - `InfoGeometry.Core`
  - `InfoGeometry.GrandCanonical.Core`
  - `InfoGeometry.Jordan.Core`
  - `InfoGeometry.MaxEnt.Core`
- `Drazin`:
  - `InfoGeometry.Canonical.Drazin`
  - `InfoGeometry.Singular.Drazin`
- `DualConnections`:
  - `InfoGeometry.Assumptions.DualConnections`
  - `InfoGeometry.Canonical.DualConnections`
- `Finite`:
  - `InfoGeometry.ExponentialFamily.Finite`
  - `InfoGeometry.KL.Finite`
  - `InfoGeometry.MaxEnt.Finite`
- `FiniteMatrix`:
  - `InfoGeometry.Thermal.FiniteMatrix`
  - `InfoGeometry.Thermo.FiniteMatrix`
- `Grading`:
  - `InfoGeometry.Clifford.Grading`
  - `InfoGeometry.Krein.Grading`
- `IB`:
  - `InfoGeometry.Assumptions.IB`
  - `InfoGeometry.Canonical.IB`
- `Involution`:
  - `InfoGeometry.Cartan.Involution`
  - `InfoGeometry.Core.Involution`
- `LLN`:
  - `InfoGeometry.Assumptions.LLN`
  - `InfoGeometry.Canonical.LLN`
- `Legendre`:
  - `InfoGeometry.Convex.Legendre`
  - `InfoGeometry.ExponentialFamily.Legendre`
- `ManifoldHomology`:
  - `InfoGeometry.Assumptions.ManifoldHomology`
  - `InfoGeometry.Canonical.ManifoldHomology`
- `MoorePenrose`:
  - `InfoGeometry.Canonical.MoorePenrose`
  - `InfoGeometry.Singular.MoorePenrose`
- `Projective`:
  - `InfoGeometry.Canonical.Projective`
  - `InfoGeometry.Projective.Projective`
- `SuperUnified`:
  - `InfoGeometry.Canonical.SuperUnified`
  - `InfoGeometry.SuperUnified`
- `Thermo`:
  - `InfoGeometry.Canonical.Thermo`
  - `InfoGeometry.Potential.Thermo`

## Path Probe: RN -> Potential -> Calabi-Yau (Module Level)

- Radon-Nikodym anchor `InfoGeometry.Assumptions.LLN` to potential anchor `InfoGeometry.Potential.LogPotential`: `InfoGeometry.Assumptions.LLN -> InfoGeometry.Assumptions -> InfoGeometry.Canonical.Foundations -> InfoGeometry.Convex.Bregman -> InfoGeometry.Potential.LogPotential`
- Potential anchor `InfoGeometry.Potential.LogPotential` to Calabi-Yau anchor `InfoGeometry.Canonical.CalabiYauBridge`: `InfoGeometry.Potential.LogPotential -> InfoGeometry.Convex.Bregman -> InfoGeometry.Canonical.Foundations -> InfoGeometry.Canonical.All -> InfoGeometry.Canonical.CalabiYauBridge`
- Radon-Nikodym anchor `InfoGeometry.Assumptions.LLN` to Calabi-Yau anchor `InfoGeometry.Canonical.CalabiYauBridge`: `InfoGeometry.Assumptions.LLN -> InfoGeometry.Canonical.LLN -> InfoGeometry.Canonical.All -> InfoGeometry.Canonical.CalabiYauBridge`

## Refactor Phases

1. Repair syntax/import drift in the non-archive non-buildable set.
2. Promote buildable orphan modules by creating canonical wrappers and adding explicit imports into `InfoGeometry.Canonical.Foundations` or domain umbrellas.
3. De-duplicate short-name collisions by selecting one canonical module path and leaving thin aliases in old paths.
4. Keep `Archive/Drafts` out of stable closure; salvage only declarations with complete proofs into canonical/domain modules.
5. Re-run `make_graph` and `refactor_plan` after each refactor slice to track convergence.
