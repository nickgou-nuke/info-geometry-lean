# Theory DAG Vicinity Audit

Date: 2026-03-17

## Scope

This audit maps the whole-codebase vicinity around the keyword cluster:

- `chiral anomaly`
- `topological obstruction`
- `singularity`
- `rotation`
- `liquid flow`
- `volume form`
- `Radon-Nikodym`
- `rnDeriv`

The goal is not just file listing. The goal is to identify the actual theory DAG,
the category-spines it induces, and the highest-value canonicalization /
deduplication targets.

## Toolchain Roles

### Lean DAG core

Primary graph engine:

- `lean/DAG/Basic.lean`
- `lean/DAG/Hydrate.lean`
- `lean/DAG/Analysis.lean`
- `lean/DAG/BlockExport.lean`
- `lean/DAG/ServerExport.lean`
- `lean/DAG/ExportDecls.lean`
- `lean/InfoGeometry/GraphExport.lean`

What it does:

- extracts declaration graphs directly from the Lean environment
- condenses SCCs into a true DAG
- computes path counts, distances, dominators, vulnerability
- extracts a "theory skeleton"
- exports declaration/block metadata

### Python orchestration

Secondary orchestration, not the source of truth:

- `scripts/analysis/make_graph.py`
- `scripts/graph_to_blueprint.py`
- `scripts/docs/graph_to_blueprint.py`
- `scripts/docs/build_doc_map.py`

What it does:

- wraps Lean exporters
- builds module metadata and doc maps
- projects graph data into blueprint / `Architect` surfaces

### Shell / quality layer

Boundary and policy layer:

- `scripts/enforce_quarantine_imports.sh`
- `scripts/quality/orphaned-check.sh`
- `scripts/quality/*.sh`
- `scripts/perf/profile_commands.sh`

What it does:

- enforces repo boundaries
- validates source-tree shape
- profiles elaboration

### Blueprint / Architect representation

Representation layer:

- `lean/Docs/emit_blueprint_tex.lean`
- `lean/Docs/AutoTag.lean`
- `lean/InfoGeometry/BlueprintTags.lean`
- `Architect` imports in canonical files

What it does:

- turns graph/skeleton information into blueprint-facing Lean or LaTeX surfaces

## Keyword-Seeded Module Set

The keyword search over `lean/InfoGeometry` hits the following main clusters:

### Inverse / singularity layer

- `InfoGeometry.Singular.Drazin`
- `InfoGeometry.Singular.DrazinAdjoint`
- `InfoGeometry.Singular.KreinNaturalFlow`
- `InfoGeometry.Singular.NormalAnomaly`
- `InfoGeometry.Canonical.Singular`
- `InfoGeometry.Canonical.AnomalyGauge`

### Spectral / conformal / anomaly layer

- `InfoGeometry.Canonical.MoorePenrose`
- `InfoGeometry.Canonical.ChiralAnomaly`
- `InfoGeometry.Canonical.ChiralEinsteinBridge`
- `InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.ConformalAlgebra`
- `InfoGeometry.Canonical.WeylInformationGauge`
- `InfoGeometry.Canonical.AnomalyDilationBridge`
- `InfoGeometry.Canonical.BerryPhase`
- `InfoGeometry.Canonical.TopologicalInvariants`

### Spectral bridge / Hessian layer

- `InfoGeometry.Canonical.SpectralInference`
- `InfoGeometry.Canonical.BeliefDynamics`
- `InfoGeometry.Canonical.InformationTorsion`
- `InfoGeometry.Canonical.RicciMongeAmpere`

### RN / volume layer

- `InfoGeometry.Volume.RadonNikodym`
- `InfoGeometry.Volume.ConnesCocycle`
- `InfoGeometry.Volume.DeterminantBundle`
- `InfoGeometry.Canonical.UniversalVolume`
- `InfoGeometry.Measure.DiscreteRN`
- `InfoGeometry.Measure.Normalized`
- `InfoGeometry.Canonical.IBMeasure`
- `InfoGeometry.Canonical.BeliefDynamics`

### Sinkhorn / KMS / entropy barrier layer

- `InfoGeometry.Canonical.GrandCanonicalExperts`
- `InfoGeometry.Canonical.KMSSinkhornBridge`
- `InfoGeometry.Canonical.BekensteinBound`
- `InfoGeometry.Canonical.ConnesArakiFramework`

### Modular / Tomita layer

- `InfoGeometry.Canonical.TomitaTakesaki`
- `InfoGeometry.Canonical.BekensteinBound`
- `InfoGeometry.Canonical.ConnesArakiFramework`
- `InfoGeometry.Canonical.MasterSynthesis`
- `InfoGeometry.Canonical.YangMillsContinuum`

### Rotation / flow / fluid layer

- `InfoGeometry.Krein.HilbertBridge`
- `InfoGeometry.Krein.Clifford`
- `InfoGeometry.Canonical.AnomalyGauge`
- `InfoGeometry.Canonical.NavierStokesBridge`
- `InfoGeometry.Canonical.PathIntegral`

## Current-Source Intra-Vicinity DAG

The following import edges are the highest-signal theory edges inside the
keyword vicinity.

### Spine A: singular inverse geometry

- `InfoGeometry.Singular.Drazin -> InfoGeometry.Singular.MoorePenrose`
- `InfoGeometry.Singular.KreinNaturalFlow -> InfoGeometry.Singular.Drazin`
- `InfoGeometry.Canonical.Singular -> InfoGeometry.Singular.Drazin`
- `InfoGeometry.Canonical.SpectralInference -> InfoGeometry.Canonical.Singular`

Interpretation:

- the singular inverse layer feeds the canonical spectral bridge
- the canonical spectral bridge is the entry point through which singularity
  data enters most of the modern canonical stack

### Spine B: canonical spectral bridge

- `InfoGeometry.Canonical.SpectralInference -> InfoGeometry.Canonical.MoorePenrose`
- `InfoGeometry.Canonical.BeliefDynamics -> InfoGeometry.Canonical.SpectralInference`
- `InfoGeometry.Canonical.RicciMongeAmpere -> InfoGeometry.Canonical.SpectralInference`
- `InfoGeometry.Canonical.TopologicalInvariants -> InfoGeometry.Canonical.SpectralInference`
- `InfoGeometry.Canonical.ChiralRGFlow -> InfoGeometry.Canonical.SpectralInference`

Interpretation:

- `SpectralInference` is the main spectral junction
- it is already a stronger canonicalization target than the older singular files

### Spine C: anomaly to conformal

- `InfoGeometry.Canonical.ChiralAnomaly -> InfoGeometry.Canonical.MoorePenrose`
- `InfoGeometry.Canonical.ChiralEinsteinBridge -> InfoGeometry.Canonical.ChiralAnomaly`
- `InfoGeometry.Canonical.ConformalUnification -> InfoGeometry.Canonical.ChiralEinsteinBridge`
- `InfoGeometry.Canonical.ConformalUnification -> InfoGeometry.Canonical.MoorePenrose`
- `InfoGeometry.Canonical.ConformalUnification -> InfoGeometry.Canonical.GrandSynthesis`

Interpretation:

- the conformal layer is not rooted directly in `AnomalyGauge`
- it is rooted in the Moore-Penrose / spectral / Einstein bridge stack

### Spine D: conformal downstream fan-out

- `InfoGeometry.Canonical.ConformalAlgebra -> InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.BerryPhase -> InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.ChiralAction -> InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.ChiralTorsionBridge -> InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.ConformalWard -> InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.WeylInformationGauge -> InfoGeometry.Canonical.ConformalUnification`
- `InfoGeometry.Canonical.AnomalyDilationBridge -> InfoGeometry.Canonical.ConformalUnification`

Interpretation:

- `ConformalUnification` is the central canonical anomaly/conformal hub

### Spine E: holography / count substrate

- `InfoGeometry.Canonical.HolographicEmergence -> InfoGeometry.Canonical.ChiralTorsionBridge`
- `InfoGeometry.Canonical.HolographicEmergence -> InfoGeometry.Canonical.WeylInformationGauge`
- `InfoGeometry.Canonical.CountSubstrateBridge -> InfoGeometry.Canonical.HolographicEmergence`

Interpretation:

- holography is strictly downstream of the conformal/anomaly stack
- count-substrate logic is a facade over that already downstream layer

### Spine F: RN / volume / modular

- `InfoGeometry.Volume.ConnesCocycle -> InfoGeometry.Volume.RadonNikodym`
- `InfoGeometry.Canonical.UniversalVolume -> InfoGeometry.Volume.RadonNikodym`
- `InfoGeometry.Canonical.UniversalVolume -> InfoGeometry.Volume.ConnesCocycle`
- `InfoGeometry.Canonical.TomitaTakesaki -> InfoGeometry.Volume.ConnesCocycle`
- `InfoGeometry.Canonical.BekensteinBound -> InfoGeometry.Volume.ConnesCocycle`
- `InfoGeometry.Canonical.YangMillsContinuum -> InfoGeometry.Volume.ConnesCocycle`

Interpretation:

- `Volume.RadonNikodym` is the root of the volume/modular side
- `ConnesCocycle` is the modular transport hub on top of it
- `TomitaTakesaki` is now a named specialization on that shared hub

### Spine G: entropy barrier and modular consumers

- `InfoGeometry.Canonical.BekensteinBound -> InfoGeometry.Canonical.GrandCanonicalExperts`
- `InfoGeometry.Canonical.ConnesArakiFramework -> InfoGeometry.Canonical.BekensteinBound`
- `InfoGeometry.Canonical.MasterSynthesis -> InfoGeometry.Canonical.BekensteinBound`
- `InfoGeometry.Canonical.MasterSynthesis -> InfoGeometry.Canonical.UniversalVolume`
- `InfoGeometry.Canonical.MasterSynthesis -> InfoGeometry.Canonical.YangMillsContinuum`

Interpretation:

- `GrandCanonicalExperts` is the RN-barrier / entropy source
- `BekensteinBound` is the modular/entropy consumer
- `ConnesArakiFramework` and `MasterSynthesis` are already downstream packaging layers

### Spine H: rotation and fluidization

- `InfoGeometry.Canonical.AnomalyGauge -> InfoGeometry.Singular.Drazin`
- `InfoGeometry.Canonical.NavierStokesBridge -> InfoGeometry.Canonical.Singular`
- `InfoGeometry.Canonical.NavierStokesBridge -> InfoGeometry.Canonical.GrandCanonicalExperts`
- `InfoGeometry.Krein.Clifford -> InfoGeometry.Krein.HilbertBridge`
- `InfoGeometry.Krein.Metric -> InfoGeometry.Krein.HilbertBridge`

Interpretation:

- the "singularity turning into rotation" story still lives partly on the older
  singular gauge side and partly on the modern conformal side
- the fluid bridge consumes the singular anomaly layer, not the conformal bridge

## Reverse-Import Hubs

Direct importer counts for the main thematic hubs:

- `InfoGeometry.Canonical.SpectralInference`: 16
- `InfoGeometry.Canonical.TomitaTakesaki`: 11
- `InfoGeometry.Canonical.ConformalUnification`: 10
- `InfoGeometry.Canonical.KMSSinkhornBridge`: 7
- `InfoGeometry.Volume.ConnesCocycle`: 4
- `InfoGeometry.Canonical.BekensteinBound`: 3
- `InfoGeometry.Canonical.Singular`: 3
- `InfoGeometry.Canonical.AnomalyGauge`: 2
- `InfoGeometry.Canonical.BeliefDynamics`: 2
- `InfoGeometry.Volume.RadonNikodym`: 2

Interpretation:

- the actual canonical hubs are `SpectralInference`, `ConformalUnification`,
  `TomitaTakesaki`, `KMSSinkhornBridge`, `ConnesCocycle`
- `AnomalyGauge` is not a hub; it is a narrow singular-boundary specialist

## Definition-Level Duplication Hotspots

### Chiral anomaly

Multiple anomaly objects coexist:

- `InfoGeometry.Singular.Drazin.ChiralAnomaly`
- `InfoGeometry.Singular.DrazinAdjoint.ChiralAnomaly`
- `InfoGeometry.Canonical.MoorePenrose.chiralAnomaly`
- `InfoGeometry.Canonical.ConformalUnification.chiralAnomaly`
- `InfoGeometry.Canonical.ConformalUnification.rightChiralAnomaly`

Current status:

- this is not pure duplication anymore
- there is a real categorical split:
  - raw singular inverse commutator
  - canonical projector mismatch
  - left-projector conformal anomaly
  - right-projector Einstein anomaly convention

Canonicalization target:

- make `ConformalUnification` the canonical public anomaly hub
- treat singular definitions as source-layer constructions
- keep the right/left projector split explicit and derived, not co-equal public centers

### Einstein anomaly

- `InfoGeometry.Canonical.Singular.EinsteinAnomaly`
- bridged in `ConformalUnification` via
  `einsteinAnomaly_eq_neg_rightChiralAnomaly`

Canonicalization target:

- keep `Canonical.Singular` as source object
- expose the conformal theorem layer as the public semantic identity

### RN layers

Distinct RN-related notions coexist:

- discrete measure-theoretic RN:
  - `InfoGeometry.Measure.DiscreteRN`
  - `InfoGeometry.Measure.Normalized`
- abstract volume RN:
  - `InfoGeometry.Volume.RadonNikodym`
- Hessian surrogate RN:
  - `InfoGeometry.Canonical.BeliefDynamics.radonNikodymOp`
- Sinkhorn barrier generators:
  - `rowRadonNikodymGenerator`
  - `colRadonNikodymGenerator`
- KMS/Sinkhorn local ratio:
  - `KMSSinkhornBridge.ibRNDerivative`
- IB genuine measure-side RN:
  - `InfoGeometry.Canonical.IBMeasure`

Canonicalization target:

- do not collapse these by name alone; they live in different categories
- but they should be documented as a chain:
  discrete RN -> normalized log potential -> abstract volume RN ->
  modular cocycle -> Sinkhorn/KMS generator -> measure-theoretic IB RN

### Volume / log-volume naming

Still separate layers:

- determinant-bundle action on volume forms
- `Volume.RadonNikodym` scalar bridge
- `UniversalVolume`
- spectral log-volume in `RicciMongeAmpere` / `HeatKernel`

Canonicalization target:

- use `log-volume` explicitly when the quantity is not a true volume form
- reserve `volume form` for determinant-bundle / measure transport layers

### Rotation / fluid generator

There are two conceptually different rotation stories:

- geometric/skew-adjoint anomaly rotation:
  - `Canonical.AnomalyGauge`
- coordinate/bridge rotation:
  - `Krein.HilbertBridge.rotation45`
  - `Krein.Clifford`

Canonicalization target:

- keep `rotation45` as chart/representation transport
- keep anomaly-as-rotation as a Lie/gauge layer
- do not blur them in downstream naming

## Category-Level Reading of the Theory DAG

The theory currently spans these effective categories:

1. Singular generalized inverse category
2. Canonical spectral projector category
3. Conformal/anomaly category
4. Modular cocycle / additive modular flow category
5. RN / volume transport category
6. Sinkhorn/KMS entropy-barrier category
7. Fluid / rotation / gauge-flow category
8. Holographic / boundary emergence category

The real integration bridges are:

- `SpectralInference`
- `ConformalUnification`
- `Volume.ConnesCocycle`
- `TomitaTakesaki`
- `BekensteinBound`
- `KMSSinkhornBridge`
- `MasterSynthesis`

## Highest-Value Canonicalization Targets

1. Unify public anomaly semantics around `ConformalUnification`
   - treat singular anomaly files as source-level implementations
   - keep theorem bridges to Einstein/right-projector conventions explicit

2. Elevate `SpectralInference` over raw singular files
   - more of the downstream stack should depend on certified spectral packages,
     not directly on raw witness-level singular definitions

3. Make RN layering explicit across categories
   - discrete RN
   - volume RN
   - modular cocycle
   - Sinkhorn barrier
   - IB RN

4. Route rotation/fluid semantics through explicit bridge theorems
   - anomaly-as-rotation
   - singularity-to-fluid bridge
   - avoid mixing with representation rotations like `rotation45`

5. Keep `TomitaTakesaki` as the named modular specialization hub
   - downstream modular consumers should use Tomita-specific wrappers when the
     semantics are fixed, not abstract `σ` surfaces

## Practical Next Steps

1. Add a canonical "anomaly semantics" facade that re-exports:
   - conformal anomaly
   - Einstein anomaly bridge
   - unit-of-action / chiral-scale identification
   - left/right projector agreement conditions

2. Add an RN taxonomy note or facade module connecting:
   - `Measure.DiscreteRN`
   - `Volume.RadonNikodym`
   - `ConnesCocycle`
   - `GrandCanonicalExperts`
   - `KMSSinkhornBridge`
   - `IBMeasure`

3. Refactor downstream singular-flow consumers
   - especially fluid / gauge / holographic consumers
   - toward certified spectral/conformal interfaces where possible

4. Run the full Lean DAG exporters offline for declaration-level skeleton output
   - useful for exact vulnerability ranking
   - not required for the category map above, but required for a full
     declaration-level blueprint extraction
