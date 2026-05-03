# Repo Surface Audit — 2026-04-13

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

## Scope
Full integration check across:
- Lean sources (`*.lean`)
- Markdown docs (`*.md`)
- Python tooling (`*.py`)
- Configuration/manifests (`*.json|*.yaml|*.yml|*.toml|*.ini|*.cfg|*.lock`)

## Inventory
Tracked files (`git ls-files`):
- Lean: 787
- Markdown: 355
- Python: 189
- Config: 116

Current untracked additions (`git status --short`):
- Lean: 12
- Markdown: 9
- Python: 0
- Config: 8

## Canonical lane integration status
New real-doubled modular/Kramers closure surfaces present in working tree:
- `TomitaTakesakiRealStandardForm.lean`
- `ModularOrientationContract.lean`
- `RealTomitaCore.lean`
- `WedgeBoostModularBridge.lean`
- `TypeIIIContinuousCoreReal.lean`
- `ModularKramersBridge.lean`
- `KramersPhaseAxisReduction.lean`
- `KramersMajoranaCompatibility.lean`
- `DrazinModularSingularityBridge.lean`
- `KKTNoetherCharges.lean`
- `ModularSuperchargeClosure.lean`

`Canonical/All.lean` imports this lane (including `WedgeBoostModularBridge`).

## Build verification
Direct owners:
- `lake build InfoGeometry.Canonical.TomitaTakesakiRealStandardForm` ✅
- `lake build InfoGeometry.Canonical.RealTomitaCore` ✅
- `lake build InfoGeometry.Canonical.ModularKramersBridge` ✅
- `lake build InfoGeometry.Canonical.KramersPhaseAxisReduction` ✅
- `lake build InfoGeometry.Canonical.KramersMajoranaCompatibility` ✅
- `lake build InfoGeometry.Canonical.KKTNoetherCharges` ✅
- `lake build InfoGeometry.Canonical.DrazinModularSingularityBridge` ✅
- `lake build InfoGeometry.Canonical.ModularSuperchargeClosure` ✅
- `lake build InfoGeometry.Canonical.WedgeBoostModularBridge` ✅

Umbrella targets:
- `lake build InfoGeometry.Canonical.All` ✅
- `lake build InfoGeometry.All` ✅

Status: clean compile with pre-existing lint warnings only.

## Fixes performed during this audit
1. Repaired `WedgeBoostModularBridge.lean` elaboration failures:
- removed invalid named implicit arguments on scalar-only normalization maps
- normalized wedge/modular parameter calls
- qualified `chiralBoost` reference

2. Removed the modular assumption gate in `ModularSuperchargeClosure`:
- introduced canonical seed `h_mod := -(H_D ∘ K)`
- derived `H_D = modularTransportGenerator(h_mod)` internally
- made `ModularSuperchargeCompatibility` assumption-free on even/generator equality

3. Integrated `KramersPhaseAxisReduction` into `KramersMajoranaCompatibility`:
- canonical reduction factor alias `R := -(Θ ∘ K)`
- reduction identity `Θ = R ∘ K`
- Majorana closure theorem for the canonical reduction factor
- unified reduction/compatibility package theorem

4. Refactored canonical Tomita/wedge bridge wiring in `ModularSuperchargeClosure`:
- removed the intermediary `TomitaWedgeCompatibility` witness layer
- exposed direct lower-owner bridge theorems:
  - `flow_at_wedgeParameter`
  - `flow_eq_unruh_modular_polynomial`
- kept backward-compatible aliases:
  - `flow_at_wedgeParameter_of_wedgeCompatibility`
  - `flow_eq_unruh_modular_polynomial_of_wedgeCompatibility`
- revalidated the lane with `lake build InfoGeometry.Canonical.ModularSuperchargeClosure`

5. Added declaration-cloud movie exporter:
- new infra tool `tools/infra/generate_theory_cloud_movie.py`
- modes: `structural`, `semantic`, `commits`
- bounded particle relaxation (node/edge caps, local spatial hashing repulsion)
- optional commit interpolation and ffmpeg render path

## Remaining closure debt (unchanged)
1. `Canonical/DrazinSpectralBridge.lean` remains scaffold-only.
2. Strong non-scalar intrinsic internal central candidate in the Drazin lane still needs capstone centrality/index-shadow closure.
3. Tomita/wedge identification capstone is still pending: canonical modular-seed closure is in place, but explicit equality with the owned wedge-normalized Tomita generator lane is not yet discharged.
