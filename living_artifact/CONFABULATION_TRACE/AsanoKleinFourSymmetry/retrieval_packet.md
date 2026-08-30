# RetrievalPacket: AsanoKleinFourSymmetry

## Contextual Orientation
**Corridor:** `Thermodynamics/AsanoKleinFourSymmetry.lean`
**Upstream Dependencies:**
- `InfoGeometry.Thermodynamics.SouriauBostConnesFlow` — Metriplectic flow on inverse temperature
- `InfoGeometry.Thermodynamics.ProjectiveTemperature` — Stereographic Lee-Yang circle coordinates
- `InfoGeometry.Canonical.CayleyCriticalLineCircleBridge` — Critical line ↔ unit circle via Cayley
- `InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint` — Topological endpoint proof
- `InfoGeometry.Canonical.LeeYangAsanoKleinV4Compactification` — V₄ compactification certificate

## Key Theorems Retrieved
1. `v4Action_preserves_LeeYangCircle` — V₄ action preserves unit circle
2. `v4Action_preserves_LeeYangCircle` — V₄ action preserves unit circle (theorem)
3. `v4_orbit_on_LeeYangCircle` — V₄ orbit of any point on circle stays on circle
4. `forbiddenSet_disjoint_LeeYangCircle` — Forbidden set disjoint from Lee-Yang circle

## Local Proof State
**Target:** Prove `AsanoCompactificationWitness` can be instantiated by a concrete prime/Majorana system.
**Obstructions:**
1. `MertensDefectBoundary` — Requires finite Möbius magnetization data
2. `ZeroModeProtectionPacket` — Requires Majorana zero-mode gate
3. `PrimeSUSYVacuumBridge` — 8 analytic laws (witten index, boson/fermion cancellation, etc.)

## Corridor Placement
This socket sits at the interface between:
- **Thermodynamics layer** (Asano V₄ symmetry, Lee-Yang circle)
- **Arithmetic layer** (PrimeSUSYVacuum, Bost-Connes)
- **Canonical layer** (Asano-Ruelle topological endpoint, Lee-Yang/Hurwitz bridge)

## Authority Level
`retrieval` — Contextual orientation complete. Ready for proof-state localization.