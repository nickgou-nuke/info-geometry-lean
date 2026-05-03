# Analytic Debt Audit (2026-03-14)

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

## Build Status
- `lake build -R`: PASS
- Syntactic status: no errors; warnings only (mostly linter/style).

## Debt Ledger

### 1) Drazin Inverse Gap
- Status: CLOSED in canonical layer.
- Constructive theorem now present and compiling:
  - `InfoGeometry.Canonical.Singular.exists_drazinInverse_global`
- Route:
  - imported finite-dimensional Fitting-based construction from `InfoGeometry.Singular.DrazinAdjoint.exists_drazinInverse_global`
  - translated into canonical predicate `InfoGeometry.Canonical.Drazin.IsDrazinInverse` for `E →L[ℝ] E`.

### 2) Topological Deformation Gap
- Status: PARTIALLY CLOSED (with explicit no-crossing hypothesis).
- Existing constructive core:
  - `chiralSliceIsoAlong_of_noZeroEigenCrossing`
  - `indexInvariantAlong_of_noZeroEigenCrossing`
  - `chiralSliceIsoAlong_of_conjugacy`
  - `chiralSliceIsoAlong_of_modularCliffordTransport`
- Added this cycle:
  - `chiralSliceIsoAlong_of_continuous_path`
  - `indexInvariantAlong_of_continuous_path`
- Important boundary:
  - continuity + grading alone does not force slice isomorphism in general;
  - no-zero-eigenvalue-crossing (or equivalent spectral-gap protection) remains the mathematically correct closure condition currently formalized.

### 3) IB Contraction Gap
- Status: OPEN (core contraction estimate still missing).
- Existing Banach closure:
  - `tendsto_ibTrajectory_fixedPoint` requires `hContr : ContractingWith Kc ...`.
- Added this cycle (small-step decomposition):
  - `ibBlahutArimotoStep_contracting_of_lipschitz`
  - `tendsto_ibTrajectory_fixedPoint_of_lipschitz`
- Remaining constructive target:
  - prove a concrete Lipschitz/strict-contraction bound for
    `ibBlahutArimotoStep` under a chosen metric on encoder space.

### 4) Ricci-Flatness Vacuum Gap
- Status: OPEN.
- Current blocker is structural:
  - `IsRicciFlat (R : RicciTensor E)` is predicate on an abstract tensor;
  - `relativeVolumeChangeRN = 1` currently lives in Sinkhorn/log-det layer;
  - no theorem yet links unit RN volume directly to vanishing Ricci tensor without extra geometric identification assumptions.
- Required next bridge:
  - derive Ricci from the metric/log-det object in the same theorem context,
    then prove vanishing curvature under unit-volume/fixed-point conditions.

## New Obstacles Identified
1. **Metric mismatch for IB contraction**:
   no canonical metric instance currently tied to BA geometry (e.g. Birkhoff/Hilbert metric on positive simplex) in `IBCore`.
2. **Ricci abstraction gap**:
   `RicciTensor` is too unconstrained for `relativeVolumeChangeRN = 1 -> IsRicciFlat` unless we fix a derived Ricci model in hypothesis/data.
3. **Topological frontier naming vs theorem truth**:
   continuity-only formulation must not be used as closure claim without no-crossing/gap assumptions.

## Immediate Next Constructive Targets

### A) IB contraction (next actionable)
1. Define the concrete encoder metric space used for BA contraction.
2. Prove one-step Lipschitz estimate:
   - `LipschitzWith Kc (ibBlahutArimotoStep prob)`
3. Discharge strictness `Kc < 1` from BA/KL coercivity assumptions.
4. Apply `tendsto_ibTrajectory_fixedPoint_of_lipschitz`.

### B) Ricci-flatness from unit volume
1. Introduce a theorem context where Ricci is explicitly metric-derived (not arbitrary tensor).
2. Prove zero scalar flow from normalized + fixed-point conditions (already available in scalar layer).
3. Lift scalar zero to Ricci-flat statement in that derived context.
4. Export as `isRicciFlat_of_unit_relativeVolume` with explicit derivation path.

### C) Topological route hardening
1. Keep using no-crossing/gap-protected route as canonical.
2. If desired later: prove `ChiralNoZeroEigenCrossingNear` from a verified modular transport/conjugacy condition in the same module.
