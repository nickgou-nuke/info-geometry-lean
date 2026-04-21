# Corridor F theorem-distillation memo

Corridor:
- Drazin / Moore–Penrose / Operator Ratio / Lightcone / Regularized Support

Black-book source shards reviewed:
- `00w_drazin_penrose_lightcone_projectors_and_casimir_gravity.md`
- `00x_operator_ratio_physical_sector_and_stability_map.md`
- `00z_pfaffian_bps_python_module_and_stability_index.md`
- `00ag_topological_closure_axioms_and_final_signature.md`

Primary repo surfaces checked:
- `lean/InfoGeometry/Canonical/Drazin.lean`
- `lean/InfoGeometry/Canonical/MoorePenrose.lean`
- `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`
- `lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean`

## 1. Core symbolic claims in Corridor F

Recurring claims in the source shards:

1. Singular operator regimes should be handled by Drazin and Moore–Penrose regularization, not naive inversion.
2. Drazin isolates the nilpotent / topological / memory-like core.
3. Moore–Penrose isolates the physical / metric / visible sector.
4. The light cone is a singular support/filtering surface rather than a passive boundary.
5. Projector algebra separates physical shell vs protected core.
6. The meaningful replacement for a global operator ratio is a support-restricted regularized corridor.
7. BPS/zero-mode language should be attached to the protected/singular kernel lane, not to naive determinant rhetoric.

The strongest of these claims are already much closer to repo-native owner language than many of the other black-book corridors.

## 2. What is already owner-backed in the repo

### A. Canonical Drazin inverse and spectral projector lane is owned

`Drazin.lean` already owns:
- `IsDrazinInverse`
- `projection`
- `complementaryProjection`
- idempotence / orthogonality / decomposition theorems
- uniqueness of the Drazin inverse witness
- `core` / `nilpotent` decomposition

This means the repo already has a real algebraic owner lane for:
- regular/core part,
- nilpotent/defect part,
- projector decomposition attached to Drazin witnesses.

So the black-book intuition that Drazin isolates a protected/singular/core sector is not merely metaphor; it has a real owner surface.

### B. Canonical Moore–Penrose projector lane is owned

`MoorePenrose.lean` already owns:
- `IsMoorePenroseInverse`
- `rightProjector`
- `leftProjector`
- idempotence and self-adjointness theorems
- `spectralProjector`
- `metricProjector`
- `projectorMismatch`
- `chiralAnomaly`
- `epsilon` / `chiralScale`

This means the repo really distinguishes:
- spectral projector data,
- metric projector data,
- their mismatch/anomaly.

So the black-book talk of a Penrose shell vs Drazin core does have a formal algebraic backbone, though the prose often over-embellishes the physical interpretation.

### C. CertifiedInverseKernel is the actual proof-carrying center

`CertifiedInverseKernel.lean` already owns the combined package:
- `A`, `A_D`, `A_MP`
- `hDrazin`
- `hMoorePenrose`

Derived canonical objects include:
- `spectralProjector`
- `mpRangeProjector`
- `metricProjector`
- `projectorMismatch`
- `chiralAnomaly`
- `rightChiralAnomaly`
- `dilationGap`
- `chiralScale`

This is the real center of the corridor.
The repo itself already says downstream surfaces should adapt to this kernel rather than rebundle inverse data ad hoc.

### D. Drazin–Penrose dilation algebra is explicitly owned

`DrazinPenroseDilationAlgebra.lean` already packages the canonical generators:
- `P_D`
- `P_L`, `P_R`
- spectral Cartan generator
- geometric Cartan generator
- dilation generator
- projector mismatch generator
- left/right anomaly generators

So black-book language about algebraic splitting, defect generators, and dilation/gap structure is strongly supported here.

### E. The support-restricted operator-ratio corridor is already named and theorem-backed

This is the most important result for Corridor F.

`DrazinModularSingularityBridge.lean` already owns:
- `certified_operator_ratio_regularization_corridor`
- `certified_operator_ratio_regularization_kills_defect_of_alignment`
- `certified_operator_ratio_regularization_kills_defect_of_inertial_lane`

And the theorem text itself states the corridor cleanly:
- do not form a global ratio across the defect kernel,
- separate `Preg`, `Pzero`, `Pmetric`,
- log only on the regular lane,
- use support and alignment criteria for the remaining physical compression.

This is almost exactly the theorem-factory extraction that the black-book source is reaching for.

### F. Finite singular support truncation is also already owned

`RelativeModularSingularization.lean` already owns a finite model of singularization:
- `supportProjector`
- `singularRelativeModularOperator`
- `singularRelativeModularPseudoInverse`
- support-truncated modular operator/pseudoinverse relations

This is valuable because it gives a concrete finite model of the same support-restricted logic before passing to the more abstract certified inverse-kernel lane.

## 3. What is only partially owned / still requires theorem work

### A. “Drazin core” and “Penrose shell” as physics names

The underlying algebra is real.
But the exact physical nomenclature:
- Drazin core = topological memory phase
- Penrose shell = dissipative thermodynamic shell

is still partly black-book rhetoric unless tied to specific repo theorems and readouts.

Safer owner-level phrasing is:
- Drazin regular/core projector lane,
- Moore–Penrose metric/range lane,
- support-restricted physical compression,
- mismatch/anomaly as owned algebraic obstruction.

### B. Full light-cone / chirality / gravitational interpretation

The source shards repeatedly speak about:
- light cone as active filter,
- BPS states moving at the speed of light,
- direct gravitational interpretation of the singular lanes.

The repo does have:
- chiral anomaly language,
- lightcone-related bridge files elsewhere,
- support-restricted modular singularization,
- Drazin/Penrose algebra.

But the fully assembled physical statement in those exact words is not yet one owner theorem package in the files checked here.

Status:
- conceptually aligned,
- still partly bridge/capstone.

### C. Pfaffian/Zeta/BPS simulation rhetoric in this corridor

The source often merges:
- projector algebra,
- Pfaffian index language,
- zeta regularization,
- BPS simulation stories,
- cosmological claims.

Those belong partly to Corridor G/H/I, not purely to Corridor F.
So the theorem factory should keep Corridor F focused on:
- inverse/projector/support regularization algebra
and not allow it to overgrow into total cosmological interpretation.

## 4. Owner-level statements we can already safely extract

These are safe, repo-faithful statements:

1. The Drazin inverse provides a canonical projector decomposition into regular and complementary/defect sectors.

2. The Moore–Penrose inverse provides left/right projector data with self-adjoint/idempotent structure.

3. The combined Drazin/Penrose package is owned by `CertifiedInverseKernel`, which is the proof-carrying center for inverse/projector/anomaly data.

4. The spectral and metric projector lanes need not coincide; their mismatch and commutator are explicit owned objects.

5. The meaningful replacement for a naive global operator ratio is a support-restricted regularization corridor:
   - form the logarithm only on `Preg`,
   - exclude `Pzero`,
   - compress physically through `Pmetric` only after alignment criteria are stated.

6. There is already a named theorem surface explicitly certifying this operator-ratio regularization corridor.

7. Finite support truncation already provides a concrete singularized model of the same logic.

## 5. Statements that must remain marked as debt/proposal

These should not yet be promoted as already proved:

1. That the “Drazin core” and “Penrose shell” physical interpretations are fully theorem-derived in the strong black-book sense.
2. That light-cone/BPS/gravity language attached to these projectors is already closed by the inverse-kernel files alone.
3. That Pfaffian/zeta/cosmological stories are already part of the same owner theorem package as the operator-ratio regularization corridor.
4. That dark-matter / holographic / Klein-bottle interpretations are already consequences of the Drazin/Penrose support algebra.

## 6. Best next theorem targets for Corridor F

Priority theorem targets:

1. Strengthen the finite-to-certified singular bridge
- connect `RelativeModularSingularization` more explicitly to `CertifiedModularReduction` / `CertifiedInverseKernel` as a finite witness model of the same support logic.

2. Clarify the physical-lane compression semantics
- add explicit theorems or docs explaining when `Kphys` is the only lawful physical readout after `Preg` and `Pmetric` compression.

3. Keep the corridor pure
- isolate projector/support/inverse algebra from the Pfaffian/zeta/cosmology layer;
- only rejoin them later through named bridge theorems.

4. If desired later
- connect chiral/lightcone files to the Drazin/Penrose regularization corridor with exact theorem names rather than metaphorical identification.

## 7. Pauli-style closure status for Corridor F

ROLE:
- strongly owner-backed operator corridor with good existing theorem packaging

SEMANTIC_FIDELITY:
- high for support restriction / Drazin / Penrose / mismatch / anomaly claims
- medium for the “core vs shell” physical naming
- low-to-medium for the overextended gravity/cosmology interpretations in the source shards

THEOREM_STRENGTH:
- high on inverse/projector/support algebra
- high on the operator-ratio regularization corridor
- medium on physical interpretation bridges

CLOSURE_STRENGTH:
- owner-closed on the algebraic regularization corridor
- bridge-valid-but-not-closed on the stronger physical/lightcone/BPS interpretation layer
- capstone-only on cosmological overgrowth

PROMOTION_ALLOWED:
- yes for the algebraic/support-restricted operator-ratio statements listed in section 4
- no for the stronger physical or cosmological claims listed in section 5

## 8. Recommended extraction order inside Corridor F

Extract in this order:

1. `00x` -> operator-ratio / Penrose-vs-Drazin segregation language
2. `00w` -> Drazin / Moore–Penrose / lightcone projector pressure
3. `00z` -> only the parts that reinforce support/protected-core logic, not the simulation cosmology rhetoric
4. `00ag` -> only where it restates topological closure in algebraic terms; keep the dark-matter/holography claims marked as capstone

This preserves the strongest existing owner corridor in the black-book material and prevents it from being diluted by later metaphysical extension layers.
