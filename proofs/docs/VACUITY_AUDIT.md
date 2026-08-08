# Vacuity Audit

Generated after searching the Lean proof tree for declarations of the form
`Prop := True`, `∃ _, True`, `fun _ => True`, top-level `axiom`, and `sorry`.

## Summary

The current `InfoGeometry` master target builds, but the repository still
contains older extracted/prototype files with vacuous propositions and axioms.
Most are not part of the current theorem-honest capstone path, but they should
be replaced, quarantined, or renamed as sockets before being cited.

## Direct vacuous proposition definitions

### `proofs/EmergentSpacetimeAnsatz.lean`

- `emergent_spacetime_ansatz : Prop := True`

Replacement direction:

- Replace by a structure with explicit hypotheses, or point to existing finite
  anchors:
  - `EinsteinThermodynamicBridge.no_bare_singularities`
  - `InformationGeometricCutoff.fractal_resolution_limit`
  - `BlackHoleHolography.black_hole_area_quantization`

### `proofs/GT_FromText.lean`

Vacuous definitions:

- `flow_is_steady_state : Prop := True`
- `is_dirac_hodge : Prop := True`
- `is_dirac := True`
- `preserves_natural_cone : Prop := True`
- `twisted_index_vanishing : Prop := True`
- `is_kms_equilibrium_at_crit_point : Prop := True`
- `g_is_einsteinian : Prop := True`
- `topologyIsKleinBottle : Prop := True`
- `is_dirac_energy : Prop := True`
- `Topology.IsKleinBottle : Prop := True`

Replacement directions:

| Vacuous target | Existing non-vacuous replacement anchors |
| --- | --- |
| `is_kms_equilibrium_at_crit_point` | `GoldenCCR.exp_neg_penroseBeta`, `GoldenCCR.qPenrose_interior` |
| `topologyIsKleinBottle`, `Topology.IsKleinBottle` | `SuperBerezinianKlein.pgGlide_sq`, `GlideSymmetricInvariant.hamiltonian_preserves_plus_eigenspace`, `GlideSymmetricInvariant.hamiltonian_preserves_minus_eigenspace` |
| `g_is_einsteinian` | `EinsteinThermodynamicBridge.no_bare_singularities` as scalar equation-of-state anchor |
| `is_dirac_hodge`, `is_dirac`, `is_dirac_energy` | `GoldenSpectralTriple.dirac_creates_particle_metric`, `FractalHamiltonian.fibHamiltonian2_symmetric` |
| `twisted_index_vanishing` | `SuperBerezinianKlein.trifactor_plus_minus_orthogonal`, `GlideSymmetricInvariant` eigensector preservation; full index remains socket |
| `preserves_natural_cone` | `InformationGeometricCutoff.fractal_resolution_limit`, `minimal_phase_space_volume_pos`; full natural-cone theorem remains socket |
| `flow_is_steady_state` | No full Lean proof yet; nearest witnesses are `klein_metriplectic_flow.py` and `DiracKreinMetriplectic.MetriplecticCutoffSocket` |

Recommendation:

- Treat `GT_FromText.lean` as an extraction scratchpad, not a proof module.
- Either move it under `_deprecated/` or rewrite it as a socket-only file with no
  top-level axioms and no `Prop := True` declarations.

## Existentially vacuous declarations

### `proofs/FockSpaceDerivation.lean`

- `∀ h : X.det = 0, ∃ (ψ : H₁), True`
- `fun _ => True`

Replacement direction:

- Use `GoldenSpectralTriple.GoldenFockSpace` and
  `GoldenSpectralTriple.dirac_creates_particle_metric` for a concrete first
  particle-sector statement.
- Use `golden_fock_gram.py` as a witness for positivity in binary sectors `n=2,3`.
- Full q-Fock construction remains `QFockPositivitySocket`.

## Top-level axioms in non-deprecated files

- `LieFlowMatching.lean`: `powerScheduleCompression`
- `KreinVacuumKMSBridge.lean`: `kms_state`, `kms_is_cyclic`
- `proofs/_deprecated/removed_from_default_2026_06_15/PlatycosmKTheory.lean`: `platycosm_k_theory_iso`
- `GT_FromText.lean`: multiple extracted conjectural axioms

Replacement strategy:

1. Move extracted/conjectural files out of active roots if they are not intended
   as kernel assumptions.
2. Replace axioms with explicit `structure ... Socket where` fields.
3. Add finite anchors where possible, following the pattern used in:
   - `InformationGeometricCutoff.lean`
   - `EinsteinThermodynamicBridge.lean`
   - `GlideSymmetricInvariant.lean`
   - `BraidIdealDescent.lean`

## Current clean capstone path

The current `InfoGeometry` target builds and uses theorem-honest finite anchors
plus sockets.  The most recent build status:

```text
lake build InfoGeometry
Build completed successfully (8043 jobs).
```

The presence of older vacuous/prototype files elsewhere in `proofs/` should not
be confused with the status of the capstone path, but they should be audited
before any repository-wide claim of zero vacuity.
