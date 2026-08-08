# Release Notes: v1.0.0-gravity

Title: **Initial Release: The Information Geometry of Quantum Gravity**

## Summary

This release publishes the theorem-honest Lean 4 / SymPy proof architecture for `info-geometry-lean` under Apache-2.0, with citation metadata and disclosed AI-coding-agent collaboration.

The master Lean target builds successfully:

```bash
cd proofs
lake build InfoGeometry
```

Last verified result:

```text
Build completed successfully (8043 jobs).
```

## Highlights

- Master manifest: `proofs/InfoGeometry.lean`
- Apache-2.0 license: `LICENSE`
- Citation metadata: `CITATION.cff`
- Zenodo metadata: `.zenodo.json`
- AI collaboration disclosure: `AI_COLLABORATION.md`
- Architecture whitepaper/manifest: `docs/INFOGEOMETRY_MANIFEST.md`

## Formalization Stack

The release aggregates proof anchors for:

1. split Clifford/CPT kinematics;
2. q-CCR/CAR and Cuntz--Toeplitz deformation sockets;
3. Penrose/PGA projective geometry;
4. noncommutative tiling algebra and `ℤ + φℤ` gap labels;
5. convex algebraic duality / spectrahedral sockets;
6. golden q-CCR scalar bridge `q = φ⁻¹`;
7. finite Fibonacci Hamiltonian anchors;
8. black-hole entropy scalar holography;
9. golden Fock / spectral triple sockets;
10. information-geometric cutoff via Itakura--Saito and Cramér--Rao;
11. scalar thermodynamic Einstein/Jacobson bridge;
12. unified gauge-field / TKK socket;
13. Dirac/Krein metriplectic modular bridge;
14. Super-Berezinian / Klein-glide anchors;
15. glide-symmetric `ℤ₂` eigensector protection;
16. canonical Peirce tripotent anchors;
17. braid ideal descent / q-cross map socket.

## Key Lean Theorems / Anchors

- `clnn_succ_factor`
- `FibR_pf_eigen`
- `gap_labeling_trace_scaling`
- `tileFrequency_eq_evalTrace`
- `toeplitz_range_defect_projection`
- `exp_neg_penroseBeta`
- `qPenrose_interior`
- `fibHamiltonian2_symmetric`
- `qPenrose_eq_gapLabel`
- `black_hole_area_quantization`
- `dirac_creates_particle_metric`
- `itakuraSaito_scale_invariant`
- `fractal_resolution_limit`
- `minimal_phase_space_volume_pos`
- `no_bare_singularities`
- `total_energy_minus_gauge`
- `gravity_gauge_scalar_accounting`
- `diracAdjoint2_involutive`
- `bogoliubov2_preserves_krein`
- `trifactor_partition_of_unity`
- `pgGlide_sq`
- `hamiltonian_preserves_plus_eigenspace`
- `hamiltonian_preserves_minus_eigenspace`
- `Pcanonical_is_tripotent`
- `qCrossMap_tmul`

## Theorem-Honesty Policy

This release distinguishes:

- Lean-proved finite algebraic/scalar/matrix anchors;
- SymPy witnesses;
- explicit sockets for analytic C*-algebraic, von Neumann, infinite spectral, and physical interpretation layers.

## Suggested GitHub Release Text

```text
Initial open-source release of the InfoGeometry proof architecture.

Master build:
  cd proofs && lake build InfoGeometry

Result:
  Build completed successfully (8043 jobs).

This release includes Apache-2.0 licensing, CITATION.cff, Zenodo metadata,
AI collaboration disclosure, the InfoGeometry master Lean manifest, SymPy
witnesses, and the theorem-honest architecture manifest.
```
