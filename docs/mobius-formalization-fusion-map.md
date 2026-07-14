# Möbius Formalization Fusion Map

This note reconstructs the Möbius-related owner chain that was previously
scattered across the topology, categorical, self-reference, and canonical
lanes.

## Owner Surface

- [lean/InfoGeometry/Topology/MobiusGeometry.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Topology/MobiusGeometry.lean)

This is the proof owner. It contains the actual Möbius transform model, circle
preservation results, fixed-point classification, normal forms, conjugacy, and
cross-ratio statements.

## Forwarding Lane

- [lean/InfoGeometry/Categorical/MobiusGeometry.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Categorical/MobiusGeometry.lean)

This file is only a thin import bridge into the owner surface.

## Adjacent Möbius-Lane Surfaces

- [lean/SelfReference/Moebius.lean](/home/goutev/repos/info-geometry-lean/lean/SelfReference/Moebius.lean)
- [lean/InfoGeometry/Canonical/MoebiusVirasoroBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/MoebiusVirasoroBridge.lean)
- [lean/InfoGeometry/Canonical/MobiusHyperbolicCompactification.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/MobiusHyperbolicCompactification.lean)
- [lean/InfoGeometry/Canonical/CayleyMobiusPowerLaws.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CayleyMobiusPowerLaws.lean)

These are not replacements for the owner file. They package downstream
interpretations, involution readouts, or compactified boundary behavior.

## Proof Chain Inside the Owner File

The core theorem chain in `Topology/MobiusGeometry.lean` is:

1. `MobiusTransform` and `MobiusTransform.eval`
2. `GenCircle` and generalized-circle containment
3. `trans_preserves_circle`, `dil_preserves_circle`, `inv_preserves_circle`
4. `circle_preserving`
5. `maps_to_01inf`, `mobius_unique_01inf`, `strictly_three_transitive`
6. `MobiusTransform.is_fixed_point`
7. `fixed_point_quadratic`, `fixed_point_linear`, `fixed_point_translation`
8. `three_fixed_points_implies_identity`
9. `is_conjugate`, `non_parabolic_matrix`, `nonParabolicNormalForm`
10. `non_parabolic_normal_form`
11. `parabolic_matrix`, `parabolicNormalForm`, `parabolic_normal_form`
12. `characteristic_parallelogram`, `multiplier_from_poles`
13. `eigenvalue_mapping`, `eigenvalue_roots`
14. `mobius_decomposition`, `mobius_algebraic_decomposition`
15. `cross_ratio_preserving`, `cocircular_iff_real_cross_ratio`
16. `mobius_action_correspondence`, `pgl_equivalence`
17. `circle_inversion_involution`, `mobius_scaling_equivalence`
18. `disk_to_half_plane_zero`, `elliptic_norm_invariant`
19. `hyperbolic_trace_bound`, `iter_trace_bound`
20. `hyperplane_reflection_involution`, `minkowski_det`

## Reconstruction Rule

When reconstructing lost Möbius material, start from the owner surface and
lift outward:

1. recover or repair theorems in `Topology/MobiusGeometry.lean`;
2. keep the categorical file as a forwarding import only;
3. use the canonical/self-reference files only as downstream packaging;
4. do not promote the packaging layers into new owners.
