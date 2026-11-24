# Arnold finite-group core: formalization map

## Scope

This packet records the finite algebraic analogue of Arnold's volume-preserving
group used in geometric hydrodynamics and in the Navier--Stokes context.

It does not claim the infinite-dimensional group `SDiff(M)` or the
Euler--Arnold Navier--Stokes equation. Those remain open debts.

## Evidence used

- Live ArangoDB `infogeometry.decls`: no `Arnold group` phrase and no native
  `ArnoldGroup` declaration.
- Existing Lean owners:
  - `Physics.ArnoldHydrodynamicsBeltrami` — Lamb vector, Beltrami alignment,
    helicity density, viscous decay, ABC flow.
  - `Physics.ArnoldNavierStokesVorticityDepletion` — energy/helicity
    dissipation, scale barrier, blow-up immunity.
  - `Physics.ArnoldCoadjointOrbitsChern` — KKS form, coadjoint action, Casimir
    stabilization, helicity self-pairing.
  - `Canonical.Stratum34TopologicalClosureBridge` — finite traceless matrix
    stages toward an `sdiff(M)` colimit narrative.
- Alexandria PDF retrieval: Proposition 6.2 in
  `1-s2.0-S0022247X06001028-main.pdf` states that 2D Navier--Stokes is a Leibniz
  flow associated with the area-preserving diffeomorphism group. This is
  `retrieval_context_only`.

## New owner

`lean/InfoGeometry/Physics/ArnoldFiniteGroupCore.lean`

Declarations:

- `ArnoldFiniteGroup n := Matrix.SpecialLinearGroup (Fin n) ℝ`
- `arnoldFiniteGroup_det_one`
- `IsTraceless n X := Matrix.trace X = 0`
- `isTraceless_add`
- `isTraceless_smul`
- `arnoldFinite_traceless_commutator`
- `arnoldFiniteGroup_adjoint_traceless`
- `arnoldFiniteLieModule`
- `arnoldFiniteLieModule_bracket_mem`
- `arnoldFiniteGroup_adjoint_mem`
- `arnoldFiniteGroup_tracePairing_invariant`
- `arnoldFiniteGroup_quadratic_trace_invariant`

These give the finite determinant-one volume-preserving group and the
trace-zero incompressible Lie-algebra closure.

## Verification

`lake build InfoGeometry.Physics.ArnoldFiniteGroupCore` — exit 0, zero errors,
`Build completed successfully (3092 jobs)`.

## Explicit open debts

1. A native carrier for `SDiff(M)` as volume-preserving diffeomorphisms.
2. Euler equation `du/dt + ∇_u u = -∇p` on that carrier.
3. Euler--Arnold form `dω/dt = -ad*_u ω`.
4. Navier--Stokes viscous term `νΔu` in the same Lie-group framework.
5. A theorem identifying helicity with the relevant coadjoint Casimir on the
   infinite-dimensional carrier.
6. A native bridge from the Alexandria Proposition 6.2 chunk to a Lean theorem.
