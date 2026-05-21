# Clifford Current Hierarchy Boundary

Lean module:

`InfoGeometry.Canonical.CliffordCurrentHierarchyBoundary`

## Formalized Chain

The current formalization separates two proved layers.

The finite substrate is the doubled real `Cl(1,1)` atom:

```text
J² = 1
ε² = 1
Jε = -εJ
(Jε)² = -1
u₊² = 0
u₋² = 0
u₊u₋ = P₊
u₋u₊ = P₋
[u₊, u₋] = ε
```

This is formalized in `TomitaKreinNilpotentAtom`.

The current/conformal layer is mode-indexed and lives in the external Virasoro
corridor:

```text
[J_m, J_n] = m δ_{m+n,0} K
Affine Kac-Moody = central extension of loop algebra by the residue cocycle
[L_m, L_n] = (m-n)L_{m+n} + ((m³-m)/12) δ_{m+n,0} C
C acts as 1 in the charged Fock Sugawara representation
```

This is formalized by direct imports of:

- `HeisenbergAlgebra.lie_jgen`
- `AffineKacMoody`
- `affineKacMoodyCocycle`
- `VirasoroAlgebra.lgen_bracket`
- `AbelianLieAlgebraOn.heisenbergCocycle_nontriviality`
- `WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero`
- `ChargedFockSpace.sugawaraRepresentation_cgen_apply`

## Boundary

The Lean module does not claim that the finite split-Clifford atom has already
been mapped into the Heisenberg currents.  That morphism would require a
mode-indexed construction, normal ordering, and a proof that the central
cocycle is the one induced by the finite substrate after the relevant
completion.

The theorem `finite_atom_and_external_mode_laws` is therefore a boundary
theorem: it packages the proved finite atom and the proved external mode laws
in one place, without asserting an unproved derivation between them.

## Exact Status

Proved:

- finite nilpotent/idempotent split-Clifford atom
- Heisenberg mode bracket in the external Virasoro library
- affine Kac-Moody as the external loop-algebra central-extension owner
- Virasoro mode bracket in the external Virasoro library
- nontrivial Heisenberg and Virasoro cocycle surfaces
- Sugawara central element acts as identity on charged Fock space

Not proved here:

- a tensor-tower theorem `Cl(1,1)^{⊗N} ≃ Cl(N,N)`
- an AF/UHF completion theorem for that tower
- a bosonization morphism from the finite split-Clifford completion to
  Heisenberg current modes
- a Sugawara derivation theorem from the split completion itself
