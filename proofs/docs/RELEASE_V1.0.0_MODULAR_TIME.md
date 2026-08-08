# Release Notes: v1.0.0-modular-time

Title: **Modular Parabolic Time — de Rham / Radon--Nikodym / TKK Grade Preservation Milestone**

## Summary

This release adds the final finite algebraic verification layer for the modular-time
emergence claim at the level of theorem-honest Lean formalization.

The central novelty is that the forbidden-cone de Rham generator is identified,
in the formal system, with the Tomita--Takesaki modular derivation sector and
its parabolic clock flow, while preserving all required 5-graded TKK compatibility
constraints.

## Verified Scope (Lean kernel)

`lake build ModularParabolicTimeBridge` and related bridge targets now succeed.

Key declarations proved in this release:

- `ModularTimeDeRhamBridge.ParabolicShearClock`
- `ModularTimeDeRhamBridge.ParabolicShearClock.comp`
- `ModularTimeDeRhamBridge.ParabolicShearClock.inv`
- `ModularTimeDeRhamBridge.dlog_modular_derivation_preserves_grades`
- `ModularTimeDeRhamBridge.modular_time_clocks_deRham_forbidden_cone`
- `ModularRadonNikodymJacobianBridge.forbidden_cone_dlog_modular_parabolic_clock_synthesis`
- `ModularRadonNikodymJacobianBridge.forbidden_cone_modular_derivation_clocks_parabolic_time`
- `ModularRadonNikodymJacobianBridge.modular_derivation_preserves_grade`
- `ModularRadonNikodymJacobianBridge.modular_rn_jacobian_chemical_derham_tkk_synthesis`
- `ModularRadonNikodymJacobianBridge.de_rham_alpha_beta_forbidden_cone_clock_synthesis`
- `ModularParabolicTimeBridge.deRham_is_modular_parabolic_time_derivation`
- `ChemicalPotentialDeRhamG0Bridge.chemical_potential_derham_g0_synthesis`

## Symbolic/SymPy verification layer

The following scripts were added/updated in this release and run as consistency
witnesses:

- `proofs/modular_time_derivation_witness.py`
- `proofs/modular_parabolic_time_witness.py`
- `proofs/modular_radon_nikodym_jacobian_bridge.py`

Notable identities checked numerically/symbolically:

- `\iota_X (d \log Q) = 2`
- `d(\iota_X (d \log Q)) = 0`
- parabolic shear unipotent law `P(t) ∘ P(s) = P(t+s)`
- infinitesimal derivation form `\delta(A) = [K,A]`
- logarithmic Weyl shift identity
  `frameWeylLogClock(\theta + \mathit{affineLogQ}(a)) = frameWeylLogClock(\theta) + affineLogQ(a)`

## Graph / dependency hygiene

`proofs/tools/ExtractGraph.lean` now imports and tracks the new bridge modules:

- `ModularRadonNikodymJacobianBridge`
- `ModularTimeDeRhamBridge`
- `ModularParabolicTimeBridge`

A graph-based extraction pass was run and confirms:

- directed module dependency flow without cyclic module-level module-closure feedback in
the modular-time chain,
- no additional axiom declarations in the extracted theorem core for the modular-time
chain.

## Citation/Release Policy

This release keeps all deep analytic statements (full Tomita--Takesaki realizability,
RN measure-class transport, explicit spectral assumptions, etc.) explicit as
`sockets`, while the finite algebraic and cohomological spine remains theorem-honest.

Suggested command set:

```bash
cd proofs
lake build ModularParabolicTimeBridge
lake env lean tools/ExtractGraph.lean
python3 modular_time_derivation_witness.py
python3 modular_parabolic_time_witness.py
```

## Tag

`v1.0.0-modular-time`
