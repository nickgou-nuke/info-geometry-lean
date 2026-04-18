# Operator Theorem Translation Registry

This registry enforces the repo rule:

1. do not import external theorem language as authority;
2. translate source theorem surfaces into doubled-real, symmetry-graded operator language;
3. keep one-to-one anchor mapping to concrete Lean declarations.

The source narrative for this shift is recorded in:
- [black_books/131_the_transmutation_of_the_complex_mask.md](black_books/131_the_transmutation_of_the_complex_mask.md)

## Translation Invariants

- space/time/coordinate-free operator surfaces only
- doubled real Krein carrier (`Cl(1,1)`/graded operator lane)
- linear/antilinear and symmetric/antisymmetric sectors explicit
- functorial, equivariant mapping required for promoted theorem surfaces
- no closure by naming; closure by theorem anchor

## Translation Anchors

| ID | Source Surface (External Notation) | Repo-Native Operator Surface | Lean Anchor | Status |
|---|---|---|---|---|
| TR-001 | `H_D = A_mod(seed)` (modular generator identity) | projected even generator equals modular transport generator of a Lorentz-bivector seed on doubled real Krein carrier | `InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed` | implemented |
| TR-002 | KMS equilibrium under modular flow | graded-state invariance under Lorentz-bivector generated transport on doubled carrier | `InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural` | implemented |
| TR-003 | cocycle split `u_t u_s = u_{t+s}` translation lane | modular generator split with Drazin-lane central defect in operator basis | `InfoGeometry.Canonical.ModularSuperchargeClosure.exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality` | implemented |
| TR-004 | Lorentz-group orbit action with parameter `τ` | projected even generator is fixed along Lorentz-chiral modular orbit on doubled real operator lane | `InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit` | implemented |
| TR-005 | wedge-to-modular parameter transliteration | wedge parameter `τ_wedge` maps to modular time and preserves the projected even generator on the Lorentz-chiral orbit | `InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzWedgeOrbit` | implemented |
| TR-007 | external complex unit `i` | internal Lorentz-bivector axis `J ∘ ε` on the doubled-real carrier | `InfoGeometry.Canonical.ComplexMaskTransmutationBridge.lorentzBivectorGenerator_eq_modular_j_comp_spectral_epsilon` | implemented |
| TR-008 | modular seed written with complex-mask naming | canonical seed restated as `-(H_D ∘ (J ∘ ε))` in transmuted language | `InfoGeometry.Canonical.ComplexMaskTransmutationBridge.canonicalModularSeed_eq_neg_superHamiltonian_comp_lorentzBivectorGenerator` | implemented |
| TR-009 | circular polarization transport (`u⁺ ↔ u⁻`) under modular phase axis | Lorentz-bivector sheet exchange on doubled-real carrier | `InfoGeometry.Canonical.ComplexMaskTransmutationBridge.lorentzBivectorGenerator_maps_plusSheet_to_minusSheet` | implemented |
| TR-010 | circularly polarized channel basis | `uPlus/uMinus` defined as exact aliases of the `g₁/g₋₁` off-diagonal channels | `InfoGeometry.Canonical.KKTCore.uPlus_eq_gOnePart` | implemented |
| TR-011 | nilpotent constraints on polarized channels | `uPlus² = 0` and `uMinus² = 0` on channel multiplication | `InfoGeometry.Canonical.KKTCore.uPlus_mul_uPlus_eq_zero` | implemented |
| TR-012 | polarized commutator closure | `[uPlus, uMinus]` closes in the grade-zero channel `g₀` | `InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero` | implemented |
| TR-013 | Cartan boost orbit on the `u⁺` channel | `ε`-generated hyperbolic boost gives `uPlus` weight `(cosh τ + sinh τ)` | `InfoGeometry.Canonical.KKTLorentzOrbitBridge.channelBoost_mul_uPlus` | implemented |
| TR-014 | Cartan boost orbit on the `u⁻` channel | `ε`-generated hyperbolic boost gives `uMinus` weight `(cosh τ - sinh τ)` | `InfoGeometry.Canonical.KKTLorentzOrbitBridge.channelBoost_mul_uMinus` | implemented |
| TR-015 | Cartan boost action on the grade-zero channel | `ε`-generated hyperbolic boost commutes with `g₀` channel operators | `InfoGeometry.Canonical.KKTLorentzOrbitBridge.channelBoost_mul_gZeroPart_eq_gZeroPart_mul_channelBoost` | implemented |

## Promotion Rule

A translation is promoted only if all hold:

1. anchor exists as a Lean declaration;
2. anchor is listed in this registry;
3. strict gate includes this registry check and Pauli I-XI check.
