# Log-Det and Noncommutative Radon-Nikodym Mechanism

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This note records the repository interpretation of the blueprint:

`multiplicative noncommutative data -> abelianized scalar shadow -> additive log potential`.

## Canonical translation in this repository

1. Multiplicative-to-additive abstraction:
   - `lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean`
   - exact and defective descent surfaces
2. Connes cocycle log-potential lane:
   - `lean/InfoGeometry/Volume/ConnesCocycle.lean`
   - operator cocycle -> scalar cocycle -> `cocycleLogPotential`
3. Type-III continuous-core interface:
   - `lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean`
   - modular flow, modular generator, and additive entropy potential wrappers

## New owner package

The module

- `lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean`

adds a bundled interface:

- `TypeIIILogDetRNPackage`:
  - base Type-III modular data;
  - a Connes cocycle;
  - a scalar cocycle bridge.
- `TypeIIILogDetRNPackage.logPotential`:
  - the additive log potential extracted from cocycle data.
- `TypeIIILogDetRNPackage.logPotential_add`:
  - additive law for the potential.
- `TypeIIILogDetRNPackage.cocycle_chain_rule`:
  - twisted chain rule (noncommutative RN cocycle law).
- `TypeIIILogDetRNPackage.exists_additive_logPotential`:
  - existential additive-potential form.

This is intentionally a packaging layer: it does not replace owner files for
relative modular operators, support-log operators, or crossed-product
construction internals.
