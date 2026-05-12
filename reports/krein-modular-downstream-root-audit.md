# Krein.Modular downstream root audit

Status: no-delete/no-demotion audit slice after root-first `InfoGeometry.Krein.Modular` cleanup.

## Scope

- Source module: `lean/InfoGeometry/Krein/Modular.lean`
- Direct importers found by source scan:
  - `lean/InfoGeometry/Krein/All.lean`
  - `lean/InfoGeometry/Canonical/Krein.lean`
  - `lean/InfoGeometry/Experimental/ModularSpinorBridge.lean`

## Verification already run

- `lake env lean lean/InfoGeometry/Krein/Modular.lean` passed.
- `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Krein.Modular InfoGeometry.Krein.All` passed.
- Stripped cheat scan on `Krein/Modular.lean` found no live `axiom`, `opaque`, `sorry`, or `admit`.
- Targeted `#print axioms` for new readbacks and forgetful maps reported only standard Lean/mathlib foundation axioms:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`

## Conductive profile

`InfoGeometry.Krein.Modular` has a conductive import/build/axiom profile for this slice. The remaining issue is not kernel hygiene; it is promotion policy: do not let downstream theorem surfaces be promoted when their final root is merely an arbitrary record field rather than a certified constructor/owner theorem.

## Downstream usage findings

No source usages outside `Krein/Modular.lean` were found for these symbols, excluding generated `auto_blueprints.lean`:

- `FiniteDimensionalExponentialFlow`
- `KreinPolarData`
- `KreinPolarFactorization`
- `finiteDimensional_krein_polar`
- `kreinAbs`
- `ModularFlowData`
- `ModularGeneratorData`
- `ModularFlowTransport`
- `ModularFlowBridge`
- `toFlowStack`

Therefore, the immediate downstream risk from the edited `Krein.Modular` API is currently import-surface exposure rather than active theorem dependency.

## Promoted arbitrary-field roots in direct importer

`lean/InfoGeometry/Experimental/ModularSpinorBridge.lean` imports `InfoGeometry.Krein.Modular` but does not appear to use the modular symbols above. It contains two promoted theorem surfaces rooted directly in arbitrary structure fields:

1. `spinorBilinear_eq_berryPhase`
   - Root structure: `ModularBerryBridge`
   - Proof body: rewrites by `B.h_K`, then `exact B.berry_identity ψ`
   - Promotion concern: `berry_identity` is an arbitrary field of the input bridge record.
   - Needed certified root/constructor before promotion: a constructor deriving `h_K` and `berry_identity` from the concrete `canonicalMajoranaFrame`, `spinorBilinear`, and the imported Berry/Souriau/Kähler owner data.

2. `spinorBilinear_eq_klDivergence`
   - Root structure: `SpinorInnovationBridge`
   - Proof body: `exact B.h_bilinear`
   - Promotion concern: `h_bilinear` is an arbitrary field of the input bridge record.
   - Needed certified root/constructor before promotion: a constructor deriving the KL equality from `LogRadonNikodymData`/operatorial log-density owner lemmas and a specified innovation operator, not from a free field.

No deletion was performed. These are audit targets for constructor search/proof search.

## Search notes before any deletion/demotion

Local mathlib search found relevant root ingredients but no direct Krein polar decomposition theorem:

- `Mathlib.Algebra.Star.SelfAdjoint`: `IsSelfAdjoint`, `star_mul_self`, `mul_star_self`, conjugation/power/inverse closure lemmas.
- `Mathlib.Algebra.Star.Unitary`: `unitary`, `Unitary.star_mul_self`, `Unitary.mul_star_self`, `mem_iff_star_mul_self`.
- `Mathlib.Algebra.Star.LinearMap` and `ContinuousLinearMap`/adjoint infrastructure are relevant for converting local `LinearMap.IsSymmetric` and star/unitary operator facts.

Local Isabelle/AFP search under `external/afp/thys` found no direct Krein/polar decomposition match in the quick scan; it mostly matched generic Hilbert-space material and `Complex_Bounded_Operators` as a possible donor area for operator facts.

arXiv quick search produced likely literature leads for polar decomposition in adjacent operator settings:

- `The polar decomposition for adjointable operators on Hilbert C^*-modules and centered operators`, arXiv:1807.01598
- `The polar decomposition for adjointable operators on Hilbert C^*-modules and n-centered operators`, arXiv:1806.06141
- `Generalized inverses and polar decomposition of unbounded regular operators on Hilbert C^*-modules`, arXiv:0806.0162
- `Regular Operators on Hilbert C^*-modules`, arXiv:math/9906169

These are retrieval/search leads only, not Lean authority.

## Next safe action

Keep `InfoGeometry.Krein.Modular` as conductive infrastructure for now. Next cleanup should target `Experimental/ModularSpinorBridge.lean` as a promotion audit, not a deletion pass:

1. Read owner definitions for:
   - `ModularRadonNikodymData`
   - `LogRadonNikodymData`
   - `SuperHestenesKaehlerDatum`
2. Search for existing constructors/theorems proving the two exact field laws.
3. If derivable, add certified constructors/readbacks.
4. If not yet derivable, leave theorem surfaces unpromoted and record exact missing lemmas.
