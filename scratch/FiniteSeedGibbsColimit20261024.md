# Finite-seed Gibbs colimit candidate

Status: authored sandbox proposal, uncompiled; independent AA and serial QA pending.
Only the accompanying new scratch Lean file is proposed for integration.

## Existing owners and exact scope

- `Canonical.AlgebraicKMSStateColimit`: `normalizedDeltaWeightedFunctional`,
  `stageUnitToColimit`, and `normalizedDeltaWeightedFunctional_kms` already
  define the actual global linear functional and its algebraic KMS boundary law.
- `Canonical.AlgebraicKMSStateColimitReadback`:
  `normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional` already gives
  readback at any chosen seed stage. It is reused, not reproved.
- `Canonical.CuntzMatrixAlgebraicStarColimit`: existing `Carrier`, `rawMap`,
  `stageInjection`, `stageInjection_transition`, and star/multiplication laws.
- `Canonical.GibbsParityTower` (intended native import, parent promotes first):
  James owns `CuntzMatrixCompatibleStateNet.gibbsDensity_rawMap`, the CFC
  transport helper for any k ≤ n. This candidate reuses it by qualified name.
- `Canonical.FiniteMatrixGibbsFunctional`: native Gibbs density unit, positivity,
  and normalization. `Canonical.FiniteMatrixGibbsParity.gibbsFunctional_odd_zero`
  supplies finite odd cancellation; Gamma need not be self-adjoint.

## Delta

Five separate lemmas: equality of transported colimit
density units, arbitrary later-stage observable readback, normalization,
global positivity, and seed odd cancellation. No definitions, carriers,
state structures, or conjunction packets are added.

The functional is exactly
`normalizedDeltaWeightedFunctional (stageUnitToColimit k (gibbsDensityUnit H hH β))`.
Its existing left-weight identity identifies it with normalized global trace
weighted by `stageInjection k (gibbsDensity H hH β)`.
The seed may be at k=1 (a genuine 2x2 Klein example), or any finite k.
No strict Hamiltonian compatibility from stage zero is assumed.

Later-stage readback assumes Hn equals `rawMap hkn H` and accepts arbitrary X
at stage n. Equality of density units reduces it to the existing readback.
For global positivity an arbitrary representative at stage j is moved with
the seed to max k j, then native finite Gibbs positivity applies there.

## Shared helper coordination for James (via parent)

Parent must promote James's accepted `scratch/GibbsParityTower20261024.lean`
to `InfoGeometry.Canonical.GibbsParityTower` before compiling this candidate.
The inspected helper signature matches the qualified use here. No duplicate
CFC helper remains, and there is no scratch-to-scratch import. No need for a
second cofinal carrier or a stage-zero Hamiltonian family.

## Acceptance boundary

No build, tests, axiom audit, or kernel success claimed. Parent must verify the
exact candidate serially after independent AA. In particular check CFC
elaboration, unit coercion rewriting, and common-stage direct-limit induction.
The result is positivity and normalization of a complex linear functional on
the existing algebraic colimit. It does not construct a completed Cstar state,
an analytic KMS strip, or compatibility for interacting successor Hamiltonians.
The existing algebraic KMS theorem needs no duplicate forwarding theorem.
