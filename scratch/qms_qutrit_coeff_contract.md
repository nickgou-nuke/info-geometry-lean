# QMS theorem contract: canonical injectivity of ternary coefficient flattening

## Result established

At the canonical root of unity `InfoGeometry.Topology.Parafermion.omega`, the
owner proves that equal flattened matrices have equal nine coefficient
arrays:

```lean
flatten omega A = flatten omega B → A = B
```

This establishes uniqueness for the existing finite coefficient expansion. It
does not claim a new abstract algebra isomorphism or a relation to W24.

## Source-grounded owners and conventions

- `Synthesis/TernaryShirokovCoefficientFlattening.lean` defines the coefficient
  carrier and maps its slots to `ternaryMultivector` in the order
  `(00,10,01,20,02,11,21,12,22)`, i.e. terms `P^j R^k`.
- `Synthesis/ShirokovTernaryCliffordUnitarySU3Synthesis.lean` defines the
  Shirokov shift `P = ternaryShiftP` and clock `R = ternaryClockR`.
- `Canonical/QutritWeylOperatorBasis.lean` proves linear independence,
  spanning, basis expansion, and uniqueness for `weylWord a b =
  colorShift^a * colorClock omega^b` on the same `Matrix (Fin 3) (Fin 3) ℂ`
  carrier.
- `Canonical/TwoSheetThreeColorWeyl.lean` defines the reverse-cycle
  `colorShift`; the finite matrix identity needed is
  `ternaryShiftP = colorShift ^ 2`. The clock definitions agree.
- The canonical `omega` is the `Topology.Parafermion.omega` and satisfies
  `omega^3 = 1`, `omega ≠ 1`, hence `omega^2 + omega + 1 = 0`.

## Proof route used

Show the shift identity, define/reason about the Fin 3 permutation `j ↦ j+j`,
rewrite the Shirokov nine-term expansion as a reindexing of `weylWord`, and use
the existing `weylWord_linearIndependent` (or `weyl_expansion_unique`) to
recover every coefficient. Keep all maps explicit and preserve the opposite
shift convention through the reindexing.

## Exclusions

- No arbitrary-root parameterized basis theorem is claimed.
- No abstract multiplication law or Shirokov adjugate theorem is proved here.
- No map or theorem connecting the adjugate to the 24-channel `W24` carrier is
  asserted.
- The already-proved trace identity is reused, not strengthened.

## Acceptance evidence

The primary locked build of the owner, audit, and `InfoGeometry.Synthesis.All`
completed successfully (10018 jobs). Independent QA-A separately rebuilt the
audit (9645 jobs) and synthesis umbrella (10018 jobs), with no active compiler
before either build. Both strict screens reported zero violations and no
quarantined packets. The audit prints only
`[propext, Classical.choice, Quot.sound]` for the three audited theorems. The
independent A-A and QA-A reviews passed. Gate 4 was not run, so this records
QMS source/kernel acceptance evidence, not a Gate 4 or release certification.
