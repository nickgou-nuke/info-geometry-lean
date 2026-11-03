# Ground-truth contract: ring tail shift for the matrix `Cl(1,1)` tower

## Claim
For every finite offset `k`, the algebraic direct limit of the matrix stages
`MatStage (n + k)`, with transition maps induced by the existing
`Cl11TensorTower.stageEmbed`, is ring-isomorphic to the canonical
`Cl11TensorTowerLimit.Limit`. The maps are induced by the actual iterated stage
embeddings and are inverse on every canonical stage image.

## Carrier and maps
- Stage: `InfoGeometry.Clifford.Cl11TensorTower.MatStage n`.
- One-step bond: `Cl11TensorTowerLimit.stageBond n`, definitionally the ring map
  underlying `Cl11TensorTower.stageEmbed n`.
- Original limit: `Cl11TensorTowerLimit.Limit`, the
  `DirectLimitSuperClosure` of those bonds.
- Tail stage `n`: `MatStage (n + k)`; its transition from `m` to `n` is the
  iterated original bond from stage `m + k` to `n + k`.
- Tail limit: the algebraic ring direct limit of that shifted stage system.

## Existing owner facts
- `Cl11TensorTower.stageEmbed` is the canonical unital algebra embedding and
  preserves the tower's star operation (`stageEmbed_star`).
- `DirectLimitSuperClosureLemmas` supplies the iterated maps
  `bondMap`, `bondMap_apply_trans`, and the canonical ring colimit maps.
- `Cl11TensorTowerLimit.ofStage_apply_bond` identifies the existing limit's
  canonical stage maps across one transition.
- `Canonical/SplitCliffordDirectLimitRingShift.lean` proves the analogous
  result for the distinct recursive `Cl(n,n)` algebra tower. It does not prove
  the matrix-tower specialization because its stage carriers and bonds differ.

## Exact boundary
This is an algebraic ring equivalence between direct limits of the matrix
stages. It does not identify the limit with an analytic infinite tensor
product, a completion, or a graded tensor product of a finite Clifford algebra
with a limit. The finite-stage `Cl(1,1)` graded factorizations remain owned by
`Canonical/SplitCliffordTensorBridge.lean`.

## Verification
Compile the new owner through the repository's shared locked Lake build; check
for placeholders and inspect `#print axioms` for the ring equivalence.
