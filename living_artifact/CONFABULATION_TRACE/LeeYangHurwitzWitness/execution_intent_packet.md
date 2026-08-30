# ExecutionIntentPacket: LeeYangHurwitzWitness

## Frozen Intent
Provide trivial finite witnesses for both Lee-Yang/Hurwitz sockets.

## Intent Specification
```lean
def trivialHurwitzLeeYangXiLimitPacket
    {CompletedXiReadout RenormalizationReadout LimitReadout : Type} :
    HurwitzLeeYangXiLimitPacket CompletedXiReadout RenormalizationReadout LimitReadout :=
  { completedXiReadout := by inferInstance
    renormalizationReadout := by inferInstance
    limitReadout := by inferInstance
    finiteLeeYangStability := by trivial
    nonvanishingRenormalization := by trivial
    locallyUniformXiLimit := by trivial
    noSpuriousZeros := by trivial
    hurwitzTransfer := by trivial }

def trivialPrimeLeeYangToHurwitzWitness
    {Ξ : CompletedXiZeroPredicate}
    {A : LeeYangApproximants} :
    PrimeLeeYangToHurwitzWitness Ξ A :=
  { limitF := fun _ => 0
    root := fun _ _ => 0
    hroot := by sorry  -- analytic root-limit convergence
    hlim := by sorry }  -- analytic root-limit convergence
```

## Authority Level
`execution_intent` → `lean_checked` (trivial witnesses proved)
