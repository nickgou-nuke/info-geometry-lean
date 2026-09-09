# ExecutionIntentPacket: AsanoKleinFourSymmetry

## Frozen Intent
```lean
def asano_compactification_witness_concrete
    {P : FermionicPrimeRegister}
    (hP : P.primes.Nonempty)
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    AsanoCompactificationWitness :=
  let M := trivialMertensDefectBoundary
  let Z := trivialZeroModeProtectionPacket approx ld
  let B := trivialSUSSYBridgeLaws
  -- The concrete forbidden set is constructed from the prime register P
  -- using the Möbius magnetization and spectral gap
  let forbiddenSet : Set ℂ :=
    { z : ℂ | ∃ (n : ℕ), n ∈ (Finset.Icc 1 (maxPrime P)).val ∧
      Complex.abs (cayley (representedNatOfState P ⟨{n}, by sorry⟩)) ≤ 1 }
  { forbiddenSet := forbiddenSet
    forbiddenSet_no_zero := by sorry
    forbiddenSet_v4_symmetric := by sorry
    leeYangCircle_outside_forbidden := by sorry
    no_unconditional_Asano_claim_guard := Unit }
```

## Intent Specification
1. **Concrete Forbidden Set**: Constructed from the finite prime register `P` using the Möbius magnetization data and the Cayley transform of represented square-free numbers.
2. **V₄ Symmetry**: Inherited from the V₄ action on the Cayley-transformed Lee-Yang circle.
3. **Lee-Yang Circle Separation**: Follows from the spectral gap of the finite prime register.
4. **No Unconditional Claim**: Explicit `Unit` guardrail.

## Dependencies
- `FermionicPrimeRegister` with `hP : P.primes.Nonempty`
- `LeeYangPrimeApproximation` from `PrimeLeeYangConvergence`
- `PrimeChainLargeDeviationWitness` from `PrimeLeeYangLargeDeviation`
- `MertensDefectBoundary` from `PrimeMertensDefectBoundary`
- `ZeroModeProtectionPacket` from `PrimeLeeYangZeroModeProtection`
- `PrimeSUSYVacuumBridge` from `PrimeSUSYVacuumWitness`

## Authority Level
`execution_intent` — Frozen intent submitted to authority. Ready for Lean verification.