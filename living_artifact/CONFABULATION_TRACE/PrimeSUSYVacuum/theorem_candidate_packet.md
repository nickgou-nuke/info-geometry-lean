# TheoremCandidatePacket: PrimeSUSYVacuum

## Formal Target
**Namespace:** `InfoGeometry.Canonical.PrimeSUSYVacuum`
**Packet:** `PrimeSUSYVacuumPacket` (theorem-honest data-only)
**Authority Level:** `lean_checked` (proved theorems), `execution_intent` (socket for bridge laws)

## Candidate Structure
```lean
structure PrimeSUSYVacuumPacket
    (CompletedXiReadout VacuumReadout : Type) where
  mertensBoundary : MertensDefectBoundary
  zeroModeProtection : ZeroModeProtectionPacket CompletedXiReadout
  vacuumReadout : VacuumReadout
```

## Genuine Theorems (Proved)
1. `finite_mobius_eq_fermionParity` — Möbius = fermion parity on square-free states
2. `finite_wittenIndex_cancel` — Finite Boolean Witten-index cancellation
3. `finite_divisorMobius_cancel` — Finite divisor Möbius cancellation

## Assembly Function (Pure Data)
```lean
def primeSUSYVacuum_of_zeroModeProtection
    {CompletedXiReadout VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket CompletedXiReadout)
    (R : VacuumReadout) :
    PrimeSUSYVacuumPacket CompletedXiReadout VacuumReadout
```

## Bridge Claim (Socket Debt)
The 8 SUSY bridge laws (Witten index, boson/fermion cancellation, zero vacuum energy, unbroken SUSY, SUSY↔Mertens, SUSY zeros=ξ zeros, RH guardrail, Witten≠ξ determinant) remain as explicit `Type` fields in `PrimeSUSYVacuumBridge` — explicit socket debt, not proved.

## Novelty Defense
1. **Theorem-honest redesign** — Removed 8 arbitrary law fields from packet
2. **Pure data assembly** — Only genuine finite theorems + data packaging
3. **Explicit socket debt** — 8 bridge laws remain as explicit `Type` fields

## Authority Level
`lean_checked` (theorems), `execution_intent` (socket for bridge laws)