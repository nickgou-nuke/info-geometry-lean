import Mathlib

/-!
# Companion Patch for lib/InfoGeometryCore/InfoGeometryCore/Basic.lean

This companion file documents the exact definitions to be added to
`namespace InfoGeometryCore` in `lib/InfoGeometryCore/InfoGeometryCore/Basic.lean`.

Location in Basic.lean: lines 23-24, immediately following:
```lean
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
```

And immediately preceding:
```lean
/-- First complex Pauli matrix. -/
def sigma1C : M2C := !![0, 1; 1, 0]
```

## Patch Content:
```lean
/-- First real Pauli matrix. -/
def sigma1R : M2R := !![0, 1; 1, 0]

/-- Third real Pauli matrix. -/
def sigma3R : M2R := !![1, 0; 0, -1]
```

This definition establishes `sigma1R` and `sigma3R` at the root of `InfoGeometryCore`,
resolving dependencies across `BottPeriodicityReconciliation.lean`,
`Cl11SplitQuaternionMobiusBridge.lean`, and `FibonacciCliffordBridge.lean`.
-/

namespace InfoGeometryCore

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- First real Pauli matrix. -/
def sigma1R : M2R := !![0, 1; 1, 0]

/-- Third real Pauli matrix. -/
def sigma3R : M2R := !![1, 0; 0, -1]

end InfoGeometryCore
