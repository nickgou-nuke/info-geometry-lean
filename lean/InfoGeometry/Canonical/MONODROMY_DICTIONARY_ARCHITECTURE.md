# Cl(1,1) Monodromy Dictionary Architecture

## Overview

This document tracks the files implementing the theorem-honest construction:

**Time = Modular Flow = de Rham Monodromy**

constructed from the Cl(1,1) tensor tower, bridging to the `ModularMonodromyClock` interface.

## Core Files

### 1. Canonical Owner Surface
**File:** `lean/InfoGeometry/Canonical/Cl11MonodromyDictionaryConstruction.lean`

**Main constructions:**
- `wittCreationStage1` - Stage 1 nilpotent generator (a†)
- `wittCreationStage1_sq` - proves (a†)² = 0
- `modularHamiltonian` - K = ι₁(a†) in the infinite carrier
- `modularHamiltonian_sq` - proves K² = 0 via limit_square_zero
- `carrierResidue` - Res(X) = [K, X] (de Rham monodromy operator)
- `carrierResidue_iterate_formula` - Res²(X) = -2(K X K)
- `carrierResidue_globally_parabolic_iff_middle_doubled_zero` - characterization

**Theorems proved:**
- Square-zero generator in finite stage
- Square-zero preservation in direct limit
- Derivation property of carrier residue
- Nilpotency condition (Res² = 0 iff K X K = 0)
- Finite advance compatibility

### 2. Clifford Tower Support
**File:** `lean/InfoGeometry/Clifford/Cl11TensorTower.lean`

**Key definitions:**
- `wittCreationBase = !![0, 1; 0, 0]` - 2×2 nilpotent matrix
- `wittCreationBase_sq` - proves (a†)² = 0 by direct computation
- `wittAnnihilationBase = !![0, 0; 1; 0]`
- Jordan-Wigner embedding infrastructure

### 3. Direct Limit Carrier
**File:** `lean/InfoGeometry/Clifford/Cl11InfiniteCarrier.lean`

**Infrastructure:**
- `CompatibleCarrier` - direct limit type
- `intoCarrier` - canonical cone embeddings
- `limit_square_zero` - preserves nilpotency
- `finiteAdvance` - tensor tower iteration

## Axiomatic Interface

**File:** `lean/InfoGeometry/Canonical/ModularMonodromyClock.lean`

**Defines:**
- `Derivation` - R-linear Leibniz maps
- `modularDerivation K` - inner derivation [K, X]
- `DeRhamResidue` - square-zero residue operators
- `MonodromyModularDictionary` - the bridge structure
- `parabolicTimeClock` - main theorem

**Note:** The actual construction lives in `Cl11MonodromyDictionaryConstruction.lean`, 
which provides the concrete Witt-based realization. The `ModularMonodromyClock` file 
provides the axiomatic interface.

## Mathematical Structure

### Construction Flow

```
Cl(1,1) tensor tower (Cl11TensorTower)
  ↓
Witt creation a† with (a†)² = 0
  ↓
Embed into direct limit: K = ι₁(a†)
  ↓  
Prove K² = 0 (modularHamiltonian_sq)
  ↓
Define Res(X) = [K, X] (carrierResidue)
  ↓
Prove Res is a derivation
  ↓
Characterize Res² = -2(K X K)
  ↓
Condition for parabolicity: K X K = 0
```

### Physical Interpretation

- **K** = modular Hamiltonian (nilpotent generator)
- **Res** = de Rham residue (monodromy around null cone)
- **[K, X]** = modular flow (time evolution)
- **Res² = 0 condition** = parabolic clock (unipotent shear)

The construction shows that **time evolution** (modular flow) and **topological winding** 
(de Rham monodromy) are both manifestations of the same nilpotent generator from the 
Cl(1,1) tower.

## Related Files

### Thermal Time Bridge
- `lean/InfoGeometry/Canonical/ThermalTimeMonodromyBridge.lean`

### Capstone Documents
- `lean/InfoGeometry/Capstone/GrandIdentityDeRhamModular.lean`
- `lean/InfoGeometry/Capstone/CompleteWorldlineAttentionFluid.lean`

### Parabolic Clock
- `lean/InfoGeometry/OperatorAlgebra/ParabolicClockInClifford.lean`
- `lean/InfoGeometry/Physics/ParabolicClock.lean`

### Monodromy Structures
- `lean/InfoGeometry/Canonical/BernsteinSatoMonodromy.lean`
- `lean/InfoGeometry/Topology/Q8MonodromySpinorCover.lean`
- `lean/InfoGeometry/BostConnes/BostConnesModularFlow.lean`

## Verification Status

✅ **Witt creation square-zero** - proved in Cl11TensorTower
✅ **Direct limit preservation** - proved via limit_square_zero
✅ **Derivation property** - carrier_ringCommutator_isDerivation
✅ **Nilpotency formula** - carrierResidue_iterate_formula
✅ **Parabolicity condition** - explicitly characterized

## Outstanding Considerations

The residue operator squares to zero **only when** the "middle term" vanishes:
```
  Res²(X) = -2 (K X K)
```

This is **not automatically zero** for all X in the noncommutative carrier. 
The file provides the exact characterization:
```lean
  carrierResidue_globally_parabolic_iff_middle_doubled_zero
```

This is mathematically correct and expected - the parabolic clock property holds 
on the subalgebra annihilated by K on both sides.

---

**Commit History:**
- File created and committed prior to current session
- Architecture audited and documented: 2026-06-28
