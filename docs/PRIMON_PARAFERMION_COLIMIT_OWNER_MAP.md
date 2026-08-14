# Primon–Parafermion Colimit Owner Map

*Generated per Phase 0, Task 0.1 of the Primon-Parafermion Colimit Framework Plan.*

This document enumerates the authoritative locations and duplicate definitions for the core thermodynamic and parafermion variables across the repository.

## Parafermion Factors & Q Polynomials

### 1. `finiteParafermionLocalFactor`
- **Owner**: `lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean` (Line 50)
- **Signature**: `def finiteParafermionLocalFactor`
- **Classification**: Designated finite complex owner as per Phase 0 policy.

### 2. `localParafermionFactor`
- **Duplicate Location**: `lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean` (Line 9)
- **Signature**: `def localParafermionFactor (κ : ℕ) (x : ℝ) : ℝ`
- **Classification**: Exact/Real Duplicate. Should be deprecated in favor of the `Arithmetic` owner.

### 3. `Q_kappa`
- **Duplicate Location 1**: `lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean` (Line 101)
- **Duplicate Location 2**: `lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean` (Line 24)
- **Signature**: `def Q_kappa (κ : ℕ) (x : ℝ) : ℝ`
- **Classification**: Real specializations of the canonical complex geometric recurrence. The `Arithmetic` owner must subsume these.

---

## Thermodynamic Potentials

### 4. `grandPotential`
- **Locations**:
  - `lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauBregman.lean` (Line 144)
  - `lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauWeights.lean` (Line 129)
  - `lean/InfoGeometry/Arithmetic/ZetaSouriauComplexLift.lean` (Line 444)
  - `lean/InfoGeometry/Arithmetic/ZetaSouriauThermodynamics.lean` (Line 256)
  - `lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean` (Line 251)
  - `lean/InfoGeometry/Arithmetic/PrimeLatticeGasVariational.lean` (Line 86)
- **Signatures**: Varies from `def grandPotential (β Z : ℂ) : ℂ` to `def grandPotential (β : ℝ) (M : ℕ) (Z : Fugacity) : ℝ`
- **Classification**: Genuinely distinct structures representing the same thermodynamic potential in different categorical lanes (Lattice Gas vs Complex Souriau Lift).

### 5. `freeEnergy`
- **Locations**:
  - `lean/InfoGeometry/Arithmetic/PrimonFreeEnergyRelativeTrace.lean` (Line 29)
  - `lean/InfoGeometry/Canonical/OperatorThermodynamics.lean` (Lines 75, 157, 290)
  - `lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean` (Line 263, 436)
  - `lean/InfoGeometry/Potential/Thermo.lean` (Line 55)
  - `lean/InfoGeometry/Thermo/Gibbs.lean` (Line 35)
  - `lean/InfoGeometry/ModularVolumePotential.lean`
- **Signatures**: Heavily overloaded, ranging from real Legendre models `def freeEnergy (M : LegendreModel) (ε θ : ℝ) : ℝ` to operator packets `def freeEnergy (P : OperatorThermodynamicsPacket Op) : ℝ`.
- **Classification**: Genuinely distinct specializations spanning microcanonical Legendre physics to quantum operator thermodynamics. The authoritative finite baseline owner should ideally route through `Potential/Thermo.lean` as per Phase 0 policy.

### 6. `boltzmannEntropy`
- **Locations**:
  - `lean/InfoGeometry/Algebraic/CartanExponentialFamily.lean` (Line 71)
  - `lean/InfoGeometry/Canonical/FiniteBoltzmannMacroentropy.lean` (Line 31)
  - `lean/InfoGeometry/Canonical/MicrocanonicalBoltzmann.lean` (Line 10)
  - `lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean` (Line 255)
  - `lean/InfoGeometry/Physics/SouriauEntropyFoliation.lean` (Line 31)
  - `lean/InfoGeometry/Thermodynamics/FiniteEntropyLeaves.lean` (Line 90)
- **Signatures**: Ranging from `def boltzmannEntropy (kB W : ℝ) : ℝ` to functional definitions over vectors.
- **Classification**: Real specializations of $S = k_B \ln \Omega$.

### 7. `Massieu`
- **Locations**: Referenced heavily in `agent_memory_recovery/InformationSuperGas.lean` as a logarithmic Weyl-character readout, but no explicit bare `def Massieu` declaration found via regex (it is usually integrated directly into `freeEnergy` or `grandPotential` using the $\Psi$ symbol).

---

## Action Items (Phase 0 -> Phase 1)
1. Delete/archive duplicate parafermion owners (`lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean` and `lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean`) and force consumers to use `lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean`.
2. Institute the finite prime thermodynamic stage in `Arithmetic/PrimeThermodynamicStage.lean`.
3. Stop using `Tendsto` and infinite sums for these potentials. Establish them strictly as categorical limits.
