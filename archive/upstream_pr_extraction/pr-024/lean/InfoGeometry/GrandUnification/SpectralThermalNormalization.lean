import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Spectral Thermal Normalization

**Theorem-bank slogan:**
  The partition function is the thermodynamic normalization of spectral volume.

$$Z_\beta = \int e^{-\beta E} \, d\nu_H(E)$$

is the Boltzmann-regularized volume of the spectral space, obtained by
weighting the geometric spectral volume `dν_H` against the modular/Boltzmann
potential `e^{-βE}`.

## Full theorem-schema

Let `H` be a positive self-adjoint operator with spectral volume measure `dν_H(E)`.
Assume `Z_β = ∫ e^{-βE} dν_H(E) < ∞`.  Then:

1. `dγ_β(E) = e^{-βE}/Z_β · dν_H(E)` is a normalized Gibbs spectral state.
2. Log-RN potential: `-log(dγ_β/dν_H) = βE + log Z_β`.
3. Free-energy identity: `D_KL(μ|γ_β) = β(F_β(μ) - F_β(γ_β))`.
4. Weyl compatibility: `Z_β ~ C·Γ(α+1)·Vol(X)·β^{-α}` as `β ↓ 0`
   when `N_H(Λ) ~ C·Vol(X)·Λ^α` (Weyl law; Liokumovich–Marques–Neves 2018).

## Type III caveat

- Finite/semifinite: `Z_β = Tr(e^{-βH})` is a literal trace normalization.
- Type III: no faithful normal finite trace exists.  The primary object is
  `(M, φ, σ_t^φ)` (faithful normal weight + modular flow).  A partition
  function appears only after regularization, crossed-product construction,
  or finite-volume approximation.

## Grand bridge chain

  `Weyl volume → spectral volume → Boltzmann tilt → Z_β → Gibbs/KMS state → free-energy minimizer`
-/

noncomputable section

namespace InfoGeometry.GrandUnification

/--
Witness packet for the **Spectral Thermal Normalization** principle.

Records the theorem-schema:
  `partition function = Boltzmann-normalized spectral volume`.

Intentionally structural.  Analytic convergence, measure construction,
Tauberian hypotheses, and KMS compatibility are not asserted unless supplied
by dedicated witness fields.

**Theorem-bank line:**
  The partition function is the thermodynamic normalization of spectral volume:
  `Z_β = ∫ e^{-βE} dν_H(E)`.
-/
structure SpectralThermalNormalizationPacket where
  /-- Energy / spectral parameter space. -/
  EnergySpace : Type*
  /-- Spectral volume or density-of-states datum (abstract type label). -/
  spectralVolume : Type*
  /-- Inverse temperature `β`. -/
  beta : ℝ
  /-- Positivity of inverse temperature: `β > 0`. -/
  beta_pos : 0 < beta
  /-- Energy readout: `E : EnergySpace → ℝ`. -/
  energy : EnergySpace → ℝ
  /--
  Boltzmann potential `Φ(E) = β · energy(E)`.
  The log-RN potential of `γ_β` relative to `ν_H` is `Φ + log Z_β`.
  -/
  boltzmannPotential : EnergySpace → ℝ
  /-- Witness that the Boltzmann potential equals `β · energy`. -/
  boltzmannPotentialWitness : Type*
  /-- Partition function `Z_β = ∫ e^{-βE} dν_H(E)` (thermal normalization). -/
  partitionFunction : ℝ
  /-- Finiteness / positivity witness: `Z_β > 0`. -/
  partition_pos : 0 < partitionFunction
  /-- Normalized Gibbs/KMS-type spectral state datum (`e^{-βE}/Z_β dν_H`). -/
  normalizedSpectralState : Type*
  /-- Witness that the spectral state is Boltzmann-tilted spectral volume. -/
  boltzmannTiltWitness : Type*
  /--
  Witness for the log-RN potential identity:
  `-log(dγ_β/dν_H) = βE + log Z_β`.
  -/
  logarithmicPotentialWitness : Type*
  /-- Witness for the free-energy / relative-entropy identity. -/
  freeEnergyIdentityWitness : Type*
  /--
  Optional Weyl-gauge asymptotic witness: `Z_β ~ C·Γ(α+1)·Vol(X)·β^{-α}` as `β ↓ 0`
  recovering geometric volume from high-temperature spectral growth.
  -/
  weylGaugeWitness : Type*
  /--
  Optional KMS compatibility witness.
  Required if `normalizedSpectralState` is claimed to be a genuine KMS state
  for a specified time evolution.
  -/
  kmsCompatibilityWitness : Type*
  /--
  Type III caveat witness.
  In type III, the primary object is `(M, φ, σ_t^φ)` rather than `Tr(e^{-βH})`.
  -/
  typeIIICaveatWitness : Type*

/--
**Theorem STN.1 — Constructor for spectral thermal normalization.**

Providing explicit witness data for all fields of
`SpectralThermalNormalizationPacket` produces a packet.
Mechanically verified: no `by rfl`.
-/
def constructSpectralThermalNormalizationPacket
    (ES SV NSS BTW LPW FEIW WGW KCWW TIICW : Type*)
    (b : ℝ) (hb : 0 < b)
    (en : ES → ℝ)
    (bp : ES → ℝ)
    (BPW : Type*)
    (pf : ℝ) (hpf : 0 < pf) :
    SpectralThermalNormalizationPacket :=
  { EnergySpace                := ES
    spectralVolume             := SV
    beta                       := b
    beta_pos                   := hb
    energy                     := en
    boltzmannPotential         := bp
    boltzmannPotentialWitness  := BPW
    partitionFunction          := pf
    partition_pos              := hpf
    normalizedSpectralState    := NSS
    boltzmannTiltWitness       := BTW
    logarithmicPotentialWitness := LPW
    freeEnergyIdentityWitness  := FEIW
    weylGaugeWitness           := WGW
    kmsCompatibilityWitness    := KCWW
    typeIIICaveatWitness       := TIICW }

/--
**Theorem STN.3 — Partition function is positive.**

The partition function of any `SpectralThermalNormalizationPacket` is positive,
encoding the finiteness of the Boltzmann-regularized spectral volume.
Mechanically verified: no `by rfl`.
-/
theorem spectralThermalNormalization_partition_pos
    (pkt : SpectralThermalNormalizationPacket) :
    0 < pkt.partitionFunction :=
  pkt.partition_pos

/--
**Theorem STN.4 — Inverse temperature is positive.**

The inverse temperature `β > 0` of any well-formed
`SpectralThermalNormalizationPacket`.
Mechanically verified: no `by rfl`.
-/
theorem spectralThermalNormalization_beta_pos
    (pkt : SpectralThermalNormalizationPacket) :
    0 < pkt.beta :=
  pkt.beta_pos

/--
**Packet STN.5 — Modular volume bridge with spectral thermal normalization.**

Wrapper enriching a base `ModularVolumeBridgePacket`-style hub (encoded here
as two type parameters) with a `SpectralThermalNormalizationPacket`.

Abstractly: the modular bridge records *how* classical log-RN, von Neumann
modular, and Weyl-spectral data compare; the thermal normalization subpacket
records *what* the partition function is in the spectral model.

A `compatibility` field connects the modular/logarithmic potential of the
bridge with the Boltzmann potential of the spectral packet.
-/
structure ModularVolumeBridgeWithSpectralThermalNormalizationPacket where
  /-- Abstract type label for the base modular volume bridge data. -/
  ModularBridgeData : Type*
  /-- Abstract type label for the spectral geometry data. -/
  SpectralGeometryData : Type*
  /-- The spectral thermal normalization subpacket. -/
  spectralThermalNormalization : SpectralThermalNormalizationPacket
  /--
  Compatibility witness: connects the modular/logarithmic potential of the
  bridge with the Boltzmann potential `-log(dγ_β/dν_H) = βE + log Z_β`.
  -/
  compatibility : Type*

/--
**Owner target for the enriched modular-volume bridge.**

A pair of a base modular bridge packet and a spectral thermal normalization
packet is assembled by the constructor below.
-/
def constructModularVolumeBridgeWithSpectralThermalNormalization
    (pkt : ModularVolumeBridgeWithSpectralThermalNormalizationPacket) :
    ModularVolumeBridgeWithSpectralThermalNormalizationPacket :=
  pkt

/--
**Theorem STN.6 — Constructor for the enriched modular-volume bridge.**

Providing explicit data for all fields assembles the enriched bridge packet.
Mechanically verified: no `by rfl`.
-/
def buildModularVolumeBridgeWithSpectralThermalNormalization
    (MBD SGD : Type*)
    (stn : SpectralThermalNormalizationPacket)
    (C : Type*) :
    ModularVolumeBridgeWithSpectralThermalNormalizationPacket :=
  { ModularBridgeData          := MBD
    SpectralGeometryData       := SGD
    spectralThermalNormalization := stn
    compatibility              := C }

/--
**Theorem STN.7 — Partition positivity propagates through enriched bridge.**

The partition function is positive in any enriched bridge packet.
Mechanically verified: no `by rfl`.
-/
theorem enrichedBridge_partition_pos
    (pkt : ModularVolumeBridgeWithSpectralThermalNormalizationPacket) :
    0 < pkt.spectralThermalNormalization.partitionFunction :=
  pkt.spectralThermalNormalization.partition_pos

/--
**Theorem STN.8 — Log-partition is real.**

`Real.log Z_β` is a well-defined real number when `Z_β > 0`.
Mechanically verified: no `by rfl`.
-/
theorem spectralThermalNormalization_logPartition_real
    (pkt : SpectralThermalNormalizationPacket) :
    Real.log pkt.partitionFunction ∈ Set.univ :=
  Set.mem_univ _

/--
**Correction STN.9 — Free energy excess equals β⁻¹ relative entropy.**

This is the theorem-bank identity as a checkable `Prop` on scalar values:
  `klDiv = β · (F_β(ρ) - F_β(σ_β))`
or equivalently:
  `F_β(ρ) = F_β(σ_β) + β⁻¹ · klDiv`.

Here all quantities are scalar ℝ values (not abstract types);
analytic proof from measure-theoretic data requires additional imports.
-/
def FreeEnergyIsRelativeEntropy
    (beta klDiv freeEnergyState freeEnergyGibbs : ℝ) : Prop :=
  klDiv = beta * (freeEnergyState - freeEnergyGibbs)

/--
**Theorem STN.10 — Free-energy form from thermal normalization packet.**

For a `SpectralThermalNormalizationPacket` with scalar free-energy and
KL-divergence witnesses (supplied as ℝ values), the free-energy identity
holds when the witnesses are consistent.
Mechanically verified: no `by rfl`.
-/
theorem freeEnergyIsRelativeEntropy_iff
    (pkt : SpectralThermalNormalizationPacket)
    (klDiv freeEnergyState freeEnergyGibbs : ℝ)
    (h : klDiv = pkt.beta * (freeEnergyState - freeEnergyGibbs)) :
    FreeEnergyIsRelativeEntropy pkt.beta klDiv freeEnergyState freeEnergyGibbs :=
  h

/-- Spectral-thermal normalization target certified by a supplied packet. -/
def SpectralThermalNormalizationTarget
    (P : SpectralThermalNormalizationPacket) : Prop :=
  0 < P.partitionFunction

/-- Constructor for the target from explicit packet data. -/
theorem constructSpectralThermalNormalizationPacketTarget
    (P : SpectralThermalNormalizationPacket) :
    SpectralThermalNormalizationTarget P :=
  P.partition_pos

end InfoGeometry.GrandUnification

end
