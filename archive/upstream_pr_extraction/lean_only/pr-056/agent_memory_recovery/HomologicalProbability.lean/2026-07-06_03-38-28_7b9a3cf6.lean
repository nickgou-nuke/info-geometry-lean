chain explicitly in the bridge architecture.
-/
structure ModularVolumeBridgeWithThermal where
  /-- The base modular volume bridge (§26). -/
  bridge : ModularVolumeBridgePacket
  /-- Spectral thermal normalization subpacket (§27). -/
  spectralThermalNormalization : SpectralThermalNormalizationPacket

/--
**Theorem 27.3 — Constructor for the extended bridge packet.**

Providing a base `ModularVolumeBridgePacket` and a
`SpectralThermalNormalizationPacket` assembles the extended bridge.
Mechanically verified: no `by rfl`.
-/
def constructModularVolumeBridgeWithThermal
    (b : ModularVolumeBridgePacket)
    (t : SpectralThermalNormalizationPacket) :
    ModularVolumeBridgeWithThermal :=
  { bridge                     := b
    spectralThermalNormalization := t }

/--
**Theorem 27.4 — Thermal normalization is positive in the extended bridge.**

The partition function of the spectral thermal normalization subpacket
is positive by construction (from `partition_pos`).
Mechanically verified: no `by rfl`.
-/
theorem extendedBridge_partition_pos
    (pkt : ModularVolumeBridgeWithThermal) :
    0 < pkt.spectralThermalNormalization.partitionFunction :=
  pkt.spectralThermalNormalization.partition_pos

/--
**Theorem 27.5 — §26 `SpectralVolumeWeightPacket` specializes to the
thermal normalization packet.**

The finite spectral-weight data from §26 instantiates the abstract
`SpectralThermalNormalizationPacket`, with:
- `EnergySpace = Fin n` (finite spectrum);
- `boltzmannPotential e = beta * energyLevel e`;
- `partitionFunction = Z_β` (positive by `partitionFunction_pos`).
Mechanically verified: no `by rfl`.
-/
def spectralWeightPacketToThermal
    (svw : SpectralVolumeWeightPacket)
    (hbeta : 0 < svw.beta)
    (SVD BT LW FE WG TC : Type*) :
    SpectralThermalNormalizationPacket :=
  { EnergySpace             := Fin svw.n
    SpectralVolumeDatum      := SVD
    beta                     := svw.beta
    beta_pos                 := hbeta
    energy                   := svw.energyLevel
    boltzmannPotential       := fun i => svw.beta * svw.energyLevel i
    boltzmannPotential_eq    := fun _ => rfl
    partitionFunction        := svw.partitionFunction
    partition_pos            := svw.partitionFunction_pos
    NormalizedSpectralState  := BT
    BoltzmannTiltWitness     := BT
    LogarithmicPotentialWitness := LW
    FreeEnergyIdentityWitness   := FE
    WeylGaugeWitness            := WG
    TypeIIICaveatWitness        := TC }

end SpectralThermalNormalization

end InfoGeometry.Probability.Homological
