# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:04.587438+00:00`
Root: `lean/InfoGeometry/ModularVolumePotential.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **64**
- Hard: **0**
- Soft: **61**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ModularVolumePotential.lean` | `advisory` | 125 | 0 | 61 | 3 | 64 |

## Findings by file

### `lean/InfoGeometry/ModularVolumePotential.lean`
- module: `InfoGeometry.ModularVolumePotential`
- status: `advisory`
- debt_score: `125`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field LogRadonNikodymPacket.relativeDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field LogRadonNikodymPacket.logPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field LogRadonNikodymPacket.logPotential_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field RelativeSurprisalPacket.relativeLogPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field RelativeSurprisalPacket.klReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field RelativeSurprisalPacket.klReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field GibbsFreeEnergyPacket.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `law-field-locker` in `structure-field GibbsFreeEnergyPacket.gibbsWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field GibbsFreeEnergyPacket.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field GibbsFreeEnergyPacket.klToGibbs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field GibbsFreeEnergyPacket.gibbsWeight_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field GibbsFreeEnergyPacket.freeEnergy_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field ModularFlowPacket.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field ModularFlowPacket.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field ModularFlowPacket.connesCocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field ModularFlowPacket.relativeModularPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field ModularFlowPacket.hasTraceReference` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field ModularFlowPacket.tracePartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field ModularFlowPacket.kmsPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field SupervolumePacket.evenTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field SupervolumePacket.oddTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field SupervolumePacket.supertrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `law-field-locker` in `structure-field SupervolumePacket.supertrace_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field GKSLPacket.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field GKSLPacket.anticommutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field GKSLPacket.involution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field GKSLPacket.freeEnergyShadow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field GKSLPacket.freeEnergyDecay` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field GKSLPacket.freeEnergyDecay_holds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field GKSLPacket.freeEnergy_monotone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field SpectralBoltzmannPacket.spectralEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field SpectralBoltzmannPacket.spectralVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field SpectralBoltzmannPacket.modularPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `structure-field SpectralBoltzmannPacket.boltzmannFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field SpectralBoltzmannPacket.modularPotential_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field SpectralBoltzmannPacket.boltzmannFactor_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field FiniteSpectralBoltzmannPartition.partition_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [advisory] `existential-packaging` in `def FiniteSpectralThermalNormalizationTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L291 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.spectralVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.inverseTemperature_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannPotential_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.partitionFunction_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannTiltWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.logarithmicPotentialWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.freeEnergyIdentityWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L316 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.weylGaugeWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannTilt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [soft] `law-field-locker` in `structure-field ModularTransportBridgePacket.cocycleTransportCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L444 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.klDivergence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L450 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.spectralVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L452 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.weylVolumeGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L458 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.entropyComparison` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L460 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.freeEnergyComparison` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L462 [soft] `law-field-locker` in `structure-field ModularVolumeBridgePacket.spectralVolumeComparison` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L496 [soft] `law-field-locker` in `structure-field TomitaGromovBridgePacket.spectralThermalNormalization_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L499 [soft] `law-field-locker` in `structure-field TomitaGromovBridgePacket.modularTransport_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L514 [advisory] `existential-packaging` in `def ModularVolumePotentialTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L547 [soft] `simp-law-injection` in `simp-declaration logPotential_eq_neg_log_density` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L567 [soft] `simp-law-injection` in `simp-declaration gibbsWeight_eq_exp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L593 [soft] `simp-law-injection` in `simp-declaration supertrace_eq_even_sub_odd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

