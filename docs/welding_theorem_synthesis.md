# Synthesis Note: Anomaly-Identification Welding Chain

## Scope and Status
This note is a reference-memory synthesis for the current weld between:
- the count/projective/operator trunk, and
- the doubled/Krein/phase-space transport trunk.

It is not a proof source. Lean declarations are the authority.

The goal here is strict separation between:
- compiler-checked theorem chain,
- structural interpretation,
- synthesis inference and remaining closure.

## 1. Obstruction source (compiler-checked)
The canonical obstruction operator is defined as the projector commutator package:

- `projectorObstruction := chiralAnomalyOperator`
  - `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:19`
- exact commutator identity
  - `projectorObstruction_eq_commutator`
  - `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:25`

In symbols:

`projectorObstruction = P_D * P_MP - P_MP * P_D`.

## 2. Einstein-anomaly identification (compiler-checked)
On the conformal surface:

- unconditional right-anomaly bridge:
  - `einsteinAnomaly_eq_neg_rightChiralAnomaly`
  - `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- left-anomaly bridge under projector agreement:
  - `einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement`
  - `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:646`

So the left-chiral identification is proved, but conditionally (via MP left/right projector agreement).

## 3. Weyl holonomy as scalar obstruction readout (compiler-checked)
In the doubled Weyl bridge:

- `holonomy_eq_projectorObstruction_nnnorm_and_bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_self_of_flat_of_commute_generator`
  - `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean:429`

The scalar output is explicit:

`holonomy = ‖projectorObstruction‖₊`

under the stated flatness bridge assumptions.

## 4. Bogoliubov conjugation as operator readout (compiler-checked)
The operator channel is formalized through:

- exact conjugation model:
  - `bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg`
- infinitesimal derivation:
  - `deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularDeriv`
  - `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean:518`
- gauge/sourcing split at derivative level:
  - `..._eq_relativeModularSourceDeriv_of_commute_gaugePart`
  - `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean:533`

Important exactness note:
the source-channel derivative statement is conditional on `hCommGauge`; it is not unconditional.

## 5. Mechanic of the weld: transport split first, QGT readout second
The decisive transport operators are already named in:
`lean/InfoGeometry/Canonical/BogoliubovTransport.lean`:

- `relativeModularKGenerator` (`:440`)
- `relativeModularDeriv` (`:444`)
- `modularGaugeDeriv` (same block)
- `relativeModularSourceDeriv` (`:448`)
- `relativeModularSinkDeriv` (`:452`)
- decomposition theorem:
  - `relativeModularDeriv_eq_modularGaugeDeriv_add_relativeModularSourceDeriv` (`:472`)

This is the mechanic layer of the weld.
QGT is downstream readout of this operator transport package.

## 6. QGT mapping: proved vs inferred
### 6.1 What is already proved
In `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`:

- infinitesimal metric-seed transport reads modular derivations
  - e.g. `deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv`
- gauge/source split readout for metric seeds
  - `..._eq_metricOf_modularGaugeDeriv_add_metricOf_relativeModularSourceDeriv` (`:228`)
- certified Einstein-anomaly specialization to source channel under gauge commutation
  - `deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart` (`:305`)
- Hilbert/Krein agreement on QGT metric and Berry components after `ε`-transport
  - `qgtOfOperator_modularSignEpsilon_comp_metric_eq_kreinQgtOfOperator_metric` (`:703`)
  - `qgtOfOperator_modularSignEpsilon_comp_berry_eq_kreinQgtOfOperator_berry` (`:724`)

### 6.2 Current synthesis inference
The current package strongly supports:
- obstruction/anomaly as the curvature-carrying operator packet,
- scalar holonomy as its norm readout,
- QGT metric/Berry layers as transport readouts of the same `K`-structured operator lift.

### 6.3 Remaining closure theorem
Still to close explicitly:
- a direct endpoint theorem identifying the Berry-side generator with the canonical projector-obstruction/anomaly package under canonical weld hypotheses.

## 7. Why the weld is curved rather than flat
On current theorem surfaces, the trunks weld by obstruction-mediated coherence:
- scalar channel: obstruction norm appears as Weyl holonomy readout;
- operator channel: anomaly is either transport-invariant (commuting-generator regime) or evolves via modular source derivation (gauge-commuting split regime).

This is stronger than prose adjacency and weaker than claiming every QGT imaginary component is already theorem-identical to projector obstruction.

## 8. Minimal next trace
To keep closure rigorous, trace this theorem path next:
1. `BogoliubovTransport` generator/split primitives,
2. `EinsteinAnomalyOperator` lifted anomaly transport laws,
3. `GeometricTensorOperatorLift` bridge from lifted anomaly transport into `qgtOfOperator`/`kreinQgtOfOperator` readouts.
