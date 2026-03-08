# Ontology Synthesis: What Is Time? What Is Space?

This note records the ontological closure of the `info-geometry-lean` framework:
time and space are derived structures, not primitive background objects.

## 1. Time as Emergent Entropy Flow

In `Canonical/HolographicEmergence.lean`, time is represented by `EmergentTimeFlow`
over Sinkhorn/Weyl-gauge trajectories.

- Time is not a pre-existing coordinate.
- A "tick" is an algorithmic inference update step.
- The arrow of time is the monotone Lyapunov descent
  (`trajectoryLyapunov_monotone`), i.e. free-energy descent / entropy ascent.

Interpretation: physical time corresponds to irreversible informational transport
under constrained optimization.

## 2. Space as Information-Matrix Geometry

In `Clifford/Spacetime.lean` and `Clifford/Soldering.lean`, spacetime vectors are
realized through a soldering map into matrix algebras (`M₂(ℝ)` / split quaternions).

- Coordinates are encoded as algebraic states.
- Geometric norm is recovered through determinant identities
  (e.g. `det_soldering_eq_q22`).
- Incidence/twistor-style relations encode points relationally, not as ambient
  primitives.

Interpretation: space is the geometric shadow of algebraic information states.

## 3. Unified Ontological Statement

The framework gives a constructive ontology:

1. Algebra and measure-theoretic dynamics are primary.
2. Time emerges from monotone computational transport.
3. Space emerges from matrix/soldering realizations of state relations.

This aligns the canonical stack with a fully derived spacetime viewpoint:
no fixed background manifold is assumed; geometry is produced by operator flow.

## 4. Fluid Circulation as Chiral Anomaly Flow

`Canonical/NavierStokesBridge.lean` adds an operator-to-fluid bridge layer:

- `anomaly_as_fluid_state_with_density` maps `EinsteinAnomaly` into a
  positive-density fluid state (`ρ > 0`).
- `modular_circulation_response` defines circulation through modular pairing
  `ω (Sigma.comp K)` instead of trace-based formulas.
- `hasDerivAt_modularVelocity_zero` and `deriv_modularVelocity_zero` identify
  the `β = 0` differential response of modular velocity with the modular
  Hamiltonian.
- `chiral_anomaly_sources_flow` states that the commutator anomaly sources
  chiral flux in the doubled/Krein setting.

Interpretation: circulation is encoded as anomaly-driven modular transport;
chiral imbalance is a flow observable, not an added primitive.
