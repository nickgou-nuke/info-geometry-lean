# Entropic-Transport Emergence of Vacuum Gravity and a KMS Residual Bound

## Draft Abstract (PRL style)

We present a machine-checked derivation, in Lean 4, linking information-theoretic transport structure to two physics-level consequences: (i) a conditional emergence of the vacuum Einstein branch and (ii) a non-equilibrium thermalization bound in KMS form. On the geometric side, we formalize that if Radon-Nikodym (RN) entropy transport sources a Monge-Ampere density and a Calabi-Yau-type closure condition holds, then the induced information geometry is Ricci-flat and satisfies a vacuum Einstein equation with cosmological term (`gravity_generated_by_rnEntropy` in `InfoGeometry.Canonical.GrandSynthesis`). On the dynamical side, we prove that the stepwise KMS residual is bounded by an RN entropy barrier along Sinkhorn transport trajectories (`sinkhornStepwise_kmsResidual_le_entropyBarrier`). These theorems are fully `sorry`-free in the referenced files.

To connect formal statements to measurement, we separate dimensionless theorem-level objects from dimensional observables via explicit calibration maps: a geometric scale constant `C` in the Monge-Ampere relation and an experimental scale factor for the KMS residual channel. This yields immediate falsifiability: protocols claiming thermalization faster than the RN barrier permits must exhibit corresponding residual growth. The framework therefore provides not only logical unification across geometry, transport, and operator thermodynamics, but also concrete inequality targets for near-term experiments in finite-dimensional driven quantum systems.

## Draft Introduction

Unification claims in mathematical physics often fail at the interface between formal consistency and empirical content. Modern proof assistants eliminate ambiguity in the former but do not by themselves provide the latter. The present work addresses this boundary directly: we extract two experimentally interpretable predictions from a fully mechanized Lean 4 framework in which information geometry, transport dynamics, and operator-theoretic thermodynamics are developed in a common typed setting.

The first result concerns gravity as an emergent thermodynamic sector. In the formal development, RN entropy transport and Monge-Ampere closure are encoded as hypotheses

- `RNEntropySourcesMongeAmpere n Kgeo M`,
- `MongeAmpereRicciClosure R Kgeo`.

Under these assumptions, the theorem

- `InfoGeometry.Canonical.GrandSynthesis.gravity_generated_by_rnEntropy`

derives

- `IsRicciFlat R`,
- `VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ`.

This is a strict implication theorem: it does not assume gravity axioms, but identifies the exact informational closure conditions under which the vacuum Einstein branch follows.

The second result is operational and near-term testable. The theorem

- `InfoGeometry.Canonical.GrandSynthesis.sinkhornStepwise_kmsResidual_le_entropyBarrier`

states that along a Sinkhorn-controlled trajectory with KMS control witness, the KMS residual at each step is bounded above by the trajectory RN barrier. In physics terms, non-equilibrium deviation from KMS periodicity cannot undercut the information-transport entropy budget. This places a concrete upper bound on thermalization performance in finite-dimensional driven systems.

For publication-facing use, dimensionalization must be explicit. We therefore introduce two calibration interfaces:

1. Geometric scale calibration:
   `det(g) = C exp(-ΔS_RN)`, where `C` carries units (e.g., via a characteristic length scale `ℓ_*`).
2. KMS-channel calibration:
   map the dimensionless RN barrier to measured residual units using a protocol-dependent scale `η` (set by experimental energy/time normalization).

With these maps fixed, both predictions become falsifiable inequalities/equations rather than interpretive analogies. In particular, violation of the KMS bound under controlled finite-dimensional dynamics would refute the transport-thermodynamic closure assumptions; agreement constrains admissible microscopic models.

This paper therefore contributes a reproducible workflow from theorem prover to physics statement: theorem names, assumptions, and inequality targets are explicit and auditable. The central claim is not that formal proof replaces experiment, but that it sharpens the experimental question by isolating minimal hypotheses and exact consequences.

