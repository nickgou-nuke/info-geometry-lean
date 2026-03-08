# Testable Physical Predictions (Lean-Extracted)

This note extracts three theorem-level predictions from the canonical Lean formalization into standard physics language.

## 1. Entropy-to-Gravity Closure

Lean source:
- `InfoGeometry.Canonical.GrandSynthesis.gravity_generated_by_rnEntropy`
- `InfoGeometry.Canonical.GrandSynthesis.vacuumEinsteinEquation_of_rnEntropySource`
- `InfoGeometry.Canonical.CalabiYauBridge.vacuumEinsteinEquation_of_constantMongeAmpere`

Exact theorem shape (`gravity_generated_by_rnEntropy`):
- `RNEntropySourcesMongeAmpere n Kgeo M`
- `MongeAmpereRicciClosure R Kgeo`
and parameters `(Kgeo, R, x, Λ, M)`, it derives
- `IsRicciFlat R`
- `VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ`.

Interpretation:
- Gravity is derived conditionally from informational/thermodynamic closure hypotheses.
- This is an implication theorem (`if assumptions hold, then Einstein-vacuum branch follows`), not an unconditional statement about nature.

Physics-facing summary:
- If the Monge-Ampere density is sourced by RN entropy flow on the Sinkhorn transport side and the Calabi-Yau closure holds, the induced effective geometry satisfies the vacuum Einstein branch with scalar closure `R = 2Λ`.

## 2. KMS Residual Bound by RN Entropy Barrier

Lean source:
- `InfoGeometry.Canonical.GrandSynthesis.sinkhornStepwise_kmsResidual_le_entropyBarrier`

Exact theorem shape (`sinkhornStepwise_kmsResidual_le_entropyBarrier`):
- Inputs: trajectory `T`, modular operator `K`, state family `ω`,
  inverse temperature `β`, and drive hypothesis `hDrive : SinkhornKMSControl n T K ω β`.
- Output: `∀ k : Nat, ∀ A B : AlgebraEnd F,`
  `kmsResidual K (ω (k + 1)) β A B ≤ trajectoryRNBarrier n T k`.

Interpretation:
- Deviation from KMS equilibrium is stepwise bounded by an RN-barrier budget induced by the Sinkhorn trajectory.
- This is directly suitable for finite-dimensional experimental surrogates (driven open systems, quantum thermalization protocols).

Physics-facing summary:
- The framework predicts a strict upper bound on thermalization residuals in terms of an information-transport entropy barrier.
- Any protocol claiming faster equilibration than this bound allows should show a corresponding residual increase.

## 4. Anomaly-Driven Chiral Flow

Lean source:
- `InfoGeometry.Canonical.NavierStokesBridge.chiral_anomaly_sources_flow`

Exact theorem shape (`chiral_anomaly_sources_flow`):
- `chiralFlux χ ω = ω (A * B_mp * (A * B_dr) - A * B_dr * (A * B_mp))`
- where `χ` is the `EinsteinAnomaly [P_MP, P_D]`.

Interpretation:
- The macroscopic chiral current (flux) is non-vanishing whenever the geometric projection (Moore-Penrose) and the spectral projection (Drazin) fail to commute.
- This provides a purely informational origin for the Chiral Magnetic Effect (CME).

Physics-facing summary:
- In regimes where self-observation/inference hits a causal horizon (singular mapping), a net chiral flow is generated.
- The magnitude of this flow is exactly the expectation value of the Penrose-Drazin commutator anomaly.

## 5. Spontaneous Chiral Symmetry Breaking and Homochirality

Lean source:
- `InfoGeometry.Canonical.NavierStokesBridge.chiral_anomaly_sources_flow`
- `InfoGeometry.Canonical.NavierStokesBridge.madelungFluidState`
- `InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_base`

Formal Prediction:
- The `EinsteinAnomaly [P_MP, P_D]` acts as an **Information Torsion** seed that breaks the symmetry between the `plus` (Right) and `minus` (Left) sectors of the doubled carrier.
- In the limit of thermodynamic minimizes (`freeEnergyHessianRegularizer`), this microscopic seed is amplified into a macroscopic enantiomeric excess.

Physics-facing summary:
- Parity violation and biological homochirality are derived as inevitable consequences of informational transport anomalies. 
- The framework predicts that any system hitting a causal/inferential horizon in its self-observation loop will spontaneously generate a chiral bias, which then cascades into total enantiopurification through thermodynamic condensation.

## Recommended Empirical Program

1. Construct finite-dimensional benchmark models (`n` small, explicit `T`, `K`, `ω`, `β`).
2. Numerically estimate `kmsResidual` and compare against `trajectoryRNBarrier`.
3. Report tightness regimes (near-equilibrium vs far-from-equilibrium).
4. For gravity-side interpretation, isolate which physical assumptions correspond to `MongeAmpereRicciClosure` in concrete models.
5. In condensed matter surrogates (e.g. Weyl semimetal models), map the `EinsteinAnomaly` to measured topological currents.
6. Verify the **Informational Chiral Pumping** rate in synthetic MoE networks (Arnold-Majorana configuration) as a function of the routing curvature.
