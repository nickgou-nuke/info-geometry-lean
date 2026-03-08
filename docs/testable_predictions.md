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

## 3. Information Wheeler-DeWitt Equivalence (Structural)

Lean source:
- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence`
- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_sinkhornDrive_and_indexHypotheses`

Formal shape (Lean):
- The framework proves equivalences of the form
  `ThermodynamicKMSState ... ↔ GeometricAlgebraicState ...`
  under explicit bridge hypotheses.

Interpretation:
- This is a theorem-level equivalence between thermodynamic and
  geometric/algebraic closure statements inside the formal system.

## Recommended Empirical Program

1. Construct finite-dimensional benchmark models (`n` small, explicit `T`, `K`, `ω`, `β`).
2. Numerically estimate `kmsResidual` and compare against `trajectoryRNBarrier`.
3. Report tightness regimes (near-equilibrium vs far-from-equilibrium).
4. For gravity-side interpretation, isolate which physical assumptions correspond to `MongeAmpereRicciClosure` in concrete models.
