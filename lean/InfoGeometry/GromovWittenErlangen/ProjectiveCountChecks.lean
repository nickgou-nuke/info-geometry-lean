import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge
import InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge
import InfoGeometry.GromovWittenErlangen.ProjectiveCountDrazinFrobeniusBridge
import InfoGeometry.GromovWittenErlangen.ProjectiveCountProbabilityDrazinBridge

/-!
# InfoGeometry.GromovWittenErlangen.ProjectiveCountChecks

Entrypoint smoke checks for the GW projective-count corridor.

The checks intentionally follow the owner descent:

```text
Primitive projective counts
  → GW projective count calibration
  → canonical count ray / FinProb / surprisal operator lift
  → Drazin/Frobenius readout
```
-/

noncomputable section

namespace InfoGeometry.GromovWittenErlangen.ProjectiveCountChecks

/-- Owner surface for GW localization shadows of primitive projective counts. -/
abbrev GWProjectiveCountCalibrationType (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
    (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Primitive L0/L1/L2 projective-count bridge. -/
abbrev GWProjectiveCountStateType (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge.GWProjectiveCountState
    (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Canonical finite count-ray/probability bridge. -/
abbrev GWCanonicalCountRayBridgeType
    (n : ℕ) [Nonempty (Fin n)] (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge
    (n := n) (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Repo-native projective count probability/operator bridge. -/
abbrev GWProjectiveCountProbabilityBridgeType
    (n : ℕ) [Nonempty (Fin n)] (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.GWProjectiveCountProbabilityBridge
    (n := n) (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Drazin-attached projective count/probability bridge. -/
abbrev GWProjectiveCountDrazinBridgeType
    (n : ℕ) [Nonempty (Fin n)] (G T Target Coeff Algebra : Type*) [Ring Algebra] :=
  @InfoGeometry.GromovWittenErlangen.GWProjectiveCountDrazinBridge
    (n := n) (G := G) (T := T) (Target := Target) (Coeff := Coeff) (Algebra := Algebra)

/-- Projective count to Drazin/Frobenius bridge. -/
abbrev ProjectiveCountDrazinFrobeniusBridgeType
    (G T Target Coeff Algebra ModuliOperator : Type*) [Ring Algebra] :=
  @InfoGeometry.GromovWittenErlangen.ProjectiveCountDrazinFrobeniusBridge
    (G := G) (T := T) (Target := Target) (Coeff := Coeff)
    (Algebra := Algebra) (ModuliOperator := ModuliOperator)

/-- Smoke reference for primitive normalized-shape scale invariance. -/
abbrev normalizedShapeScaleCountsRef
    (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration.normalizedShape_scale_counts
    (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Smoke reference for canonical count-ray probability gauge. -/
abbrev stateFinProbApplyToRealRef
    (n : ℕ) [Nonempty (Fin n)] (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge.stateFinProb_apply_toReal
    (n := n) (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Smoke reference for entropy as expectation of the surprisal operator. -/
abbrev entropyAsSurprisalExpectationRef
    (n : ℕ) [Nonempty (Fin n)] (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.GWProjectiveCountProbabilityBridge.entropy_eq_diagonalExpectation_stateSurprisalOperator
    (n := n) (G := G) (T := T) (Target := Target) (Coeff := Coeff)

/-- Smoke reference for Drazin edge residue annihilation in the probability bridge. -/
abbrev edgeResidueMulRegularInverseRef
    (n : ℕ) [Nonempty (Fin n)] (G T Target Coeff Algebra : Type*) [Ring Algebra] :=
  @InfoGeometry.GromovWittenErlangen.GWProjectiveCountDrazinBridge.edgeResidue_mul_regularInverse
    (n := n) (G := G) (T := T) (Target := Target) (Coeff := Coeff) (Algebra := Algebra)

end InfoGeometry.GromovWittenErlangen.ProjectiveCountChecks
