import InfoGeometry.Canonical.BoundedKMSConditionBridge
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.BoundedKMSErgodicFixedPointBridge

Ergodic/self-similar fixed-point socket over the state-functional bounded KMS
condition bridge.

This is the `StateFunctional EndH` / `KMSAnalyticCertificate` counterpart of
`ErgodicFixedPointBridge`.  It does not construct Cesaro limits, determinant
classes, or Type-III centralizers.  It records the finite theorem-safe
consequences needed downstream:

* modular-time fixedness through `boundedKMS.flowDatum`;
* scale/self-similarity through a supplied renormalization map;
* optional centralizer-like membership;
* preservation of the Drazin regular-support lane.
-/

namespace InfoGeometry.Canonical.BoundedKMSErgodicFixedPointBridge

open InfoGeometry.Canonical.BoundedKMSConditionBridge
open InfoGeometry.Canonical.TypeIIIModularCantorSystem

section Core

variable {E LieAlgebra : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH :=
  inferInstance
local instance : IsTopologicalRing EndH :=
  inferInstance
local instance : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Operator ergodic/self-similar socket over the state-functional bounded KMS
bridge.

`ergodicMean` is supplied smoothing data.  Concrete models may realize it as
an operator mean/conditional expectation; this bridge only records fixed-sector
laws and regular-support stability.
-/
@[rep_depth thermo]
structure Bridge where
  /-- State-functional KMS socket for the bounded modular flow. -/
  kms :
    InfoGeometry.Canonical.BoundedKMSConditionBridge.Bridge
      (E := E) (LieAlgebra := LieAlgebra)

  /-- Supplied ergodic smoothing/conditional-expectation shadow. -/
  ergodicMean :
    EndH → EndH

  /-- Supplied dyadic/Cantor renormalization or self-similarity operator. -/
  renorm :
    EndH → EndH

  /-- The ergodic mean is fixed by bounded modular time. -/
  ergodicMean_modularFixed :
    ∀ t : ℝ, ∀ A : EndH, kms.flowDatum.flow t (ergodicMean A) = ergodicMean A

  /-- The ergodic mean is idempotent. -/
  ergodicMean_idempotent :
    ∀ A : EndH, ergodicMean (ergodicMean A) = ergodicMean A

  /-- The supplied renormalization preserves the modular fixed sector. -/
  renorm_preserves_modularFixed :
    ∀ A : EndH, (∀ t : ℝ, kms.flowDatum.flow t A = A) →
      ∀ t : ℝ, kms.flowDatum.flow t (renorm A) = renorm A

  /-- The ergodic mean is scale/self-similar under the supplied renormalization. -/
  renorm_ergodicMean_fixed :
    ∀ A : EndH, renorm (ergodicMean A) = ergodicMean A

  /-- Optional centralizer-like predicate supplied by the concrete model. -/
  centralizerLike :
    EndH → Prop

  /-- Modular fixed points lie in the supplied centralizer-like predicate. -/
  modularFixed_mem_centralizerLike :
    ∀ A : EndH, (∀ t : ℝ, kms.flowDatum.flow t A = A) → centralizerLike A

  /-- The ergodic mean preserves regular-support commutation. -/
  ergodicMean_regularSupportStable :
    ∀ A : EndH,
      kms.boundedFlow.souriau.superBridge.CIK.spectralProjector * A =
          A * kms.boundedFlow.souriau.superBridge.CIK.spectralProjector →
        kms.boundedFlow.souriau.superBridge.CIK.spectralProjector * ergodicMean A =
          ergodicMean A * kms.boundedFlow.souriau.superBridge.CIK.spectralProjector

namespace Bridge

variable (B : Bridge (E := E) (LieAlgebra := LieAlgebra))

/-- Modular-time fixed predicate for the state-functional bounded KMS flow. -/
@[rep_depth thermo]
def IsModularFixed (A : EndH) : Prop :=
  ∀ t : ℝ, B.kms.flowDatum.flow t A = A

/-- Renormalization/self-similarity fixed predicate. -/
@[rep_depth thermo]
def IsScaleFixed (A : EndH) : Prop :=
  B.renorm A = A

/-- Classicalized sector: fixed by modular time and by scale renormalization. -/
@[rep_depth thermo]
def IsSelfSimilarFixedPoint (A : EndH) : Prop :=
  B.IsModularFixed A ∧ B.IsScaleFixed A

/-- The ergodic mean is modular fixed. -/
@[rep_depth thermo]
theorem ergodicMean_isModularFixed (A : EndH) :
    B.IsModularFixed (B.ergodicMean A) := by
  intro t
  exact B.ergodicMean_modularFixed t A

/-- The ergodic mean is scale/self-similar. -/
@[rep_depth thermo]
theorem ergodicMean_isScaleFixed (A : EndH) :
    B.IsScaleFixed (B.ergodicMean A) :=
  B.renorm_ergodicMean_fixed A

/-- The ergodic mean lands in the self-similar fixed sector. -/
@[rep_depth thermo]
theorem ergodicMean_isSelfSimilarFixedPoint (A : EndH) :
    B.IsSelfSimilarFixedPoint (B.ergodicMean A) :=
  ⟨B.ergodicMean_isModularFixed A, B.ergodicMean_isScaleFixed A⟩

/-- Self-similar fixed points are modular fixed. -/
@[rep_depth thermo]
theorem modularFixed_of_selfSimilarFixedPoint
    {A : EndH} (hA : B.IsSelfSimilarFixedPoint A) :
    B.IsModularFixed A :=
  hA.1

/-- Self-similar fixed points are scale fixed. -/
@[rep_depth thermo]
theorem scaleFixed_of_selfSimilarFixedPoint
    {A : EndH} (hA : B.IsSelfSimilarFixedPoint A) :
    B.IsScaleFixed A :=
  hA.2

/-- The ergodic mean lands in the supplied centralizer-like predicate. -/
@[rep_depth thermo]
theorem ergodicMean_mem_centralizerLike (A : EndH) :
    B.centralizerLike (B.ergodicMean A) :=
  B.modularFixed_mem_centralizerLike
    (A := B.ergodicMean A) (B.ergodicMean_isModularFixed A)

end Bridge

end Core

end InfoGeometry.Canonical.BoundedKMSErgodicFixedPointBridge
