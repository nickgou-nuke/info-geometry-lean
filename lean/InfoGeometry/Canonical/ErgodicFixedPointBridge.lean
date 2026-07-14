import InfoGeometry.Canonical.KMSConditionBridge
import InfoGeometry.Canonical.TypeIIIModularCantorSystem

open scoped InnerProductSpace

noncomputable section

/-!
# Ergodic Fixed-Point Bridge

Witness-gated operator fixed-point socket for the bounded KMS/modular lane.

This file does not prove von Neumann's mean ergodic theorem, does not construct
an operator integral, and does not assert a type-III centralizer theorem.
It packages the theorem-safe readout:

* modular time invariance through the installed KMS flow;
* scale/self-similarity invariance through a supplied renormalization map;
* optional compatibility with the Drazin regular-support lane.
-/

namespace ErgodicFixedPointBridge

open InfoGeometry.Canonical.KMSConditionBridge
open InfoGeometry.Canonical.TypeIIIModularCantorSystem

section Core

variable {E LieAlgebra : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Operator ergodic/self-similar socket over a bounded KMS condition bridge.

`ergodicMean` is a supplied smoothing/readout map.  Concrete models may realize
it as a Cesaro/integral limit; this bridge only records the fixed-sector laws.
-/
@[rep_depth thermo]
structure OperatorErgodicFixedPointBridge where
  /-- Installed bounded KMS/modular observable action. -/
  kms :
    BoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra)

  /-- Supplied ergodic smoothing/conditional-expectation shadow. -/
  ergodicMean : EndH → EndH

  /-- Supplied dyadic/Cantor renormalization or self-similarity operator. -/
  renorm : EndH → EndH

  /-- The ergodic mean is fixed by modular time. -/
  ergodicMean_modularFixed :
    ∀ t : ℝ, ∀ A : EndH, kms.kmsFlow t (ergodicMean A) = ergodicMean A

  /-- The ergodic mean is idempotent. -/
  ergodicMean_idempotent :
    ∀ A : EndH, ergodicMean (ergodicMean A) = ergodicMean A

  /-- The supplied renormalization preserves the modular fixed sector. -/
  renorm_preserves_modularFixed :
    ∀ A : EndH, (∀ t : ℝ, kms.kmsFlow t A = A) →
      ∀ t : ℝ, kms.kmsFlow t (renorm A) = renorm A

  /-- The ergodic mean is scale/self-similar under the supplied renormalization. -/
  renorm_ergodicMean_fixed :
    ∀ A : EndH, renorm (ergodicMean A) = ergodicMean A

  /--
  Optional centralizer readout.

  In concrete standard-form/type-III models this may be the state centralizer
  condition.  It is kept as a supplied predicate here.
  -/
  centralizerLike : EndH → Prop

  /-- Modular fixed points lie in the supplied centralizer-like predicate. -/
  modularFixed_mem_centralizerLike :
    ∀ A : EndH, (∀ t : ℝ, kms.kmsFlow t A = A) → centralizerLike A

  /-- The ergodic mean preserves regular-support commutation. -/
  ergodicMean_regularSupportStable :
    ∀ A : EndH,
      kms.bounded.souriau.superBridge.CIK.spectralProjector * A =
          A * kms.bounded.souriau.superBridge.CIK.spectralProjector →
        kms.bounded.souriau.superBridge.CIK.spectralProjector * ergodicMean A =
          ergodicMean A * kms.bounded.souriau.superBridge.CIK.spectralProjector

namespace OperatorErgodicFixedPointBridge

variable (B : OperatorErgodicFixedPointBridge (E := E) (LieAlgebra := LieAlgebra))

/-- Modular-time fixed predicate. -/
@[rep_depth thermo]
def IsModularFixed (A : EndH) : Prop :=
  ∀ t : ℝ, B.kms.kmsFlow t A = A

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
  B.modularFixed_mem_centralizerLike (A := B.ergodicMean A) (B.ergodicMean_isModularFixed A)

end OperatorErgodicFixedPointBridge

end Core

section Cantor

variable {Op : Type*} [AddCommMonoid Op]

/--
Dyadic renormalization socket indexed by binary words.

The concrete Cuntz/Jones isometries are not constructed here.  The local
children and the renormalization law are supplied as operator data.
-/
@[rep_depth projective]
structure CantorDyadicRenormalization (Op : Type*) [AddCommMonoid Op] where
  /-- Cylinder/operator attached to a finite binary word. -/
  cylinder : BinaryWord → Op

  /-- Abstract dyadic renormalization map. -/
  renorm : Op → Op

  /-- Supplied dyadic self-similarity law. -/
  renorm_cylinder :
    ∀ w : BinaryWord,
      renorm (cylinder w) =
        cylinder (BinaryWord.child w false) + cylinder (BinaryWord.child w true)

namespace CantorDyadicRenormalization

variable (C : CantorDyadicRenormalization Op)

end CantorDyadicRenormalization

end Cantor

end ErgodicFixedPointBridge
