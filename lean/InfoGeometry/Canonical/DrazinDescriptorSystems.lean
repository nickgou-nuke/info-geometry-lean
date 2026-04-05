import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# InfoGeometry.Canonical.DrazinDescriptorSystems

Descriptor-style exponential flows for the Drazin core/nilpotent split.

This file keeps the scope narrow:

- scalar generators attached to the ambient/core/nilpotent operators,
- commutation of the core and nilpotent generators,
- exact exponential factorization of the ambient flow through those two pieces.
-/

namespace InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E
noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Ambient scalar generator attached to the certified inverse kernel. -/
@[rep_depth transport]
noncomputable def ambientGenerator (t : ℝ) : EndH :=
  t • CIK.A

/-- Drazin-core scalar generator. -/
@[rep_depth transport]
noncomputable def coreGenerator (t : ℝ) : EndH :=
  t • CIK.corePart

/-- Complementary nilpotent scalar generator. -/
@[rep_depth transport]
noncomputable def nilpotentGenerator (t : ℝ) : EndH :=
  t • CIK.nilpotentPart

/-- Ambient exponential flow. -/
@[rep_depth transport]
noncomputable def ambientFlow (t : ℝ) : EndH :=
  NormedSpace.exp (CIK.ambientGenerator t)

/-- Exponential flow of the Drazin-core generator. -/
@[rep_depth transport]
noncomputable def coreFlow (t : ℝ) : EndH :=
  NormedSpace.exp (CIK.coreGenerator t)

/-- Exponential flow of the complementary nilpotent generator. -/
@[rep_depth transport]
noncomputable def nilpotentFlow (t : ℝ) : EndH :=
  NormedSpace.exp (CIK.nilpotentGenerator t)

@[rep_depth transport, simp] theorem ambientGenerator_eq_coreGenerator_add_nilpotentGenerator
    (t : ℝ) :
    CIK.ambientGenerator t = CIK.coreGenerator t + CIK.nilpotentGenerator t := by
  unfold CertifiedInverseKernel.ambientGenerator
  unfold CertifiedInverseKernel.coreGenerator CertifiedInverseKernel.nilpotentGenerator
  rw [CIK.A_eq_corePart_add_nilpotentPart, smul_add]

@[rep_depth transport] theorem coreGenerator_commute_nilpotentGenerator
    (t : ℝ) :
    Commute (CIK.coreGenerator t) (CIK.nilpotentGenerator t) := by
  unfold CertifiedInverseKernel.coreGenerator CertifiedInverseKernel.nilpotentGenerator
  unfold Commute
  calc
    (t • CIK.corePart) * (t • CIK.nilpotentPart)
        = (t * t) • (CIK.corePart * CIK.nilpotentPart) := by
            simp [smul_smul, mul_assoc]
    _ = (t * t) • (CIK.nilpotentPart * CIK.corePart) := by
          rw [CIK.corePart_commute_nilpotentPart.eq]
    _ = (t • CIK.nilpotentPart) * (t • CIK.corePart) := by
          simp [smul_smul, mul_assoc]

@[rep_depth transport] theorem coreFlow_commute_nilpotentFlow
    (t : ℝ) :
    Commute (CIK.coreFlow t) (CIK.nilpotentFlow t) := by
  unfold CertifiedInverseKernel.coreFlow CertifiedInverseKernel.nilpotentFlow
  exact (CIK.coreGenerator_commute_nilpotentGenerator t).exp

@[rep_depth transport, simp] theorem ambientFlow_eq_coreFlow_mul_nilpotentFlow
    (t : ℝ) :
    CIK.ambientFlow t = CIK.coreFlow t * CIK.nilpotentFlow t := by
  unfold CertifiedInverseKernel.ambientFlow
  rw [CIK.ambientGenerator_eq_coreGenerator_add_nilpotentGenerator]
  exact NormedSpace.exp_add_of_commute (CIK.coreGenerator_commute_nilpotentGenerator t)

@[rep_depth transport, simp] theorem ambientFlow_eq_nilpotentFlow_mul_coreFlow
    (t : ℝ) :
    CIK.ambientFlow t = CIK.nilpotentFlow t * CIK.coreFlow t := by
  unfold CertifiedInverseKernel.ambientFlow
  rw [CIK.ambientGenerator_eq_coreGenerator_add_nilpotentGenerator, add_comm]
  exact NormedSpace.exp_add_of_commute (CIK.coreGenerator_commute_nilpotentGenerator t).symm

end CertifiedInverseKernel

end InfoGeometry.Canonical
