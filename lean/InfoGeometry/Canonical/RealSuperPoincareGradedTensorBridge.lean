/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge

/-!
# Real graded-tensor realization of the operator super-Poincaré relation

The source operator presentation stores its spinor matrices over `ℂ`. This
module transports those matrices through the existing realification with its
real complex-structure operator, then through the genuine Koszul-graded
`M₂(ℝ) ᵍ⊗ M₂(ℝ)` equivalence and onto the real doubled Krein carrier. The
result is a real operator equation. It does not claim that a spinor matrix
alone constructs a spacetime translation action or a Lorentz representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealSuperPoincareGradedTensorBridge

open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.GradedTensorWeylBridge
open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Physics.CuntzDeformedSuperPoincare
open scoped TensorProduct GradedTensorProduct

abbrev Tensor2 := InfoGeometry.Canonical.GradedTensorWeylBridge.twoMatrixGradedTensor
abbrev FourSpace := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
abbrev KreinFrame4 := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4

/-- Real matrix on the Koszul-graded tensor carrier corresponding to a
spinor operator matrix. -/
def chiralOperatorToRealGradedTensor (A : M2C) : Tensor2 :=
  twoMatrixGradedTensorMoritaEquiv.symm
    (realNestedMatrixToFin4.symm (realifyRingHom A))

/-- The corresponding real endomorphism on the two-sheeted four-dimensional
real carrier. -/
def chiralOperatorOnFourSpace (A : M2C) : Module.End ℝ FourSpace :=
  realTwoMatrixGradedTensorOnFourSpace (chiralOperatorToRealGradedTensor A)

/-- Diagonal lift of the real spinor operator to the doubled Krein carrier. -/
def chiralOperatorOnDoubledKrein (A : M2C) : Module.End ℝ KreinFrame4 :=
  doubleEnd (chiralOperatorOnFourSpace A)

/-- The operator-valued super-Poincaré equation survives realification at
the matrix level, with real scalar `2`. -/
theorem realify_superPoincare_relation (S : ChiralOperatorPresentation) :
    realifyRingHom S.antiQQbar = (2 : ℝ) • realifyRingHom S.Pspinor := by
  have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [S.super_poincare, htwo]
  exact realify_real_smul 2 S.Pspinor

/-- The super-Poincaré relation in the genuine two-factor real graded
tensor representation. -/
theorem realGradedTensor_superPoincare_relation
    (S : ChiralOperatorPresentation) :
    chiralOperatorToRealGradedTensor S.antiQQbar =
      (2 : ℝ) • chiralOperatorToRealGradedTensor S.Pspinor := by
  have h := congrArg
    (fun A : Mat4R => twoMatrixGradedTensorMoritaEquiv.symm
      (realNestedMatrixToFin4.symm A))
    (realify_superPoincare_relation S)
  simpa [chiralOperatorToRealGradedTensor, map_smul] using h

/-- The same operator equation acts on the real `FourSpace` carrier. -/
theorem fourSpace_superPoincare_relation
    (S : ChiralOperatorPresentation) :
    chiralOperatorOnFourSpace S.antiQQbar =
      (2 : ℝ) • chiralOperatorOnFourSpace S.Pspinor := by
  have h := congrArg realTwoMatrixGradedTensorOnFourSpace
    (realGradedTensor_superPoincare_relation S)
  simpa [chiralOperatorOnFourSpace, map_smul] using h

/-- The real spinor-momentum relation transported to the doubled Krein
carrier. -/
theorem doubledKrein_superPoincare_relation
    (S : ChiralOperatorPresentation) :
    chiralOperatorOnDoubledKrein S.antiQQbar =
      (2 : ℝ) • chiralOperatorOnDoubledKrein S.Pspinor := by
  have h := congrArg doubleEndAlgHom (fourSpace_superPoincare_relation S)
  simpa [chiralOperatorOnDoubledKrein, doubleEndAlgHom] using h

end InfoGeometry.Canonical.RealSuperPoincareGradedTensorBridge
