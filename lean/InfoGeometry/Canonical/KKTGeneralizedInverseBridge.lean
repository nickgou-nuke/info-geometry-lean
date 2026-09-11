import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.EPDefectAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KKTGeneralizedInverseBridge

Generalized-inverse bridge from the split-operator KKT grading to the certified
inverse-kernel corridor.

The hypotheses are explicit and representation-specific:

- `A` lies in the grade `+1` wing,
- `A_MP` lies in the grade `-1` wing,
- optionally `A_D` also lies in the grade `-1` wing.

Under those hypotheses, the Moore-Penrose projectors, their difference, the raw
inverse commutator, the dilation gap, and the Drazin core projector all land in
grade zero.
-/

namespace InfoGeometry.Canonical.KKTGeneralizedInverseBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.KKTCore

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

@[rep_depth krein] theorem mpInverseCommutator_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (CIK : CertifiedInverseKernel E)
    (hA : IsGOne X CIK.A)
    (hAMP : IsGNegOne X CIK.A_MP) :
    IsGZero X CIK.mpInverseCommutator := by
  change IsGZero X (commutator CIK.A CIK.A_MP)
  exact commutator_isGZero_of_isGOne_of_isGNegOne (X := X) hA hAMP

@[rep_depth krein] theorem mpRightProj_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (CIK : CertifiedInverseKernel E)
    (hA : IsGOne X CIK.A)
    (hAMP : IsGNegOne X CIK.A_MP) :
    IsGZero X CIK.mpRightProj := by
  change IsGZero X (CIK.A * CIK.A_MP)
  rw [← hA, ← hAMP]
  exact gOnePart_mul_gNegOnePart_isGZero (X := X) CIK.A CIK.A_MP

@[rep_depth krein] theorem mpLeftProj_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (CIK : CertifiedInverseKernel E)
    (hA : IsGOne X CIK.A)
    (hAMP : IsGNegOne X CIK.A_MP) :
    IsGZero X CIK.mpLeftProj := by
  change IsGZero X (CIK.A_MP * CIK.A)
  rw [← hAMP, ← hA]
  exact gNegOnePart_mul_gOnePart_isGZero (X := X) CIK.A_MP CIK.A

@[rep_depth krein] theorem mpChiralGap_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (CIK : CertifiedInverseKernel E)
    (hA : IsGOne X CIK.A)
    (hAMP : IsGNegOne X CIK.A_MP) :
    IsGZero X CIK.mpChiralGap := by
  unfold CertifiedInverseKernel.mpChiralGap
  exact isGZero_sub (X := X)
    (mpRightProj_isGZero (X := X) (CIK := CIK) hA hAMP)
    (mpLeftProj_isGZero (X := X) (CIK := CIK) hA hAMP)

@[rep_depth krein] theorem dilationGap_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (CIK : CertifiedInverseKernel E)
    (hA : IsGOne X CIK.A)
    (hAMP : IsGNegOne X CIK.A_MP) :
    IsGZero X CIK.dilationGap := by
  rw [CIK.dilationGap_eq_half_smul_mpChiralGap]
  exact isGZero_smul (X := X) ((2 : ℝ)⁻¹)
    (mpChiralGap_isGZero (X := X) (CIK := CIK) hA hAMP)

@[rep_depth krein] theorem drazinCoreProj_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (CIK : CertifiedInverseKernel E)
    (hA : IsGOne X CIK.A)
    (hAD : IsGNegOne X CIK.A_D) :
    IsGZero X CIK.drazinCoreProj := by
  change IsGZero X (CIK.A * CIK.A_D)
  rw [← hA, ← hAD]
  exact gOnePart_mul_gNegOnePart_isGZero (X := X) CIK.A CIK.A_D

end Core

end InfoGeometry.Canonical.KKTGeneralizedInverseBridge
