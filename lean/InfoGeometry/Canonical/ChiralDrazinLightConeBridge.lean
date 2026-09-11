import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ChiralDrazinLightConeBridge

Drazin/Moore--Penrose readback of the split `Cl(1,1)` chiral light-cone
channels.

The owner facts remain in:

* `CertifiedInverseKernel` / `InverseKernelCartanCore` for `P_D`, `P₀`, `Γ_S`;
* `KKTCore` / `Cl11PolarizedBasis` for `u⁺`, `u⁻`;
* `ChiralOperatorConeClosure` for chiral-cone membership and compact closure;
* `DrazinSupercharge` for `Q = χ_R - χ_L`.

This file proves only the missing direct Peirce identities connecting those
surfaces.
-/

namespace InfoGeometry.Canonical.ChiralDrazinLightConeBridge

open InfoGeometry.Canonical

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
If the split `Cl(1,1)` grading is the certified spectral grading, then its
`+1` projector is the Drazin spectral projector.
-/
@[rep_depth krein]
theorem plusProjector_eq_spectralProjector_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    KKTCore.plusProjector X = CIK.spectralProjector := by
  rw [KKTCore.plusProjector, hΓ, CIK.GammaS_eq_two_mul_spectralProjector_sub_one]
  calc
    (⅟ (2 : ℝ)) •
        ((ContinuousLinearMap.id ℝ E) + (2 * CIK.spectralProjector - 1))
        = (⅟ (2 : ℝ)) • (2 • CIK.spectralProjector) := by
            ext x
            simp
            module
    _ = CIK.spectralProjector := by
          ext x
          simp
          module

/--
If the split `Cl(1,1)` grading is the certified spectral grading, then its
`-1` projector is the Drazin complementary/defect projector.
-/
@[rep_depth krein]
theorem minusProjector_eq_spectralComplementaryProjector_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    KKTCore.minusProjector X = CIK.spectralComplementaryProjector := by
  rw [KKTCore.minusProjector, hΓ, CIK.GammaS_eq_two_mul_spectralProjector_sub_one]
  unfold CertifiedInverseKernel.spectralComplementaryProjector
  unfold CertifiedInverseKernel.toInverseKernel'
  unfold InverseKernel.spectralComplementaryProjector
  calc
    (⅟ (2 : ℝ)) •
        ((ContinuousLinearMap.id ℝ E) - (2 * CIK.spectralProjector - 1))
        = (1 : EndH) - CIK.spectralProjector := by
            ext x
            simp
            module
    _ = 1 - CIK.spectralProjector := by rfl

/-- `u⁺(A)` is the Drazin regular-from-defect Peirce block. -/
@[rep_depth krein]
theorem uPlus_eq_spectralProjector_mul_A_mul_spectralComplementaryProjector
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A : EndH)
    (hΓ : X.eps = CIK.GammaS) :
    Cl11PolarizedBasis.uPlus X A =
      CIK.spectralProjector * A * CIK.spectralComplementaryProjector := by
  rw [Cl11PolarizedBasis.uPlus, KKTCore.gOnePart]
  rw [plusProjector_eq_spectralProjector_of_eps_eq_GammaS (CIK := CIK) (X := X) hΓ]
  rw [minusProjector_eq_spectralComplementaryProjector_of_eps_eq_GammaS
    (CIK := CIK) (X := X) hΓ]

/-- `u⁻(A)` is the Drazin defect-from-regular Peirce block. -/
@[rep_depth krein]
theorem uMinus_eq_spectralComplementaryProjector_mul_A_mul_spectralProjector
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A : EndH)
    (hΓ : X.eps = CIK.GammaS) :
    Cl11PolarizedBasis.uMinus X A =
      CIK.spectralComplementaryProjector * A * CIK.spectralProjector := by
  rw [Cl11PolarizedBasis.uMinus, KKTCore.gNegOnePart]
  rw [plusProjector_eq_spectralProjector_of_eps_eq_GammaS (CIK := CIK) (X := X) hΓ]
  rw [minusProjector_eq_spectralComplementaryProjector_of_eps_eq_GammaS
    (CIK := CIK) (X := X) hΓ]

/--
Peirce form of the Drazin commutator:
`[P_D,A] = u⁺(A) - u⁻(A)`.
-/
@[rep_depth krein]
theorem commutator_spectralProjector_eq_uPlus_sub_uMinus
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A : EndH)
    (hΓ : X.eps = CIK.GammaS) :
    DrazinSupercharge.commutator CIK.spectralProjector A =
      Cl11PolarizedBasis.uPlus X A - Cl11PolarizedBasis.uMinus X A := by
  rw [uPlus_eq_spectralProjector_mul_A_mul_spectralComplementaryProjector
    (CIK := CIK) (X := X) (A := A) hΓ]
  rw [uMinus_eq_spectralComplementaryProjector_mul_A_mul_spectralProjector
    (CIK := CIK) (X := X) (A := A) hΓ]
  unfold DrazinSupercharge.commutator
  unfold CertifiedInverseKernel.spectralComplementaryProjector
  unfold CertifiedInverseKernel.toInverseKernel'
  unfold InverseKernel.spectralComplementaryProjector
  noncomm_ring [CIK.spectralProjector_idempotent]

/-- Left Moore--Penrose anomaly as Drazin light-cone off-diagonal mismatch. -/
@[rep_depth krein]
theorem chiralAnomaly_eq_uPlus_metricProjector_sub_uMinus_metricProjector
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    CIK.chiralAnomaly =
      Cl11PolarizedBasis.uPlus X CIK.metricProjector -
        Cl11PolarizedBasis.uMinus X CIK.metricProjector := by
  simpa [DrazinSupercharge.commutator, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.chiralAnomaly] using
    commutator_spectralProjector_eq_uPlus_sub_uMinus
      (CIK := CIK) (X := X) (A := CIK.metricProjector) hΓ

/-- Right Moore--Penrose anomaly as Drazin light-cone off-diagonal mismatch. -/
@[rep_depth krein]
theorem rightChiralAnomaly_eq_uPlus_mpRangeProjector_sub_uMinus_mpRangeProjector
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    CIK.rightChiralAnomaly =
      Cl11PolarizedBasis.uPlus X CIK.mpRangeProjector -
        Cl11PolarizedBasis.uMinus X CIK.mpRangeProjector := by
  simpa [DrazinSupercharge.commutator, CertifiedInverseKernel.rightChiralAnomaly,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.rightChiralAnomaly] using
    commutator_spectralProjector_eq_uPlus_sub_uMinus
      (CIK := CIK) (X := X) (A := CIK.mpRangeProjector) hΓ

/-- Supercharge as the net Moore--Penrose light-cone mismatch current. -/
@[rep_depth krein]
theorem supercharge_eq_net_lightcone_mismatch
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK =
      (Cl11PolarizedBasis.uPlus X CIK.mpRangeProjector -
          Cl11PolarizedBasis.uMinus X CIK.mpRangeProjector)
        -
        (Cl11PolarizedBasis.uPlus X CIK.metricProjector -
          Cl11PolarizedBasis.uMinus X CIK.metricProjector) := by
  unfold DrazinSupercharge.CertifiedInverseKernel.supercharge
  rw [rightChiralAnomaly_eq_uPlus_mpRangeProjector_sub_uMinus_mpRangeProjector
    (CIK := CIK) (X := X) hΓ]
  rw [chiralAnomaly_eq_uPlus_metricProjector_sub_uMinus_metricProjector
    (CIK := CIK) (X := X) hΓ]

/-- Supercharge as the light-cone off-diagonal part of the geometric grading. -/
@[rep_depth krein]
theorem supercharge_eq_uPlus_GammaG_sub_uMinus_GammaG
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK =
      Cl11PolarizedBasis.uPlus X CIK.GammaG -
        Cl11PolarizedBasis.uMinus X CIK.GammaG := by
  calc
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        = DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG := by
            exact
              DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_GammaG
                (CIK := CIK)
    _ = Cl11PolarizedBasis.uPlus X CIK.GammaG -
          Cl11PolarizedBasis.uMinus X CIK.GammaG := by
          exact commutator_spectralProjector_eq_uPlus_sub_uMinus
            (CIK := CIK) (X := X) (A := CIK.GammaG) hΓ

/-- Supercharge as twice the light-cone off-diagonal part of the dilation gap. -/
@[rep_depth krein]
theorem supercharge_eq_two_smul_uPlus_dilationGap_sub_two_smul_uMinus_dilationGap
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK =
      (2 : ℝ) •
        (Cl11PolarizedBasis.uPlus X CIK.dilationGap -
          Cl11PolarizedBasis.uMinus X CIK.dilationGap) := by
  calc
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        = (2 : ℝ) •
            DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap := by
            exact
              DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_two_smul_commutator_spectralProjector_dilationGap
                (CIK := CIK)
    _ = (2 : ℝ) •
          (Cl11PolarizedBasis.uPlus X CIK.dilationGap -
            Cl11PolarizedBasis.uMinus X CIK.dilationGap) := by
          rw [commutator_spectralProjector_eq_uPlus_sub_uMinus
            (CIK := CIK) (X := X) (A := CIK.dilationGap) hΓ]

/--
Owner readback: the Drazin supercharge is spectrally odd and its square is
spectrally compact/even.

The proofs are owned by `DrazinSupercharge`; this theorem only packages the
two readbacks as the local dictionary slogan `Q ∈ 𝔭` and `Q² ∈ 𝔨`.
-/
@[rep_depth krein]
theorem supercharge_odd_and_square_even
    (CIK : CertifiedInverseKernel E) :
    CIK.toInformationCartanTriple.IsSpectralNonCompact
        (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK) ∧
    CIK.toInformationCartanTriple.IsSpectralCompact
        (DrazinSupercharge.CertifiedInverseKernel.superHamiltonian CIK) := by
  constructor
  · simpa using
      DrazinSupercharge.CertifiedInverseKernel.supercharge_isSpectralNonCompact
        (CIK := CIK)
  · simpa using
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonian_isSpectralCompact
        (CIK := CIK)

end Core

end InfoGeometry.Canonical.ChiralDrazinLightConeBridge
