import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ChiralOperatorConeClosure

open InfoGeometry.Canonical
open InfoGeometry.Canonical.CartanDecomposition
open InfoGeometry.Canonical.DrazinSupercharge

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
The chiral operator cone on the certified inverse-kernel lane.

This is the spectral noncompact (`-1` Cartan eigensector), i.e. operators
anticommuting with the spectral grading `Γ_S`.
-/
@[rep_depth krein]
def IsInChiralOperatorCone (CIK : CertifiedInverseKernel E) (X : EndH) : Prop :=
  CIK.IsSpectralNonCompact X

/-- Set-level carrier of the chiral operator cone. -/
@[rep_depth krein]
def ChiralOperatorCone (CIK : CertifiedInverseKernel E) : Set EndH :=
  {X | IsInChiralOperatorCone CIK X}

@[rep_depth krein]
theorem mem_chiralOperatorCone_iff
    (CIK : CertifiedInverseKernel E) {X : EndH} :
    X ∈ ChiralOperatorCone CIK ↔ IsInChiralOperatorCone CIK X :=
  Iff.rfl

/-- Anticommutator characterization of chiral-cone membership. -/
@[rep_depth krein]
theorem isInChiralOperatorCone_iff_anticommute_GammaS
    (CIK : CertifiedInverseKernel E) {X : EndH} :
    IsInChiralOperatorCone CIK X ↔ X * CIK.GammaS = -(CIK.GammaS * X) := by
  simpa [IsInChiralOperatorCone] using
    (CIK.isSpectralNonCompact_iff_anticommute_GammaS (X := X))

/-- Zero lies in the chiral operator cone. -/
@[rep_depth krein]
theorem zero_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E) :
    IsInChiralOperatorCone CIK (0 : EndH) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := CIK)]
  simp

/-- The chiral operator cone is closed under addition. -/
@[rep_depth krein]
theorem add_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    {X Y : EndH}
    (hX : IsInChiralOperatorCone CIK X)
    (hY : IsInChiralOperatorCone CIK Y) :
    IsInChiralOperatorCone CIK (X + Y) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := CIK)] at hX hY ⊢
  calc
    (X + Y) * CIK.GammaS = X * CIK.GammaS + Y * CIK.GammaS := by
      simp [add_mul]
    _ = -(CIK.GammaS * X) + -(CIK.GammaS * Y) := by rw [hX, hY]
    _ = -((CIK.GammaS * X) + (CIK.GammaS * Y)) := by
      abel_nf
    _ = -(CIK.GammaS * (X + Y)) := by
      simp [mul_add]

/-- The chiral operator cone is closed under real scaling. -/
@[rep_depth krein]
theorem smul_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    (a : ℝ)
    {X : EndH}
    (hX : IsInChiralOperatorCone CIK X) :
    IsInChiralOperatorCone CIK (a • X) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := CIK)] at hX ⊢
  calc
    (a • X) * CIK.GammaS = a • (X * CIK.GammaS) := by
      simp
    _ = a • (-(CIK.GammaS * X)) := by rw [hX]
    _ = -(a • (CIK.GammaS * X)) := by simp
    _ = -(CIK.GammaS * (a • X)) := by
      simp

/-- Cone-form closure: nonnegative scaling preserves the chiral cone. -/
@[rep_depth krein]
theorem nonneg_smul_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    {a : ℝ}
    (_ha : 0 ≤ a)
    {X : EndH}
    (hX : IsInChiralOperatorCone CIK X) :
    IsInChiralOperatorCone CIK (a • X) :=
  smul_mem_chiralOperatorCone (CIK := CIK) a hX

/-- The chiral cone is stable under spectral-adjoint transport by compact generators. -/
@[rep_depth krein]
theorem spectralAdjointFlow_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    {X Y : EndH}
    (hX : CIK.IsSpectralCompact X)
    (hY : IsInChiralOperatorCone CIK Y)
    (t : ℝ) :
    IsInChiralOperatorCone CIK (CIK.spectralAdjointFlow X t Y) := by
  let T := CIK.toInformationCartanTriple
  have hX' : T.IsSpectralCompact X := by
    simpa [T, CertifiedInverseKernel.IsSpectralCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using hX
  have hY' : T.IsSpectralNonCompact Y := by
    simpa [T, IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using hY
  have hFlow : T.IsSpectralNonCompact (T.spectralAdjointFlow X t Y) :=
    InformationCartanTriple.spectralAdjointFlow_mem_noncompact
      T CIK.hDrazin (X := X) (Y := Y) hX' hY' t
  simpa [T, IsInChiralOperatorCone,
    CertifiedInverseKernel.spectralAdjointFlow,
    CertifiedInverseKernel.IsSpectralNonCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using hFlow

/-- The commutator of a compact operator with a chiral operator stays chiral. -/
@[rep_depth krein]
theorem spectralCommutator_compact_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    {X Y : EndH}
    (hX : CIK.IsSpectralCompact X)
    (hY : IsInChiralOperatorCone CIK Y) :
    IsInChiralOperatorCone CIK (CertifiedInverseKernel.spectralCommutator X Y) := by
  let T := CIK.toInformationCartanTriple
  have hX' : T.IsSpectralCompact X := by
    simpa [T, CertifiedInverseKernel.IsSpectralCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using hX
  have hY' : T.IsSpectralNonCompact Y := by
    simpa [T, IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using hY
  have hComm : T.IsSpectralNonCompact (InformationCartanTriple.spectralCommutator X Y) :=
    InformationCartanTriple.spectralCommutator_compact_noncompact
      T CIK.hDrazin hX' hY'
  simpa [T, IsInChiralOperatorCone,
    CertifiedInverseKernel.spectralCommutator,
    CertifiedInverseKernel.IsSpectralNonCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using hComm

/-- The projected Drazin supercharge is a canonical element of the chiral cone. -/
@[rep_depth krein]
theorem supercharge_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E) :
    IsInChiralOperatorCone CIK (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK) := by
  simpa [IsInChiralOperatorCone,
    CertifiedInverseKernel.IsSpectralNonCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using
    (DrazinSupercharge.CertifiedInverseKernel.supercharge_isSpectralNonCompact (CIK := CIK))

/--
Anticommutator form of left-anomaly oddness with respect to `Γ_S`.

This is the closed-form `χ_L` oddness witness used by compatibility adapters.
-/
@[rep_depth krein]
theorem anticommutator_GammaS_chiralAnomaly_eq_zero
    (CIK : CertifiedInverseKernel E) :
    DrazinSupercharge.anticommutator CIK.GammaS CIK.chiralAnomaly = 0 := by
  have hAnti :
      CIK.chiralAnomaly * CIK.GammaS = -(CIK.GammaS * CIK.chiralAnomaly) := by
    simpa [CertifiedInverseKernel.GammaS, CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using
      CIK.chiralAnomaly_anticommutes_GammaS
  unfold DrazinSupercharge.anticommutator
  calc
    CIK.GammaS * CIK.chiralAnomaly + CIK.chiralAnomaly * CIK.GammaS
        = CIK.GammaS * CIK.chiralAnomaly + -(CIK.GammaS * CIK.chiralAnomaly) := by
            rw [hAnti]
    _ = 0 := by simp

/--
Anticommutator form of right-anomaly oddness with respect to `Γ_S`.

This is the closed-form `χ_R` oddness witness used by compatibility adapters.
-/
@[rep_depth krein]
theorem anticommutator_GammaS_rightChiralAnomaly_eq_zero
    (CIK : CertifiedInverseKernel E) :
    DrazinSupercharge.anticommutator CIK.GammaS CIK.rightChiralAnomaly = 0 := by
  have hAnti :
      CIK.rightChiralAnomaly * CIK.GammaS = -(CIK.GammaS * CIK.rightChiralAnomaly) := by
    simpa [CertifiedInverseKernel.GammaS, CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using
      CIK.rightChiralAnomaly_anticommutes_GammaS
  unfold DrazinSupercharge.anticommutator
  calc
    CIK.GammaS * CIK.rightChiralAnomaly + CIK.rightChiralAnomaly * CIK.GammaS
        = CIK.GammaS * CIK.rightChiralAnomaly + -(CIK.GammaS * CIK.rightChiralAnomaly) := by
            rw [hAnti]
    _ = 0 := by simp

/--
Reified owner for the spectral Cartan chiral cone algebra on the certified
Drazin lane.

This packages theorem-by-theorem closure and commutator/anticommutator facts
already proved from `CertifiedInverseKernel`.
-/
@[rep_depth krein]
structure SpectralChiralConeAlgebra (CIK : CertifiedInverseKernel E) where
  commutator_P_D_GammaG_eq_sub_anomalies :
    DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG
      = CIK.rightChiralAnomaly - CIK.chiralAnomaly
  commutator_P_D_dilationGap_eq_half_sub_anomalies :
    DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap
      = ((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly)
  anticommutator_GammaS_chiL_eq_zero :
    DrazinSupercharge.anticommutator CIK.GammaS CIK.chiralAnomaly = 0
  anticommutator_GammaS_chiR_eq_zero :
    DrazinSupercharge.anticommutator CIK.GammaS CIK.rightChiralAnomaly = 0
  chiL_mem_chiralCone :
    IsInChiralOperatorCone CIK CIK.chiralAnomaly
  chiR_mem_chiralCone :
    IsInChiralOperatorCone CIK CIK.rightChiralAnomaly
  supercharge_eq_commutator_P_D_GammaG :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      = DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG
  supercharge_mem_chiralCone :
    IsInChiralOperatorCone CIK (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
  compact_commutator_closed :
    ∀ {X Y : EndH},
      CIK.IsSpectralCompact X →
      IsInChiralOperatorCone CIK Y →
      IsInChiralOperatorCone CIK (CertifiedInverseKernel.spectralCommutator X Y)

/--
Canonical constructor for the spectral chiral cone algebra from the certified
inverse-kernel owner.
-/
@[rep_depth krein]
def SpectralChiralConeAlgebra.ofCertifiedInverseKernel
    (CIK : CertifiedInverseKernel E) :
    SpectralChiralConeAlgebra CIK where
  commutator_P_D_GammaG_eq_sub_anomalies := by
    simpa [DrazinSupercharge.commutator] using
      CIK.spectralProjector_commutator_GammaG_eq_sub_anomalies
  commutator_P_D_dilationGap_eq_half_sub_anomalies := by
    simpa [DrazinSupercharge.commutator] using
      CIK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies
  anticommutator_GammaS_chiL_eq_zero :=
    anticommutator_GammaS_chiralAnomaly_eq_zero (CIK := CIK)
  anticommutator_GammaS_chiR_eq_zero :=
    anticommutator_GammaS_rightChiralAnomaly_eq_zero (CIK := CIK)
  chiL_mem_chiralCone := by
    simpa [IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using
      CIK.chiralAnomaly_isSpectralNonCompact
  chiR_mem_chiralCone := by
    simpa [IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using
      CIK.rightChiralAnomaly_isSpectralNonCompact
  supercharge_eq_commutator_P_D_GammaG := by
    simpa using
      (DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_GammaG
        (CIK := CIK))
  supercharge_mem_chiralCone :=
    supercharge_mem_chiralOperatorCone (CIK := CIK)
  compact_commutator_closed := by
    intro X Y hX hY
    exact spectralCommutator_compact_mem_chiralOperatorCone (CIK := CIK) hX hY

/--
Deprecated compatibility alias kept during migration to the reified owner
`SpectralChiralConeAlgebra`.
-/
abbrev ChiralConeCompatibilityData (CIK : CertifiedInverseKernel E) :=
  SpectralChiralConeAlgebra CIK

/-- Deprecated constructor alias for compatibility with existing adapters. -/
def chiralConeCompatibilityData
    (CIK : CertifiedInverseKernel E) :
    ChiralConeCompatibilityData CIK :=
  SpectralChiralConeAlgebra.ofCertifiedInverseKernel (CIK := CIK)

end Core

end InfoGeometry.Canonical.ChiralOperatorConeClosure
