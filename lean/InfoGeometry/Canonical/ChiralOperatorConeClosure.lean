import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.Cl11PolarizedBasis
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace ChiralOperatorConeClosure

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

/-! ## Operator-algebra closure surface -/

/--
The associative product of two chiral-cone operators is spectrally compact.

Thus the chiral cone is not closed under multiplication as a cone; instead,
the product closes in the even/compact lane.
-/
@[rep_depth krein]
theorem mul_mem_spectralCompact_of_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    {X Y : EndH}
    (hX : IsInChiralOperatorCone CIK X)
    (hY : IsInChiralOperatorCone CIK Y) :
    CIK.IsSpectralCompact (X * Y) := by
  rw [CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS]
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := CIK)] at hX hY
  calc
    (X * Y) * CIK.GammaS = X * (Y * CIK.GammaS) := by
      simp [mul_assoc]
    _ = X * (-(CIK.GammaS * Y)) := by rw [hY]
    _ = -(X * (CIK.GammaS * Y)) := by simp
    _ = -((X * CIK.GammaS) * Y) := by simp [mul_assoc]
    _ = -((-(CIK.GammaS * X)) * Y) := by rw [hX]
    _ = CIK.GammaS * (X * Y) := by simp [mul_assoc]

/--
The anticommutator of two chiral-cone operators lands in the spectrally
compact lane.
-/
@[rep_depth krein]
theorem anticommutator_mem_spectralCompact_of_chiralOperatorCone
    (CIK : CertifiedInverseKernel E)
    {X Y : EndH}
    (hX : IsInChiralOperatorCone CIK X)
    (hY : IsInChiralOperatorCone CIK Y) :
    CIK.IsSpectralCompact (DrazinSupercharge.anticommutator X Y) := by
  have hXY : CIK.IsSpectralCompact (X * Y) :=
    mul_mem_spectralCompact_of_chiralOperatorCone (CIK := CIK) hX hY
  have hYX : CIK.IsSpectralCompact (Y * X) :=
    mul_mem_spectralCompact_of_chiralOperatorCone (CIK := CIK) hY hX
  rw [CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS] at hXY hYX ⊢
  unfold DrazinSupercharge.anticommutator
  calc
    (X * Y + Y * X) * CIK.GammaS
        = (X * Y) * CIK.GammaS + (Y * X) * CIK.GammaS := by
            simp [add_mul]
    _ = CIK.GammaS * (X * Y) + CIK.GammaS * (Y * X) := by
          rw [hXY, hYX]
    _ = CIK.GammaS * (X * Y + Y * X) := by
          simp [mul_add]

/--
The Lie commutator of two chiral-cone operators lands in the spectrally
compact lane: `[𝔭_S, 𝔭_S] ⊆ 𝔨_S`.
-/
@[rep_depth krein]
theorem spectralCommutator_chiral_chiral_mem_spectralCompact
    (CIK : CertifiedInverseKernel E)
    {X Y : EndH}
    (hX : IsInChiralOperatorCone CIK X)
    (hY : IsInChiralOperatorCone CIK Y) :
    CIK.IsSpectralCompact (CertifiedInverseKernel.spectralCommutator X Y) := by
  let T := CIK.toInformationCartanTriple
  have hX' : T.IsSpectralNonCompact X := by
    simpa [T, IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using hX
  have hY' : T.IsSpectralNonCompact Y := by
    simpa [T, IsInChiralOperatorCone,
      CertifiedInverseKernel.IsSpectralNonCompact,
      CertifiedInverseKernel.cartanTriple,
      CertifiedInverseKernel.toInformationCartanTriple] using hY
  have hComm : T.IsSpectralCompact (InformationCartanTriple.spectralCommutator X Y) :=
    InformationCartanTriple.spectralCommutator_mem_compact_of_noncompact
      T CIK.hDrazin hX' hY'
  simpa [T, CertifiedInverseKernel.spectralCommutator,
    CertifiedInverseKernel.IsSpectralCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using hComm

/-! ## Circular-polarized and projector enrollment -/

/--
If the split `Cl(1,1)` grading `eps` is the certified spectral grading `Γ_S`,
then `P+` is a spectrally compact operator.
-/
@[rep_depth krein]
theorem plusProjector_mem_spectralCompact_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    CIK.IsSpectralCompact (KKTCore.plusProjector X) := by
  rw [CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS]
  rw [← hΓ]
  rw [KKTCore.plusProjector_mul_eps, KKTCore.eps_mul_plusProjector]

/--
If the split `Cl(1,1)` grading `eps` is the certified spectral grading `Γ_S`,
then `P-` is a spectrally compact operator.
-/
@[rep_depth krein]
theorem minusProjector_mem_spectralCompact_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = CIK.GammaS) :
    CIK.IsSpectralCompact (KKTCore.minusProjector X) := by
  rw [CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS]
  rw [← hΓ]
  rw [KKTCore.minusProjector_mul_eps, KKTCore.eps_mul_minusProjector]

/--
If the split `Cl(1,1)` grading `eps` is the certified spectral grading `Γ_S`,
then the circularly polarized `u+` operator is in the chiral cone.
-/
@[rep_depth krein]
theorem uPlus_mem_chiralOperatorCone_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A : EndH)
    (hΓ : X.eps = CIK.GammaS) :
    IsInChiralOperatorCone CIK (Cl11PolarizedBasis.uPlus X A) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := CIK)]
  rw [← hΓ]
  have hOdd :=
    Cl11PolarizedBasis.eps_mul_eq_neg_mul_eps_of_isUPlus
      (X := X) (A := A)
  rw [hOdd]
  simp

/--
If the split `Cl(1,1)` grading `eps` is the certified spectral grading `Γ_S`,
then the circularly polarized `u-` operator is in the chiral cone.
-/
@[rep_depth krein]
theorem uMinus_mem_chiralOperatorCone_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A : EndH)
    (hΓ : X.eps = CIK.GammaS) :
    IsInChiralOperatorCone CIK (Cl11PolarizedBasis.uMinus X A) := by
  rw [isInChiralOperatorCone_iff_anticommute_GammaS (CIK := CIK)]
  rw [← hΓ]
  have hOdd :=
    Cl11PolarizedBasis.eps_mul_eq_neg_mul_eps_of_isUMinus
      (X := X) (A := A)
  rw [hOdd]
  simp

/--
With `eps = Γ_S`, the circularly polarized commutator `[u+, u-]` closes in
the spectrally compact lane of the chiral-cone algebra.
-/
@[rep_depth krein]
theorem spectralCommutator_uPlus_uMinus_mem_spectralCompact_of_eps_eq_GammaS
    (CIK : CertifiedInverseKernel E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : EndH)
    (hΓ : X.eps = CIK.GammaS) :
    CIK.IsSpectralCompact
      (CertifiedInverseKernel.spectralCommutator
        (Cl11PolarizedBasis.uPlus X A) (Cl11PolarizedBasis.uMinus X B)) := by
  exact spectralCommutator_chiral_chiral_mem_spectralCompact
    (CIK := CIK)
    (uPlus_mem_chiralOperatorCone_of_eps_eq_GammaS
      (CIK := CIK) (X := X) (A := A) hΓ)
    (uMinus_mem_chiralOperatorCone_of_eps_eq_GammaS
      (CIK := CIK) (X := X) (A := B) hΓ)

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

/-- The left chiral anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiralAnomaly_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E) :
    IsInChiralOperatorCone CIK CIK.chiralAnomaly := by
  simpa [IsInChiralOperatorCone,
    CertifiedInverseKernel.IsSpectralNonCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using
    CIK.chiralAnomaly_isSpectralNonCompact

/-- The right chiral anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem rightChiralAnomaly_mem_chiralOperatorCone
    (CIK : CertifiedInverseKernel E) :
    IsInChiralOperatorCone CIK CIK.rightChiralAnomaly := by
  simpa [IsInChiralOperatorCone,
    CertifiedInverseKernel.IsSpectralNonCompact,
    CertifiedInverseKernel.cartanTriple,
    CertifiedInverseKernel.toInformationCartanTriple] using
    CIK.rightChiralAnomaly_isSpectralNonCompact

/--
Anticommutator form of left-anomaly oddness with respect to `Γ_S`.

This is the closed-form `χ_L` oddness identity used by compatibility adapters.
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

This is the closed-form `χ_R` oddness identity used by compatibility adapters.
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

end Core

end ChiralOperatorConeClosure
