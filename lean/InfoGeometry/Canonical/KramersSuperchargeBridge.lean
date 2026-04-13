import InfoGeometry.Canonical.TimeReversalKramers
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KramersSuperchargeBridge

Bridge the real Kramers/Majorana symmetry interfaces to the projected
Drazin-supercharge lane `(χ_L, χ_R, Q_D, H_D)`.
-/

namespace InfoGeometry.Canonical.KramersSuperchargeBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.HestenesRealStructures

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Spectral grading in the projected Drazin lane. -/
@[rep_depth krein]
noncomputable abbrev GammaS (CIK : CertifiedInverseKernel H₂) : EndH :=
  CIK.toInformationCartanTriple.GammaS

/-- Left projected odd anomaly `χ_L`. -/
@[rep_depth krein]
noncomputable abbrev chiL (CIK : CertifiedInverseKernel H₂) : EndH :=
  CIK.chiralAnomaly

/-- Right projected odd anomaly `χ_R`. -/
@[rep_depth krein]
noncomputable abbrev chiR (CIK : CertifiedInverseKernel H₂) : EndH :=
  CIK.rightChiralAnomaly

/-- Net projected odd supercharge `Q_D = χ_R - χ_L`. -/
@[rep_depth krein]
noncomputable abbrev QD (CIK : CertifiedInverseKernel H₂) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.supercharge CIK

/-- Projected even generator `H_D = Q_D²`. -/
@[rep_depth krein]
noncomputable abbrev HD (CIK : CertifiedInverseKernel H₂) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.superHamiltonian CIK

/-- Owner parity law for the projected odd supercharge. -/
@[rep_depth krein]
theorem qD_is_odd (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.anticommutator (GammaS CIK) (QD CIK) = 0 := by
  simpa [GammaS, QD] using
    (DrazinSupercharge.CertifiedInverseKernel.supercharge_is_odd (CIK := CIK))

/-- Owner parity law for the projected even generator. -/
@[rep_depth krein]
theorem hD_is_even (CIK : CertifiedInverseKernel H₂) :
    (HD CIK) * (GammaS CIK) = (GammaS CIK) * (HD CIK) := by
  simpa [GammaS, HD] using
    (DrazinSupercharge.CertifiedInverseKernel.superHamiltonian_commutes_GammaS (CIK := CIK))

/--
If a Kramers symmetry commutes with `Γ_S`, then the Kramers-conjugated projected
supercharge remains odd with respect to `Γ_S`.
-/
@[rep_depth krein]
theorem kramers_conjugated_qD_is_odd_of_commute_GammaS
    (CIK : CertifiedInverseKernel H₂)
    (S : KramersSymmetry (E := E))
    (hThetaGamma : Commute S.Θ (GammaS CIK)) :
    DrazinSupercharge.anticommutator (GammaS CIK) (S.Θ * (QD CIK) * S.Θ) = 0 := by
  have hOdd0 :
      (GammaS CIK) * (QD CIK) + (QD CIK) * (GammaS CIK) = 0 := by
    simpa [DrazinSupercharge.anticommutator] using qD_is_odd (CIK := CIK)
  unfold DrazinSupercharge.anticommutator
  calc
    (GammaS CIK) * (S.Θ * QD CIK * S.Θ) + (S.Θ * QD CIK * S.Θ) * (GammaS CIK)
        = ((GammaS CIK) * S.Θ) * QD CIK * S.Θ + S.Θ * QD CIK * (S.Θ * GammaS CIK) := by
            simp [mul_assoc]
    _ = (S.Θ * GammaS CIK) * QD CIK * S.Θ + S.Θ * QD CIK * (GammaS CIK * S.Θ) := by
          rw [hThetaGamma.eq.symm, hThetaGamma.eq]
    _ = S.Θ * ((GammaS CIK) * QD CIK) * S.Θ + S.Θ * ((QD CIK) * (GammaS CIK)) * S.Θ := by
          simp [mul_assoc]
    _ = S.Θ * ((GammaS CIK) * QD CIK + (QD CIK) * GammaS CIK) * S.Θ := by
          simp [mul_add, add_mul, mul_assoc]
    _ = S.Θ * 0 * S.Θ := by rw [hOdd0]
    _ = 0 := by simp

/--
Generic fixed-point stability lemma:
if an operator commutes with the Majorana involution `C`, it preserves
the Majorana fixed sector.
-/
@[rep_depth krein]
theorem majorana_fixed_closed_of_commute
    (M : MajoranaRealStructure (E := E))
    {A : EndH}
    (hCA : Commute M.C A)
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana (A u) := by
  unfold MajoranaRealStructure.IsMajorana at hu ⊢
  calc
    M.C (A u) = (M.C * A) u := rfl
    _ = (A * M.C) u := by rw [hCA.eq]
    _ = A (M.C u) := rfl
    _ = A u := by rw [hu]

/-- Majorana compatibility with the left projected odd sector `χ_L`. -/
@[rep_depth krein]
theorem majorana_closed_chiL_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((chiL CIK) u) :=
  majorana_fixed_closed_of_commute (M := M) hCL hu

/-- Majorana compatibility with the right projected odd sector `χ_R`. -/
@[rep_depth krein]
theorem majorana_closed_chiR_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCR : Commute M.C (chiR CIK))
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((chiR CIK) u) :=
  majorana_fixed_closed_of_commute (M := M) hCR hu

/-- If `C` commutes with both anomalies, then it commutes with `Q_D = χ_R - χ_L`. -/
@[rep_depth krein]
theorem commute_C_QD_of_commute_C_chi
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK)) :
    Commute M.C (QD CIK) := by
  show M.C * (QD CIK) = (QD CIK) * M.C
  have hL : M.C * (chiL CIK) = (chiL CIK) * M.C := hCL.eq
  have hR : M.C * (chiR CIK) = (chiR CIK) * M.C := hCR.eq
  calc
    M.C * (QD CIK) = M.C * (chiR CIK - chiL CIK) := by rfl
    _ = M.C * chiR CIK - M.C * chiL CIK := by simp [mul_sub]
    _ = chiR CIK * M.C - chiL CIK * M.C := by rw [hR, hL]
    _ = (chiR CIK - chiL CIK) * M.C := by simp [sub_mul]
    _ = (QD CIK) * M.C := by rfl

/-- If `C` commutes with `Q_D`, then it commutes with `H_D = Q_D²`. -/
@[rep_depth krein]
theorem commute_C_HD_of_commute_C_QD
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCQ : Commute M.C (QD CIK)) :
    Commute M.C (HD CIK) := by
  show M.C * (HD CIK) = (HD CIK) * M.C
  have hQ : M.C * (QD CIK) = (QD CIK) * M.C := hCQ.eq
  calc
    M.C * (HD CIK) = M.C * (QD CIK * QD CIK) := by rfl
    _ = (M.C * QD CIK) * QD CIK := by simp [mul_assoc]
    _ = (QD CIK * M.C) * QD CIK := by rw [hQ]
    _ = QD CIK * (M.C * QD CIK) := by simp [mul_assoc]
    _ = QD CIK * (QD CIK * M.C) := by rw [hQ]
    _ = (QD CIK * QD CIK) * M.C := by simp [mul_assoc]
    _ = (HD CIK) * M.C := by rfl

/-- Majorana compatibility with `Q_D` derived from compatibility with `χ_L, χ_R`. -/
@[rep_depth krein]
theorem majorana_closed_QD_of_commute_chi
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((QD CIK) u) := by
  have hCQ : Commute M.C (QD CIK) :=
    commute_C_QD_of_commute_C_chi (CIK := CIK) (M := M) hCL hCR
  exact majorana_fixed_closed_of_commute (M := M) hCQ hu

/-- Majorana compatibility with `H_D` derived from compatibility with `χ_L, χ_R`. -/
@[rep_depth krein]
theorem majorana_closed_HD_of_commute_chi
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((HD CIK) u) := by
  have hCQ : Commute M.C (QD CIK) :=
    commute_C_QD_of_commute_C_chi (CIK := CIK) (M := M) hCL hCR
  have hCH : Commute M.C (HD CIK) :=
    commute_C_HD_of_commute_C_QD (CIK := CIK) (M := M) hCQ
  exact majorana_fixed_closed_of_commute (M := M) hCH hu

end Core

end InfoGeometry.Canonical.KramersSuperchargeBridge
