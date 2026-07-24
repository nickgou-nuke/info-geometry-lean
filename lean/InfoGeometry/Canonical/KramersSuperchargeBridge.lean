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
open InfoGeometry.Canonical.OperatorDictionary

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

/-- Canonical defect-central extraction from `Q_D²`. -/
@[rep_depth krein]
noncomputable abbrev ZD (CIK : CertifiedInverseKernel H₂) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral CIK

/-- Canonical kinetic remainder from `Q_D² = H + Z`. -/
@[rep_depth krein]
noncomputable abbrev HK (CIK : CertifiedInverseKernel H₂) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart CIK

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

/-- Owner split identity for the projected lane: `Q_D² = H_K + Z_D`. -/
@[rep_depth krein]
theorem hD_eq_hK_add_zD (CIK : CertifiedInverseKernel H₂) :
    HD CIK = HK CIK + ZD CIK := by
  simpa [HD, HK, ZD] using
    (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral
      (CIK := CIK))

/--
Carrier bridge law between abstract Kramers symmetry `Θ` and intrinsic phase
partner map `phasePartner`:
`Θ (K u) = -(K (Θ u))`.
-/
@[rep_depth krein]
theorem theta_phasePartner_eq_neg_phasePartner_theta
    (S : KramersSymmetry (E := E))
    (u : H₂) :
    S.Θ (InfoGeometry.Canonical.HestenesKramersBridge.phasePartner (E := E) u)
      =
    -(InfoGeometry.Canonical.HestenesKramersBridge.phasePartner (E := E) (S.Θ u)) := by
  have hApply := congrArg (fun F : EndH => F u) S.anticomm_phaseAxisK
  simpa [InfoGeometry.Canonical.HestenesKramersBridge.phasePartner, phaseAxisK] using hApply

/--
Pair-level bridge:
the Kramers pair of a phase partner equals the phase-rotated pair with the
second component flipped by the anticommutation sign.
-/
@[rep_depth krein]
theorem kramersPair_phasePartner_bridge
    (S : KramersSymmetry (E := E))
    (u : H₂) :
    S.pair (InfoGeometry.Canonical.HestenesKramersBridge.phasePartner (E := E) u)
      =
    (InfoGeometry.Canonical.HestenesKramersBridge.phasePartner (E := E) u,
      -(InfoGeometry.Canonical.HestenesKramersBridge.phasePartner (E := E) (S.Θ u))) := by
  refine Prod.ext ?_ ?_
  · rfl
  · simpa [KramersSymmetry.pair] using
      (theta_phasePartner_eq_neg_phasePartner_theta (S := S) (u := u))

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

/--
If `C` commutes with both anomalies and with the defect projector `Q₀`,
then it commutes with the canonical defect-central operator `Z_D`.
-/
@[rep_depth krein]
theorem commute_C_ZD_of_commute_chi_and_Q0
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    (hCQ0 : Commute M.C CIK.spectralComplementaryProjector) :
    Commute M.C (ZD CIK) := by
  have hCQ : Commute M.C (QD CIK) :=
    commute_C_QD_of_commute_C_chi (CIK := CIK) (M := M) hCL hCR
  have hCHD : Commute M.C (HD CIK) :=
    commute_C_HD_of_commute_C_QD (CIK := CIK) (M := M) hCQ
  have hQ0 : M.C * CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector * M.C := hCQ0.eq
  have hH : M.C * HD CIK = HD CIK * M.C := hCHD.eq
  show M.C * ZD CIK = ZD CIK * M.C
  unfold ZD DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral
  calc
    M.C * (CIK.spectralComplementaryProjector * HD CIK * CIK.spectralComplementaryProjector)
        = ((M.C * CIK.spectralComplementaryProjector) * HD CIK)
            * CIK.spectralComplementaryProjector := by
              simp [mul_assoc]
    _ = ((CIK.spectralComplementaryProjector * M.C) * HD CIK)
          * CIK.spectralComplementaryProjector := by rw [hQ0]
    _ = (CIK.spectralComplementaryProjector * (M.C * HD CIK))
          * CIK.spectralComplementaryProjector := by
            simp [mul_assoc]
    _ = (CIK.spectralComplementaryProjector * (HD CIK * M.C))
          * CIK.spectralComplementaryProjector := by rw [hH]
    _ = (CIK.spectralComplementaryProjector * HD CIK)
          * (M.C * CIK.spectralComplementaryProjector) := by
            simp [mul_assoc]
    _ = (CIK.spectralComplementaryProjector * HD CIK)
          * (CIK.spectralComplementaryProjector * M.C) := by rw [hQ0]
    _ = (CIK.spectralComplementaryProjector * HD CIK * CIK.spectralComplementaryProjector)
          * M.C := by
            simp [mul_assoc]

/--
If `C` commutes with both anomalies and with the defect projector `Q₀`,
then it commutes with the canonical kinetic remainder `H_K`.
-/
@[rep_depth krein]
theorem commute_C_HK_of_commute_chi_and_Q0
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    (hCQ0 : Commute M.C CIK.spectralComplementaryProjector) :
    Commute M.C (HK CIK) := by
  have hCQ : Commute M.C (QD CIK) :=
    commute_C_QD_of_commute_C_chi (CIK := CIK) (M := M) hCL hCR
  have hCHD : Commute M.C (HD CIK) :=
    commute_C_HD_of_commute_C_QD (CIK := CIK) (M := M) hCQ
  have hCZD : Commute M.C (ZD CIK) :=
    commute_C_ZD_of_commute_chi_and_Q0
      (CIK := CIK) (M := M) hCL hCR hCQ0
  show M.C * HK CIK = HK CIK * M.C
  unfold HK DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart
  calc
    M.C * (HD CIK - ZD CIK)
        = M.C * HD CIK - M.C * ZD CIK := by simp [mul_sub]
    _ = HD CIK * M.C - ZD CIK * M.C := by rw [hCHD.eq, hCZD.eq]
    _ = (HD CIK - ZD CIK) * M.C := by simp [sub_mul]

/-- Majorana compatibility with the canonical defect-central channel `Z_D`. -/
@[rep_depth krein]
theorem majorana_closed_ZD_of_commute_chi_and_Q0
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    (hCQ0 : Commute M.C CIK.spectralComplementaryProjector)
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((ZD CIK) u) := by
  have hCZ : Commute M.C (ZD CIK) :=
    commute_C_ZD_of_commute_chi_and_Q0
      (CIK := CIK) (M := M) hCL hCR hCQ0
  exact majorana_fixed_closed_of_commute (M := M) hCZ hu

/-- Majorana compatibility with the canonical kinetic channel `H_K`. -/
@[rep_depth krein]
theorem majorana_closed_HK_of_commute_chi_and_Q0
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    (hCQ0 : Commute M.C CIK.spectralComplementaryProjector)
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((HK CIK) u) := by
  have hCH : Commute M.C (HK CIK) :=
    commute_C_HK_of_commute_chi_and_Q0
      (CIK := CIK) (M := M) hCL hCR hCQ0
  exact majorana_fixed_closed_of_commute (M := M) hCH hu

/--
Majorana-compatible closure of the canonical internal split channels
under anomaly compatibility and defect-projector compatibility.
-/
@[rep_depth krein]
theorem majorana_closed_HK_and_ZD_of_commute_chi_and_Q0
    (CIK : CertifiedInverseKernel H₂)
    (M : MajoranaRealStructure (E := E))
    (hCL : Commute M.C (chiL CIK))
    (hCR : Commute M.C (chiR CIK))
    (hCQ0 : Commute M.C CIK.spectralComplementaryProjector)
    {u : H₂}
    (hu : M.IsMajorana u) :
    M.IsMajorana ((HK CIK) u) ∧ M.IsMajorana ((ZD CIK) u) := by
  constructor
  · exact majorana_closed_HK_of_commute_chi_and_Q0
      (CIK := CIK) (M := M) hCL hCR hCQ0 hu
  · exact majorana_closed_ZD_of_commute_chi_and_Q0
      (CIK := CIK) (M := M) hCL hCR hCQ0 hu

end Core

end InfoGeometry.Canonical.KramersSuperchargeBridge
