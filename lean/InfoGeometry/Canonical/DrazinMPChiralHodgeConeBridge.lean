import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.DrazinLightConeDictionary
import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.DrazinMPChiralHodgeConeBridge

Drazin--Moore--Penrose chiral Hodge cone bridge.

This file connects three existing owner lanes:

* `CertifiedInverseKernel` supplies the Drazin/MP projectors;
* `DrazinLightConeDictionary` supplies the abstract lightcone arrows
  `u⁺(X)=PXP₀` and `u⁻(X)=P₀XP`;
* `ChiralHodgeDecomposition` owns the root doubled chiral Hodge convention.

The chiral Hodge star in this bridge is

`⋆χ = P_D - P₀`,

so `⋆χ² = 1`. This is a chirality/grading operator, not the Hestenes phase
axis `K`, which has square `-1`.
-/

namespace InfoGeometry.Canonical.DrazinMPChiralHodgeConeBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinLightConeDictionary

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/-- Drazin regular/self-dual projector. -/
@[rep_depth krein]
noncomputable def hodgeSD
    (CIK : CertifiedInverseKernel E) : EndH :=
  CIK.spectralProjector

/-- Drazin defect/anti-self-dual projector. -/
@[rep_depth krein]
noncomputable def hodgeASD
    (CIK : CertifiedInverseKernel E) : EndH :=
  CIK.spectralComplementaryProjector

/-- Chiral Hodge star / chirality grading on the Drazin split: `⋆χ = P_D - P₀`. -/
@[rep_depth krein]
noncomputable def hodgeChiralityStar
    (CIK : CertifiedInverseKernel E) : EndH :=
  CIK.spectralProjector - CIK.spectralComplementaryProjector

/-- The chiral Hodge star squares to the identity. -/
@[rep_depth krein]
theorem hodgeChiralityStar_sq_one
    (CIK : CertifiedInverseKernel E) :
    hodgeChiralityStar CIK * hodgeChiralityStar CIK = (1 : EndH) := by
  set P : EndH := CIK.spectralProjector
  set Q : EndH := CIK.spectralComplementaryProjector
  have hP : P * P = P := by
    simpa [P] using CIK.spectralProjector_idempotent
  have hQ : Q * Q = Q := by
    simpa [Q] using CIK.spectralComplementaryProjector_idempotent
  have hPQ : P * Q = 0 := by
    simpa [P, Q] using CIK.spectralProjector_mul_spectralComplementaryProjector
  have hQP : Q * P = 0 := by
    simpa [P, Q] using CIK.spectralComplementaryProjector_mul_spectralProjector
  have hAdd : P + Q = (1 : EndH) := by
    simpa [P, Q] using CIK.spectralProjector_add_spectralComplementaryProjector
  unfold hodgeChiralityStar
  change (P - Q) * (P - Q) = (1 : EndH)
  calc
    (P - Q) * (P - Q) = P + Q := by
      noncomm_ring [hP, hQ, hPQ, hQP]
    _ = (1 : EndH) := hAdd

/-- The bridge chirality agrees with the certified spectral grading. -/
@[rep_depth krein]
theorem hodgeChiralityStar_eq_GammaS
    (CIK : CertifiedInverseKernel E) :
    hodgeChiralityStar CIK = CIK.toInformationCartanTriple.GammaS := by
  unfold hodgeChiralityStar
  change
    CIK.spectralProjector - CIK.spectralComplementaryProjector =
      CIK.toInformationCartanTriple.GammaS
  change
    CIK.spectralProjector - (1 - CIK.spectralProjector) =
      2 * CIK.spectralProjector - 1
  noncomm_ring

/-- `⋆χ` acts by `+1` on the Drazin regular/self-dual sector on the left. -/
@[rep_depth krein]
theorem hodgeChiralityStar_mul_hodgeSD
    (CIK : CertifiedInverseKernel E) :
    hodgeChiralityStar CIK * hodgeSD CIK = hodgeSD CIK := by
  set P : EndH := CIK.spectralProjector
  set Q : EndH := CIK.spectralComplementaryProjector
  have hP : P * P = P := by
    simpa [P] using CIK.spectralProjector_idempotent
  have hQP : Q * P = 0 := by
    simpa [P, Q] using CIK.spectralComplementaryProjector_mul_spectralProjector
  unfold hodgeChiralityStar hodgeSD
  change (P - Q) * P = P
  noncomm_ring [hP, hQP]

/-- `⋆χ` acts by `+1` on the Drazin regular/self-dual sector on the right. -/
@[rep_depth krein]
theorem hodgeSD_mul_hodgeChiralityStar
    (CIK : CertifiedInverseKernel E) :
    hodgeSD CIK * hodgeChiralityStar CIK = hodgeSD CIK := by
  set P : EndH := CIK.spectralProjector
  set Q : EndH := CIK.spectralComplementaryProjector
  have hP : P * P = P := by
    simpa [P] using CIK.spectralProjector_idempotent
  have hPQ : P * Q = 0 := by
    simpa [P, Q] using CIK.spectralProjector_mul_spectralComplementaryProjector
  unfold hodgeChiralityStar hodgeSD
  change P * (P - Q) = P
  noncomm_ring [hP, hPQ]

/-- `⋆χ` acts by `-1` on the Drazin defect/anti-self-dual sector on the left. -/
@[rep_depth krein]
theorem hodgeChiralityStar_mul_hodgeASD
    (CIK : CertifiedInverseKernel E) :
    hodgeChiralityStar CIK * hodgeASD CIK = -hodgeASD CIK := by
  set P : EndH := CIK.spectralProjector
  set Q : EndH := CIK.spectralComplementaryProjector
  have hQ : Q * Q = Q := by
    simpa [Q] using CIK.spectralComplementaryProjector_idempotent
  have hPQ : P * Q = 0 := by
    simpa [P, Q] using CIK.spectralProjector_mul_spectralComplementaryProjector
  unfold hodgeChiralityStar hodgeASD
  change (P - Q) * Q = -Q
  noncomm_ring [hQ, hPQ]

/-- `⋆χ` acts by `-1` on the Drazin defect/anti-self-dual sector on the right. -/
@[rep_depth krein]
theorem hodgeASD_mul_hodgeChiralityStar
    (CIK : CertifiedInverseKernel E) :
    hodgeASD CIK * hodgeChiralityStar CIK = -hodgeASD CIK := by
  set P : EndH := CIK.spectralProjector
  set Q : EndH := CIK.spectralComplementaryProjector
  have hQ : Q * Q = Q := by
    simpa [Q] using CIK.spectralComplementaryProjector_idempotent
  have hQP : Q * P = 0 := by
    simpa [P, Q] using CIK.spectralComplementaryProjector_mul_spectralProjector
  unfold hodgeChiralityStar hodgeASD
  change Q * (P - Q) = -Q
  noncomm_ring [hQ, hQP]

/-- The certified left anomaly is genuinely odd for the bridge chirality. -/
@[rep_depth krein]
theorem chiralAnomaly_anticommutes_hodgeChiralityStar
    (CIK : CertifiedInverseKernel E) :
    CIK.chiralAnomaly * hodgeChiralityStar CIK =
      -(hodgeChiralityStar CIK * CIK.chiralAnomaly) := by
  rw [hodgeChiralityStar_eq_GammaS]
  exact CIK.chiralAnomaly_anticommutes_GammaS

/-- The certified right anomaly is genuinely odd for the bridge chirality. -/
@[rep_depth krein]
theorem rightChiralAnomaly_anticommutes_hodgeChiralityStar
    (CIK : CertifiedInverseKernel E) :
    CIK.rightChiralAnomaly * hodgeChiralityStar CIK =
      -(hodgeChiralityStar CIK * CIK.rightChiralAnomaly) := by
  rw [hodgeChiralityStar_eq_GammaS]
  exact CIK.rightChiralAnomaly_anticommutes_GammaS

/-- The canonical anomaly-difference Dirac is odd for the bridge chirality. -/
@[rep_depth krein]
theorem canonicalDirac_anticommutes_hodgeChiralityStar
    (CIK : CertifiedInverseKernel E) :
    (CIK.rightChiralAnomaly - CIK.chiralAnomaly) * hodgeChiralityStar CIK =
      -(hodgeChiralityStar CIK * (CIK.rightChiralAnomaly - CIK.chiralAnomaly)) := by
  have hR := rightChiralAnomaly_anticommutes_hodgeChiralityStar (CIK := CIK)
  have hL := chiralAnomaly_anticommutes_hodgeChiralityStar (CIK := CIK)
  calc
    (CIK.rightChiralAnomaly - CIK.chiralAnomaly) * hodgeChiralityStar CIK
        = CIK.rightChiralAnomaly * hodgeChiralityStar CIK -
            CIK.chiralAnomaly * hodgeChiralityStar CIK := by
              rw [sub_mul]
    _ = -(hodgeChiralityStar CIK * CIK.rightChiralAnomaly) -
        -(hodgeChiralityStar CIK * CIK.chiralAnomaly) := by
          rw [hR, hL]
    _ = -(hodgeChiralityStar CIK * (CIK.rightChiralAnomaly - CIK.chiralAnomaly)) := by
          noncomm_ring

/--
Bridge between certified Drazin/MP projectors, the lightcone projector algebra,
chiral Hodge star/chirality, and a supplied odd Dirac/supercharge candidate.

The oddness field is a calibration, not a theorem of arbitrary `Dirac`.
-/
@[rep_depth krein]
structure DrazinMPChiralHodgeConeBridge where
  /-- Certified Drazin/Moore--Penrose owner lane. -/
  CIK : CertifiedInverseKernel E

  /-- Dirac/supercharge candidate on the same carrier. -/
  Dirac : EndH

  /-- Dirac is odd for the Drazin chiral Hodge star. -/
  Dirac_odd :
    Dirac * hodgeChiralityStar CIK =
      -(hodgeChiralityStar CIK * Dirac)

/-- The canonical bridge using the repo-owned anomaly-difference Dirac. -/
@[rep_depth krein]
noncomputable def canonicalBridge
    (CIK : CertifiedInverseKernel E) : DrazinMPChiralHodgeConeBridge (E := E) where
  CIK := CIK
  Dirac := CIK.rightChiralAnomaly - CIK.chiralAnomaly
  Dirac_odd := canonicalDirac_anticommutes_hodgeChiralityStar (CIK := CIK)

/-- The canonical Drazin/Moore--Penrose chiral Hodge bridge exists. -/
@[rep_depth krein]
theorem canonicalBridge_exists
    (CIK : CertifiedInverseKernel E) :
    Nonempty (DrazinMPChiralHodgeConeBridge (E := E)) := by
  exact ⟨canonicalBridge (CIK := CIK)⟩

namespace DrazinMPChiralHodgeConeBridge

variable (B : DrazinMPChiralHodgeConeBridge (E := E))

/-- The Drazin regular/defect split as a generic projector split. -/
@[rep_depth krein]
noncomputable def drazinSplit : ProjectorSplit EndH where
  P := B.CIK.spectralProjector
  P0 := B.CIK.spectralComplementaryProjector
  P_idem := B.CIK.spectralProjector_idempotent
  P0_idem := B.CIK.spectralComplementaryProjector_idempotent
  P_add_P0 := B.CIK.spectralProjector_add_spectralComplementaryProjector
  P_mul_P0 := B.CIK.spectralProjector_mul_spectralComplementaryProjector
  P0_mul_P := B.CIK.spectralComplementaryProjector_mul_spectralProjector

/-- Chiral Dirac arrow `D⁺ = P_ASD D P_SD = P₀ D P_D`. -/
@[rep_depth krein]
noncomputable def diracPlus : EndH :=
  hodgeASD B.CIK * B.Dirac * hodgeSD B.CIK

/-- Chiral Dirac arrow `D⁻ = P_SD D P_ASD = P_D D P₀`. -/
@[rep_depth krein]
noncomputable def diracMinus : EndH :=
  hodgeSD B.CIK * B.Dirac * hodgeASD B.CIK

/-- Chiral positive-sector Hodge loop `Δ_SD = D⁻D⁺`. -/
@[rep_depth krein]
noncomputable def hodgeLaplacianSD : EndH :=
  B.diracMinus * B.diracPlus

/-- Chiral defect-sector Hodge loop `Δ_ASD = D⁺D⁻`. -/
@[rep_depth krein]
noncomputable def hodgeLaplacianASD : EndH :=
  B.diracPlus * B.diracMinus

/-- The `SD → ASD` chiral Dirac arrow is the Drazin `u⁻` arrow. -/
@[rep_depth krein]
theorem diracPlus_eq_uMinus :
    B.diracPlus = (B.drazinSplit).uMinus B.Dirac := by
  unfold diracPlus hodgeSD hodgeASD drazinSplit
  rfl

/-- The `ASD → SD` chiral Dirac arrow is the Drazin `u⁺` arrow. -/
@[rep_depth krein]
theorem diracMinus_eq_uPlus :
    B.diracMinus = (B.drazinSplit).uPlus B.Dirac := by
  unfold diracMinus hodgeSD hodgeASD drazinSplit
  rfl

/-- Same-direction nilpotence of the `D⁺ = u⁻(D)` channel. -/
@[rep_depth krein]
theorem diracPlus_mul_diracPlus_eq_zero :
    B.diracPlus * B.diracPlus = 0 := by
  rw [B.diracPlus_eq_uMinus]
  exact (B.drazinSplit).uMinus_mul_uMinus_eq_zero B.Dirac B.Dirac

/-- Same-direction nilpotence of the `D⁻ = u⁺(D)` channel. -/
@[rep_depth krein]
theorem diracMinus_mul_diracMinus_eq_zero :
    B.diracMinus * B.diracMinus = 0 := by
  rw [B.diracMinus_eq_uPlus]
  exact (B.drazinSplit).uPlus_mul_uPlus_eq_zero B.Dirac B.Dirac

/--
Odd-to-even Hodge-Cartan closure: if `D` anticommutes with `⋆χ`, then `D²`
commutes with `⋆χ`.
-/
@[rep_depth krein]
theorem dirac_square_commutes_hodgeChiralityStar :
    (B.Dirac * B.Dirac) * hodgeChiralityStar B.CIK =
      hodgeChiralityStar B.CIK * (B.Dirac * B.Dirac) := by
  calc
    (B.Dirac * B.Dirac) * hodgeChiralityStar B.CIK
        = B.Dirac * (B.Dirac * hodgeChiralityStar B.CIK) := by
            simp [mul_assoc]
    _ = B.Dirac * (-(hodgeChiralityStar B.CIK * B.Dirac)) := by
            rw [B.Dirac_odd]
    _ = -(B.Dirac * (hodgeChiralityStar B.CIK * B.Dirac)) := by
            simp
    _ = -((B.Dirac * hodgeChiralityStar B.CIK) * B.Dirac) := by
            simp [mul_assoc]
    _ = -((-(hodgeChiralityStar B.CIK * B.Dirac)) * B.Dirac) := by
            rw [B.Dirac_odd]
    _ = hodgeChiralityStar B.CIK * (B.Dirac * B.Dirac) := by
            simp [mul_assoc]

/-- Moore--Penrose range projector regular-from-defect cone component. -/
@[rep_depth krein]
noncomputable def mpRange_uPlus : EndH :=
  (B.drazinSplit).uPlus B.CIK.mpRangeProjector

/-- Moore--Penrose range projector defect-from-regular cone component. -/
@[rep_depth krein]
noncomputable def mpRange_uMinus : EndH :=
  (B.drazinSplit).uMinus B.CIK.mpRangeProjector

/-- Moore--Penrose domain/metric projector regular-from-defect cone component. -/
@[rep_depth krein]
noncomputable def mpMetric_uPlus : EndH :=
  (B.drazinSplit).uPlus B.CIK.metricProjector

/-- Moore--Penrose domain/metric projector defect-from-regular cone component. -/
@[rep_depth krein]
noncomputable def mpMetric_uMinus : EndH :=
  (B.drazinSplit).uMinus B.CIK.metricProjector

/-- The right/range Moore--Penrose anomaly is the lightcone mismatch of the range projector. -/
@[rep_depth krein]
theorem rightChiralAnomaly_eq_mpRange_uPlus_sub_uMinus :
    B.CIK.rightChiralAnomaly = B.mpRange_uPlus - B.mpRange_uMinus := by
  unfold mpRange_uPlus mpRange_uMinus
  change
    DrazinLightConeDictionary.commutator
      B.CIK.spectralProjector B.CIK.mpRangeProjector =
    (B.drazinSplit).uPlus B.CIK.mpRangeProjector
      - (B.drazinSplit).uMinus B.CIK.mpRangeProjector
  exact (B.drazinSplit).commutator_P_eq_uPlus_sub_uMinus B.CIK.mpRangeProjector

/-- The left/domain Moore--Penrose anomaly is the lightcone mismatch of the metric projector. -/
@[rep_depth krein]
theorem chiralAnomaly_eq_mpMetric_uPlus_sub_uMinus :
    B.CIK.chiralAnomaly = B.mpMetric_uPlus - B.mpMetric_uMinus := by
  unfold mpMetric_uPlus mpMetric_uMinus
  change
    DrazinLightConeDictionary.commutator
      B.CIK.spectralProjector B.CIK.metricProjector =
    (B.drazinSplit).uPlus B.CIK.metricProjector
      - (B.drazinSplit).uMinus B.CIK.metricProjector
  exact (B.drazinSplit).commutator_P_eq_uPlus_sub_uMinus B.CIK.metricProjector

/-- The net Moore--Penrose chiral charge is the difference between range and metric lightcone mismatches. -/
@[rep_depth krein]
theorem netMPChiralCharge_eq_lightcone_mismatch :
    B.CIK.rightChiralAnomaly - B.CIK.chiralAnomaly =
      (B.mpRange_uPlus - B.mpRange_uMinus)
        - (B.mpMetric_uPlus - B.mpMetric_uMinus) := by
  rw [B.rightChiralAnomaly_eq_mpRange_uPlus_sub_uMinus,
    B.chiralAnomaly_eq_mpMetric_uPlus_sub_uMinus]

/--
The certified anomaly is already off-diagonal for the Drazin chiral cone. This
is the existing owner theorem re-exported through the bridge.
-/
@[rep_depth krein]
theorem chiralAnomaly_offDiagonal_support :
    B.CIK.spectralProjector * B.CIK.chiralAnomaly * B.CIK.spectralProjector = 0
      ∧
    B.CIK.spectralComplementaryProjector * B.CIK.chiralAnomaly *
        B.CIK.spectralComplementaryProjector = 0
      ∧
    B.CIK.chiralAnomaly =
      B.CIK.spectralProjector * B.CIK.chiralAnomaly *
          B.CIK.spectralComplementaryProjector
        +
      B.CIK.spectralComplementaryProjector * B.CIK.chiralAnomaly *
          B.CIK.spectralProjector := by
  exact B.CIK.chiralAnomaly_spectralSupportProfile

end DrazinMPChiralHodgeConeBridge

end Core

end InfoGeometry.Canonical.DrazinMPChiralHodgeConeBridge
