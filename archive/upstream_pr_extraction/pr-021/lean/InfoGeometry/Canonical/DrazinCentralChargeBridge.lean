import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DrazinCentralChargeBridge

Bridge the internal Drazin split lane (`Q_D² = H + Z`) to the transported
operatorial central-charge lane without collapsing them into a single ontology.

This file keeps the currently honest separation:
- `DrazinSupercharge`: internal operator-valued split with Drazin-lane centrality.
- `OperatorialCentralCharge`: transported analytical-index owner.

The bridge packages both on the same doubled real carrier.
-/

namespace InfoGeometry.Canonical.DrazinCentralChargeBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

section CarrierLane

variable {A B F : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [KreinSpace (DoubledSpace F)] [KreinGradedModule (DoubledSpace F)]

local notation "H₂" => DoubledSpace F
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

namespace DrazinLane

/--
Scalar-shadow realization of the transported operatorial central charge on the
local Drazin operator lane.
-/
@[rep_depth transport]
noncomputable def operatorialCentralScalar
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : EndH :=
  ((operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)) • (1 : EndH)

/--
Any scalar-shadow central operator commutes with the full Drazin lane.
-/
@[rep_depth transport]
theorem operatorialCentralScalar_isDrazinLaneCentral
    (CIK : CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK (operatorialCentralScalar (A := A) (B := B) X hX) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact (Commute.one_left CIK.spectralProjector).smul_left
        (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)
    · exact (Commute.one_left CIK.spectralComplementaryProjector).smul_left
        (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)
  · exact (Commute.one_left CIK.toInformationCartanTriple.GammaS).smul_left
      (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)

/--
Transported slice equality written directly on the scalar-shadow operator.
-/
@[rep_depth transport]
theorem operatorialCentralScalar_eq_transport_slice
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    operatorialCentralScalar (A := A) (B := B) X hX
      =
    ((quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t) : ℝ)) • (1 : EndH) := by
  have hIdx :=
    operatorialCentralCharge_eq_transport_slice
      (A := A) (B := B) (E := F) V X hX hEven t
  have hIdxR :
      (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ)
        =
      (quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t) : ℝ) := by
    exact congrArg (fun z : ℤ => (z : ℝ)) hIdx.symm
  calc
    operatorialCentralScalar (A := A) (B := B) X hX
        =
      (operatorialCentralCharge (A := A) (B := B) (E := F) X hX : ℝ) • (1 : EndH) := by
          rfl
    _ =
      (quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t) : ℝ) • (1 : EndH) := by
          rw [hIdxR]

/--
Integrated bridge packet:

1. internal Drazin split `Q_D² = H + Z` with lane-central `Z`,
2. transported operatorial central-charge scalar shadow `Zop`,
3. transported index equality for the same slice.
-/
@[rep_depth transport]
theorem exists_internal_split_with_operatorial_shadow
    (CIK : CertifiedInverseKernel H₂)
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    ∃ H Z : EndH,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK CIK H
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        = H + Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (operatorialCentralScalar (A := A) (B := B) X hX)
        ∧
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        =
      operatorialCentralCharge (A := A) (B := B) (E := F) X hX := by
  rcases
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.exists_superHamiltonian_canonical_split_with_drazin_lane_centralityK
        (CIK := CIK) with
    ⟨H, Z, hCentral, hDefect, hVanishing, hSplit⟩
  refine ⟨H, Z, hCentral, hDefect, hVanishing, hSplit, ?_, ?_⟩
  · exact operatorialCentralScalar_isDrazinLaneCentral (A := A) (B := B) CIK X hX
  · exact operatorialCentralCharge_eq_transport_slice
      (A := A) (B := B) (E := F) V X hX hEven t

/--
Intrinsic non-scalar bridge packet:

1. canonical internal split `Q_D² = H + Z` on the Drazin lane,
2. intrinsic transported defect shadow `Z_shadow` is lane-central/defect-supported,
3. intrinsic residual `Z - Z_shadow` remains lane-central/defect-supported,
4. transported analytical index equals the operatorial central charge.
-/
@[rep_depth transport]
theorem exists_internal_split_with_intrinsic_nonScalar_shadow
    (CIK : CertifiedInverseKernel H₂)
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    ∃ H Z : EndH,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK CIK H
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        = H + Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.intrinsicCentralIndexResidual
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.intrinsicCentralIndexResidual
          (A := A) (B := B) CIK X hX)
        ∧
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        =
      operatorialCentralCharge (A := A) (B := B) (E := F) X hX := by
  have hPack :
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        =
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK)
        +
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.intrinsicCentralIndexResidual
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.intrinsicCentralIndexResidual
          (A := A) (B := B) CIK X hX)
        ∧
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        =
      operatorialCentralCharge (A := A) (B := B) (E := F) X hX :=
    InfoGeometry.Canonical.DrazinSupercharge.canonical_split_with_intrinsic_nonScalar_and_index_shadow
      (A := A) (B := B) CIK V X hX hEven t
  rcases hPack with
    ⟨hSplit, hCanonCentral, hShadowCentral, hShadowDef, hResidualCentral, hResidualDef, hIdx⟩
  refine ⟨
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK),
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK,
    hCanonCentral,
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK_isDefectSupportedK
      (CIK := CIK),
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK_hasVanishingDefectBlockK
      (CIK := CIK),
    hSplit,
    hShadowCentral,
    hShadowDef,
    hResidualCentral,
    hResidualDef,
    hIdx⟩

/--
Strict non-scalarity witness for the intrinsic transported defect shadow.

This closes the remaining naming-vs-proof gap: the "intrinsic non-scalar"
shadow is formally non-scalar whenever:
- the operatorial central charge is nonzero, and
- the Drazin defect projector is nontrivial (`Q₀ ≠ 0`, `Q₀ ≠ 1`).
-/
@[rep_depth transport]
theorem intrinsic_nonScalar_shadow_witness
    (CIK : CertifiedInverseKernel H₂)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hCharge : operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0)
    (hQ0ne0 : CIK.spectralComplementaryProjector ≠ 0)
    (hQ0ne1 : CIK.spectralComplementaryProjector ≠ (1 : EndH)) :
    ¬ InfoGeometry.Canonical.DrazinSupercharge.IsScalarOperatorK
      (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
        (A := A) (B := B) CIK X hX) := by
  exact
    InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow_not_scalar_of_nonzero_charge_of_nontrivial_defect_projector
      (A := A) (B := B) CIK X hX hCharge hQ0ne0 hQ0ne1

/--
Integrated intrinsic bridge + strict non-scalarity witness.
-/
@[rep_depth transport]
theorem exists_internal_split_with_intrinsic_nonScalar_shadow_and_witness
    (CIK : CertifiedInverseKernel H₂)
    (V : BogoliubovVielbeinBundle (E := F))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hCharge : operatorialCentralCharge (A := A) (B := B) (E := F) X hX ≠ 0)
    (hQ0ne0 : CIK.spectralComplementaryProjector ≠ 0)
    (hQ0ne1 : CIK.spectralComplementaryProjector ≠ (1 : EndH)) :
    (∃ H Z : EndH,
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlockK CIK H
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        = H + Z
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.intrinsicCentralIndexResidual
          (A := A) (B := B) CIK X hX)
        ∧
      InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK CIK
        (InfoGeometry.Canonical.DrazinSupercharge.intrinsicCentralIndexResidual
          (A := A) (B := B) CIK X hX)
        ∧
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := F) V X hX hEven t)
        =
      operatorialCentralCharge (A := A) (B := B) (E := F) X hX)
      ∧
    ¬ InfoGeometry.Canonical.DrazinSupercharge.IsScalarOperatorK
      (InfoGeometry.Canonical.DrazinSupercharge.operatorialCentralDefectShadow
        (A := A) (B := B) CIK X hX) := by
  refine ⟨?_, ?_⟩
  · exact exists_internal_split_with_intrinsic_nonScalar_shadow
      (A := A) (B := B) CIK V X hX hEven t
  · exact intrinsic_nonScalar_shadow_witness
      (A := A) (B := B) CIK X hX hCharge hQ0ne0 hQ0ne1

end DrazinLane

end CarrierLane

end InfoGeometry.Canonical.DrazinCentralChargeBridge
