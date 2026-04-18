import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.DrazinPenroseDilationKKT
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ClosureDrazinBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ChiralOperatorConeClosure
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Canonical.DrazinPenroseDilationKKT

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/--
A non-circular closure package for the chiral/Drazin lane.

This is a thin adapter layer over the reified spectral owner
`SpectralChiralConeAlgebra`.
-/
@[rep_depth krein]
structure ConstructiveClosureDrazinData where
  kernel : CertifiedInverseKernel E
  chiralAlgebra : SpectralChiralConeAlgebra kernel

namespace ConstructiveClosureDrazinData

variable (C : ConstructiveClosureDrazinData (E := E))

/-- KKT-lane view of the same certified kernel. -/
@[rep_depth krein]
def toDPDKKT : DPDKKT E :=
  ⟨C.kernel⟩

/-- Closure identity: `[P_D, Γ_G] = χ_R - χ_L`. -/
@[rep_depth krein]
theorem commutator_P_D_GammaG_eq_sub_anomalies :
    DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG
      = C.kernel.rightChiralAnomaly - C.kernel.chiralAnomaly :=
  C.chiralAlgebra.commutator_P_D_GammaG_eq_sub_anomalies

/-- Closure identity: `[P_D, G] = (1/2)(χ_R - χ_L)`. -/
@[rep_depth krein]
theorem commutator_P_D_dilationGap_eq_half_sub_anomalies :
    DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.dilationGap
      = ((2 : ℝ)⁻¹) • (C.kernel.rightChiralAnomaly - C.kernel.chiralAnomaly) :=
  C.chiralAlgebra.commutator_P_D_dilationGap_eq_half_sub_anomalies

/-- Left anomaly is odd with respect to `Γ_S` in anticommutator form. -/
@[rep_depth krein]
theorem anticommutator_GammaS_chiL_eq_zero :
    DrazinSupercharge.anticommutator C.kernel.GammaS C.kernel.chiralAnomaly = 0 :=
  C.chiralAlgebra.anticommutator_GammaS_chiL_eq_zero

/-- Right anomaly is odd with respect to `Γ_S` in anticommutator form. -/
@[rep_depth krein]
theorem anticommutator_GammaS_chiR_eq_zero :
    DrazinSupercharge.anticommutator C.kernel.GammaS C.kernel.rightChiralAnomaly = 0 :=
  C.chiralAlgebra.anticommutator_GammaS_chiR_eq_zero

/-- Left anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiL_mem_chiralCone :
    IsInChiralOperatorCone C.kernel C.kernel.chiralAnomaly :=
  C.chiralAlgebra.chiL_mem_chiralCone

/-- Right anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiR_mem_chiralCone :
    IsInChiralOperatorCone C.kernel C.kernel.rightChiralAnomaly :=
  C.chiralAlgebra.chiR_mem_chiralCone

/-- Canonical odd generator identity: `Q = [P_D, Γ_G]`. -/
@[rep_depth krein]
theorem supercharge_eq_commutator_P_D_GammaG :
    DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel
      = DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG :=
  C.chiralAlgebra.supercharge_eq_commutator_P_D_GammaG

/-- The canonical odd generator lies in the spectral chiral cone. -/
@[rep_depth krein]
theorem supercharge_mem_chiralCone :
    IsInChiralOperatorCone C.kernel
      (DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel) :=
  C.chiralAlgebra.supercharge_mem_chiralCone

/-- Compact/chiral commutator closure on the gathered package. -/
@[rep_depth krein]
theorem spectralCommutator_compact_mem_chiralCone
    {X Y : EndH}
    (hX : C.kernel.IsSpectralCompact X)
    (hY : IsInChiralOperatorCone C.kernel Y) :
    IsInChiralOperatorCone C.kernel (CertifiedInverseKernel.spectralCommutator X Y) :=
  C.chiralAlgebra.compact_commutator_closed hX hY

/--
Compatibility adapter from closure-gathered data to the witness-free
constructive Riesz owner in `DrazinInfiniteCore`.
-/
@[rep_depth krein]
def toConstructiveRieszDecompositionAtZero :
    ConstructiveRieszDecompositionAtZero (𝕂 := ℝ) C.kernel.A where
  k := C.kernel.drazinIndex
  P := C.kernel.spectralProjector
  P_idempotent := C.kernel.spectralProjector_idempotent
  PT_comm := by
    change C.kernel.A * Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D =
        Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D * C.kernel.A
    exact (Drazin.IsDrazinInverse.projection_mul_eq_mul_projection (h := C.kernel.hDrazin)).symm
  S := C.kernel.A_D
  left_inverse_on_regular := by
    calc
      C.kernel.A_D * C.kernel.A = C.kernel.A * C.kernel.A_D := C.kernel.hDrazin.comm.symm
      _ = Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D := by rfl
      _ = C.kernel.spectralProjector := by rfl
  right_inverse_on_regular := by
    calc
      C.kernel.A * C.kernel.A_D = Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D := by
        rfl
      _ = C.kernel.spectralProjector := by rfl
  S_supported_on_regular_left := by
    calc
      C.kernel.A_D * C.kernel.spectralProjector
          = C.kernel.A_D * Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D := by
              rfl
      _ = C.kernel.A_D := by
            simpa [Drazin.IsDrazinInverse.projection, mul_assoc] using C.kernel.hDrazin.idempotent
  S_supported_on_regular_right := by
    calc
      C.kernel.spectralProjector * C.kernel.A_D
          = Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D * C.kernel.A_D := by
              rfl
      _ = C.kernel.A_D * Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D := by
            simpa using Drazin.IsDrazinInverse.projection_comm (h := C.kernel.hDrazin)
      _ = C.kernel.A_D := by
            simpa [Drazin.IsDrazinInverse.projection, mul_assoc] using C.kernel.hDrazin.idempotent
  nilpotent_on_complement := by
    calc
      C.kernel.A ^ C.kernel.drazinIndex * (1 - C.kernel.spectralProjector)
          = C.kernel.A ^ C.kernel.drazinIndex
              * (1 - Drazin.IsDrazinInverse.projection C.kernel.A C.kernel.A_D) := by
                rfl
      _ = C.kernel.A ^ C.kernel.drazinIndex * (1 - C.kernel.A * C.kernel.A_D) := by
            rfl
      _ = C.kernel.A ^ C.kernel.drazinIndex
            - C.kernel.A ^ C.kernel.drazinIndex * (C.kernel.A * C.kernel.A_D) := by
              rw [mul_sub, mul_one]
      _ = C.kernel.A ^ C.kernel.drazinIndex
            - C.kernel.A ^ (C.kernel.drazinIndex + 1) * C.kernel.A_D := by
              rw [pow_succ, mul_assoc]
      _ = C.kernel.A ^ C.kernel.drazinIndex - C.kernel.A ^ C.kernel.drazinIndex := by
            rw [C.kernel.hDrazin.power]
      _ = 0 := by simp

/--
Constructive closure package yields Drazin existence through the constructive
Riesz owner route.
-/
@[rep_depth krein]
theorem exists_drazinInverse_of_constructiveClosure :
    ∃ k D, Drazin.IsDrazinInverse C.kernel.A D k := by
  exact
    exists_drazinInverse_of_constructiveRieszDecompositionAtZero
      (hR := C.toConstructiveRieszDecompositionAtZero)

/--
Thin adapter from the reified spectral chiral owner into
`ConstructiveClosureDrazinData`.
-/
@[rep_depth krein]
def ofSpectralChiralConeAlgebra
    (CIK : CertifiedInverseKernel E)
    (Aχ : SpectralChiralConeAlgebra CIK) :
    ConstructiveClosureDrazinData (E := E) where
  kernel := CIK
  chiralAlgebra := Aχ

end ConstructiveClosureDrazinData

/-- Canonical constructor from the certified Drazin owner surface. -/
@[rep_depth krein]
def ConstructiveClosureDrazinData.ofCertifiedInverseKernel
    (CIK : CertifiedInverseKernel E) :
    ConstructiveClosureDrazinData (E := E) :=
  ConstructiveClosureDrazinData.ofSpectralChiralConeAlgebra
    (CIK := CIK)
    (Aχ := SpectralChiralConeAlgebra.ofCertifiedInverseKernel (CIK := CIK))

/-- Existence wrapper for the non-circular closure package. -/
@[rep_depth krein]
theorem exists_constructiveClosureDrazinData
    (CIK : CertifiedInverseKernel E) :
    ∃ C : ConstructiveClosureDrazinData (E := E), C.kernel = CIK := by
  refine ⟨ConstructiveClosureDrazinData.ofCertifiedInverseKernel (CIK := CIK), rfl⟩

end Core

end InfoGeometry.Canonical.ClosureDrazinBridge
