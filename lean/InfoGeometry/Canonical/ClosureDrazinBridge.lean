import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.DrazinPenroseDilationKKT
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace ClosureDrazinBridge

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

This stores only the certified inverse-kernel owner.  The chiral closure facts
below are read directly from `CertifiedInverseKernel` and
`ChiralOperatorConeClosure`, without an intermediate proof packet.
-/
@[rep_depth krein]
structure ConstructiveClosureDrazinData where
  kernel : CertifiedInverseKernel E

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
  by
    simpa [DrazinSupercharge.commutator] using
      C.kernel.spectralProjector_commutator_GammaG_eq_sub_anomalies

/-- Closure identity: `[P_D, G] = (1/2)(χ_R - χ_L)`. -/
@[rep_depth krein]
theorem commutator_P_D_dilationGap_eq_half_sub_anomalies :
    DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.dilationGap
      = ((2 : ℝ)⁻¹) • (C.kernel.rightChiralAnomaly - C.kernel.chiralAnomaly) :=
  by
    simpa [DrazinSupercharge.commutator] using
      C.kernel.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies

/-- Left anomaly is odd with respect to `Γ_S` in anticommutator form. -/
@[rep_depth krein]
theorem anticommutator_GammaS_chiL_eq_zero :
    DrazinSupercharge.anticommutator C.kernel.GammaS C.kernel.chiralAnomaly = 0 :=
  anticommutator_GammaS_chiralAnomaly_eq_zero (CIK := C.kernel)

/-- Right anomaly is odd with respect to `Γ_S` in anticommutator form. -/
@[rep_depth krein]
theorem anticommutator_GammaS_chiR_eq_zero :
    DrazinSupercharge.anticommutator C.kernel.GammaS C.kernel.rightChiralAnomaly = 0 :=
  anticommutator_GammaS_rightChiralAnomaly_eq_zero (CIK := C.kernel)

/-- Left anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiL_mem_chiralCone :
    IsInChiralOperatorCone C.kernel C.kernel.chiralAnomaly :=
  chiralAnomaly_mem_chiralOperatorCone (CIK := C.kernel)

/-- Right anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiR_mem_chiralCone :
    IsInChiralOperatorCone C.kernel C.kernel.rightChiralAnomaly :=
  rightChiralAnomaly_mem_chiralOperatorCone (CIK := C.kernel)

/-- Canonical odd generator identity: `Q = [P_D, Γ_G]`. -/
@[rep_depth krein]
theorem supercharge_eq_commutator_P_D_GammaG :
    DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel
      = DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG :=
  DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_GammaG
    (CIK := C.kernel)

/-- The canonical odd generator lies in the spectral chiral cone. -/
@[rep_depth krein]
theorem supercharge_mem_chiralCone :
    IsInChiralOperatorCone C.kernel
      (DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel) :=
  supercharge_mem_chiralOperatorCone (CIK := C.kernel)

/--
Closure-level chiral-supertrace cancellation for the Drazin odd generator.

This delegates to the kernel owner: oddness of `Q_D` plus cyclicity of the
chosen chiral readout forces `Str_Γ(Q_D)=0`.
-/
@[rep_depth krein]
theorem chiralSupertrace_supercharge_eq_zero
    (τ : DrazinSupercharge.CertifiedInverseKernel.ChiralSupertraceReadout C.kernel) :
    DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace
        (CIK := C.kernel) τ
        (DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel) = 0 :=
  DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace_supercharge_eq_zero
    (CIK := C.kernel) τ

/--
Drazin-Witten public alias for the vanishing chiral supertrace of the odd
Drazin generator.

This is the same kernel-checked cancellation as `chiralSupertrace_supercharge_eq_zero`,
re-exported under the Drazin-Witten wording used by the grand-unification lane.
-/
@[rep_depth krein]
theorem drazinWitten_chiralSupertrace_eq_zero
    (τ : DrazinSupercharge.CertifiedInverseKernel.ChiralSupertraceReadout C.kernel) :
    DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace
        (CIK := C.kernel) τ
        (DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel) = 0 :=
  chiralSupertrace_supercharge_eq_zero (C := C) τ

/-- Compact/chiral commutator closure on the gathered package. -/
@[rep_depth krein]
theorem spectralCommutator_compact_mem_chiralCone
    {X Y : EndH}
    (hX : C.kernel.IsSpectralCompact X)
    (hY : IsInChiralOperatorCone C.kernel Y) :
    IsInChiralOperatorCone C.kernel (CertifiedInverseKernel.spectralCommutator X Y) :=
  spectralCommutator_compact_mem_chiralOperatorCone (CIK := C.kernel) hX hY

/--
Compatibility adapter from closure-gathered data to the direct
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

end ConstructiveClosureDrazinData

end Core

end ClosureDrazinBridge
