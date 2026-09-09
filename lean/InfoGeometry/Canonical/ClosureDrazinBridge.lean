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

This stores only the certified inverse-kernel owner.  The chiral closure facts
below are read directly from `CertifiedInverseKernel` and
`ChiralOperatorConeClosure`, without an intermediate proof packet.
-/
@[rep_depth krein]
abbrev ConstructiveClosureDrazinData := CertifiedInverseKernel E

namespace ConstructiveClosureDrazinData

variable (C : ConstructiveClosureDrazinData (E := E))

/-- KKT-lane view of the same certified kernel. -/
@[rep_depth krein]
def toDPDKKT : DPDKKT E :=
  ⟨C⟩

/-- Closure identity: `[P_D, Γ_G] = χ_R - χ_L`. -/
@[rep_depth krein]
theorem commutator_P_D_GammaG_eq_sub_anomalies :
    DrazinSupercharge.commutator C.spectralProjector C.GammaG
      = C.rightChiralAnomaly - C.chiralAnomaly :=
  by
    simpa [DrazinSupercharge.commutator] using
      C.spectralProjector_commutator_GammaG_eq_sub_anomalies

/-- Closure identity: `[P_D, G] = (1/2)(χ_R - χ_L)`. -/
@[rep_depth krein]
theorem commutator_P_D_dilationGap_eq_half_sub_anomalies :
    DrazinSupercharge.commutator C.spectralProjector C.dilationGap
      = ((2 : ℝ)⁻¹) • (C.rightChiralAnomaly - C.chiralAnomaly) :=
  by
    simpa [DrazinSupercharge.commutator] using
      C.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies

/-- Left anomaly is odd with respect to `Γ_S` in anticommutator form. -/
@[rep_depth krein]
theorem anticommutator_GammaS_chiL_eq_zero :
    DrazinSupercharge.anticommutator C.GammaS C.chiralAnomaly = 0 :=
  anticommutator_GammaS_chiralAnomaly_eq_zero (CIK := C)

/-- Right anomaly is odd with respect to `Γ_S` in anticommutator form. -/
@[rep_depth krein]
theorem anticommutator_GammaS_chiR_eq_zero :
    DrazinSupercharge.anticommutator C.GammaS C.rightChiralAnomaly = 0 :=
  anticommutator_GammaS_rightChiralAnomaly_eq_zero (CIK := C)

/-- Left anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiL_mem_chiralCone :
    IsInChiralOperatorCone C C.chiralAnomaly :=
  chiralAnomaly_mem_chiralOperatorCone (CIK := C)

/-- Right anomaly belongs to the spectral chiral cone. -/
@[rep_depth krein]
theorem chiR_mem_chiralCone :
    IsInChiralOperatorCone C C.rightChiralAnomaly :=
  rightChiralAnomaly_mem_chiralOperatorCone (CIK := C)

/-- Canonical odd generator identity: `Q = [P_D, Γ_G]`. -/
@[rep_depth krein]
theorem supercharge_eq_commutator_P_D_GammaG :
    DrazinSupercharge.CertifiedInverseKernel.supercharge C
      = DrazinSupercharge.commutator C.spectralProjector C.GammaG :=
  DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_GammaG
    (CIK := C)

/-- The canonical odd generator lies in the spectral chiral cone. -/
@[rep_depth krein]
theorem supercharge_mem_chiralCone :
    IsInChiralOperatorCone C
      (DrazinSupercharge.CertifiedInverseKernel.supercharge C) :=
  supercharge_mem_chiralOperatorCone (CIK := C)

/--
Closure-level chiral-supertrace cancellation for the Drazin odd generator.

This delegates to the kernel owner: oddness of `Q_D` plus cyclicity of the
chosen chiral readout forces `Str_Γ(Q_D)=0`.
-/
@[rep_depth krein]
theorem chiralSupertrace_supercharge_eq_zero
    (τ : DrazinSupercharge.CertifiedInverseKernel.ChiralSupertraceReadout C) :
    DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace
        (CIK := C) τ
        (DrazinSupercharge.CertifiedInverseKernel.supercharge C) = 0 :=
  DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace_supercharge_eq_zero
    (CIK := C) τ

/--
Drazin-Witten public alias for the vanishing chiral supertrace of the odd
Drazin generator.

This is the same kernel-checked cancellation as `chiralSupertrace_supercharge_eq_zero`,
re-exported under the Drazin-Witten wording used by the grand-unification lane.
-/
@[rep_depth krein]
theorem drazinWitten_chiralSupertrace_eq_zero
    (τ : DrazinSupercharge.CertifiedInverseKernel.ChiralSupertraceReadout C) :
    DrazinSupercharge.CertifiedInverseKernel.chiralSupertrace
        (CIK := C) τ
        (DrazinSupercharge.CertifiedInverseKernel.supercharge C) = 0 :=
  chiralSupertrace_supercharge_eq_zero (C := C) τ

/-- Compact/chiral commutator closure on the gathered package. -/
@[rep_depth krein]
theorem spectralCommutator_compact_mem_chiralCone
    {X Y : EndH}
    (hX : C.IsSpectralCompact X)
    (hY : IsInChiralOperatorCone C Y) :
    IsInChiralOperatorCone C (CertifiedInverseKernel.spectralCommutator X Y) :=
  spectralCommutator_compact_mem_chiralOperatorCone (CIK := C) hX hY

/--
Compatibility adapter from closure-gathered data to the direct
constructive Riesz owner in `DrazinInfiniteCore`.
-/
@[rep_depth krein]
def toConstructiveRieszDecompositionAtZero :
    ConstructiveRieszDecompositionAtZero (𝕂 := ℝ) C.A where
  k := C.drazinIndex
  P := C.spectralProjector
  P_idempotent := C.spectralProjector_idempotent
  PT_comm := by
    change C.A * Drazin.IsDrazinInverse.projection C.A C.A_D =
        Drazin.IsDrazinInverse.projection C.A C.A_D * C.A
    exact (Drazin.IsDrazinInverse.projection_mul_eq_mul_projection (h := C.hDrazin)).symm
  S := C.A_D
  left_inverse_on_regular := by
    calc
      C.A_D * C.A = C.A * C.A_D := C.hDrazin.comm.symm
      _ = Drazin.IsDrazinInverse.projection C.A C.A_D := by rfl
      _ = C.spectralProjector := by rfl
  right_inverse_on_regular := by
    calc
      C.A * C.A_D = Drazin.IsDrazinInverse.projection C.A C.A_D := by
        rfl
      _ = C.spectralProjector := by rfl
  S_supported_on_regular_left := by
    calc
      C.A_D * C.spectralProjector
          = C.A_D * Drazin.IsDrazinInverse.projection C.A C.A_D := by
              rfl
      _ = C.A_D := by
            simpa [Drazin.IsDrazinInverse.projection, mul_assoc] using C.hDrazin.idempotent
  S_supported_on_regular_right := by
    calc
      C.spectralProjector * C.A_D
          = Drazin.IsDrazinInverse.projection C.A C.A_D * C.A_D := by
              rfl
      _ = C.A_D * Drazin.IsDrazinInverse.projection C.A C.A_D := by
            simpa using Drazin.IsDrazinInverse.projection_comm (h := C.hDrazin)
      _ = C.A_D := by
            simpa [Drazin.IsDrazinInverse.projection, mul_assoc] using C.hDrazin.idempotent
  nilpotent_on_complement := by
    calc
      C.A ^ C.drazinIndex * (1 - C.spectralProjector)
          = C.A ^ C.drazinIndex
              * (1 - Drazin.IsDrazinInverse.projection C.A C.A_D) := by
                rfl
      _ = C.A ^ C.drazinIndex * (1 - C.A * C.A_D) := by
            rfl
      _ = C.A ^ C.drazinIndex
            - C.A ^ C.drazinIndex * (C.A * C.A_D) := by
              rw [mul_sub, mul_one]
      _ = C.A ^ C.drazinIndex
            - C.A ^ (C.drazinIndex + 1) * C.A_D := by
              rw [pow_succ, mul_assoc]
      _ = C.A ^ C.drazinIndex - C.A ^ C.drazinIndex := by
            rw [C.hDrazin.power]
      _ = 0 := by simp

/--
Constructive closure package yields Drazin existence through the constructive
Riesz owner route.
-/
@[rep_depth krein]
theorem exists_drazinInverse_of_constructiveClosure :
    ∃ k D, Drazin.IsDrazinInverse C.A D k := by
  exact
    exists_drazinInverse_of_constructiveRieszDecompositionAtZero
      (hR := C.toConstructiveRieszDecompositionAtZero)

end ConstructiveClosureDrazinData

end Core

end InfoGeometry.Canonical.ClosureDrazinBridge
