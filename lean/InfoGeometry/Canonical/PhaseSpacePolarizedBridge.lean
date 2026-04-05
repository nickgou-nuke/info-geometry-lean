import InfoGeometry.Canonical.RelativeModularPolarizedBridge
import InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpacePolarizedBridge

Adjacency bridge from the corrected neutral phase-space owner to the existing
polarized relative-modular carrier package.

This file stays narrow:

- a chosen real duality equivalence `ρ : H ≃ₗ[ℝ] H*` pulls polarized doubled
  lifts back to owner-side phase-space lifts,
- the phase-space `±` projectors fix those pulled-back lifts exactly,
- and the forward doubled realization recovers the original polarized lifts.

No recomposition data is introduced here.
-/

namespace InfoGeometry.Canonical.PhaseSpacePolarizedBridge

open InfoGeometry.Canonical.RelativeModularPolarizedBridge
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {betaPlus : Type*} [Fintype betaPlus] [Nonempty betaPlus]
variable {betaMinus : Type*} [Fintype betaMinus] [Nonempty betaMinus]

/-- Owner-side phase-space lift of a polarized `+`-sector point. -/
@[rep_depth krein]
noncomputable def PlusRestrictedRelativeModularData.phaseLift
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) : PhaseSpaceCarrier H :=
  fromDoubledCopyRho (E := H) ρ (R.lift b)

/-- Owner-side phase-space lift of a polarized `-`-sector point. -/
@[rep_depth krein]
noncomputable def MinusRestrictedRelativeModularData.phaseLift
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) : PhaseSpaceCarrier H :=
  fromDoubledCopyRho (E := H) ρ (R.lift b)

@[rep_depth krein, simp] theorem PlusRestrictedRelativeModularData.realize_phaseLift
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    toDoubledCopyRho (E := H) ρ (PlusRestrictedRelativeModularData.phaseLift R ρ b) = R.lift b := by
  apply DoubledSpace.ext <;>
    simp [PlusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply,
      toDoubledCopyRho_apply]

@[rep_depth krein, simp] theorem MinusRestrictedRelativeModularData.realize_phaseLift
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    toDoubledCopyRho (E := H) ρ (MinusRestrictedRelativeModularData.phaseLift R ρ b) = R.lift b := by
  apply DoubledSpace.ext <;>
    simp [MinusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply,
      toDoubledCopyRho_apply]

@[rep_depth krein, simp] theorem PlusRestrictedRelativeModularData.phaseLift_fixed_by_phasePlusProjector
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    phasePlusProjector (E := H) (PlusRestrictedRelativeModularData.phaseLift R ρ b)
      = PlusRestrictedRelativeModularData.phaseLift R ρ b := by
  have hsnd : WithLp.snd (R.lift b) = 0 := by
    exact (mem_plusSheet_iff_snd_eq_zero (E := H) (R.lift b)).mp (R.lift_mem b)
  rw [PlusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply, hsnd]
  ext
  · simp [phasePlusProjector_apply, phaseEpsilon_apply]
    calc
      (2 : ℝ)⁻¹ • WithLp.fst (R.lift b) + (2 : ℝ)⁻¹ • WithLp.fst (R.lift b)
          = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • WithLp.fst (R.lift b) := by
              simpa using
                (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) (WithLp.fst (R.lift b))).symm
      _ = WithLp.fst (R.lift b) := by
            norm_num
  ·
    simp [phasePlusProjector_apply, phaseEpsilon_apply]

@[rep_depth krein, simp] theorem MinusRestrictedRelativeModularData.phaseLift_fixed_by_phaseMinusProjector
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    phaseMinusProjector (E := H) (MinusRestrictedRelativeModularData.phaseLift R ρ b)
      = MinusRestrictedRelativeModularData.phaseLift R ρ b := by
  have hfst : WithLp.fst (R.lift b) = 0 := by
    exact (mem_minusSheet_iff_fst_eq_zero (E := H) (R.lift b)).mp (R.lift_mem b)
  rw [MinusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply, hfst]
  ext
  · simp [phaseMinusProjector_apply, phaseEpsilon_apply]
  ·
    simp [phaseMinusProjector_apply, phaseEpsilon_apply]
    ring_nf

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.plus_realize_phaseLift
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    toDoubledCopyRho (E := H) ρ
      (PlusRestrictedRelativeModularData.phaseLift R.plus ρ b) = R.plus.lift b := by
  simpa using PlusRestrictedRelativeModularData.realize_phaseLift R.plus ρ b

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.minus_realize_phaseLift
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    toDoubledCopyRho (E := H) ρ
      (MinusRestrictedRelativeModularData.phaseLift R.minus ρ b) = R.minus.lift b := by
  simpa using MinusRestrictedRelativeModularData.realize_phaseLift R.minus ρ b

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.plus_phaseLift_fixed_by_phasePlusProjector
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    phasePlusProjector (E := H) (PlusRestrictedRelativeModularData.phaseLift R.plus ρ b)
      = PlusRestrictedRelativeModularData.phaseLift R.plus ρ b := by
  simpa using PlusRestrictedRelativeModularData.phaseLift_fixed_by_phasePlusProjector R.plus ρ b

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.minus_phaseLift_fixed_by_phaseMinusProjector
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    phaseMinusProjector (E := H) (MinusRestrictedRelativeModularData.phaseLift R.minus ρ b)
      = MinusRestrictedRelativeModularData.phaseLift R.minus ρ b := by
  simpa using MinusRestrictedRelativeModularData.phaseLift_fixed_by_phaseMinusProjector R.minus ρ b

end Core

end InfoGeometry.Canonical.PhaseSpacePolarizedBridge
