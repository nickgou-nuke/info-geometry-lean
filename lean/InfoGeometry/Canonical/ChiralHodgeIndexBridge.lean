import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ChiralHodgeIndexBridge

Thin bridge from the root chiral Hodge square to the canonical finite
analytical-index lane.
-/

namespace ChiralHodgeIndexBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.ChiralHodgeDecomposition
open InfoGeometry.Canonical.AnalyticalIndex

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →ₗ[ℝ] H₂

omit [CompleteSpace E] in
/-- The canonical analytical-index positive projector is the root `ε = +1` projector. -/
@[rep_depth krein]
theorem root_chiralProjectorPlus_eq_spectralChiralPlusProjector :
    chiralProjectorPlus ((spectral_epsilon (E := E)).toLinearMap)
      = (spectralChiralPlusProjector (E := E)).toLinearMap := by
  ext u <;>
    simp [chiralProjectorPlus, spectralChiralPlusProjector, spectralPlusProj,
      spectral_epsilon_apply, one_div]

omit [CompleteSpace E] in
/-- The canonical analytical-index negative projector is the root `ε = -1` projector. -/
@[rep_depth krein]
theorem root_chiralProjectorMinus_eq_spectralChiralMinusProjector :
    chiralProjectorMinus ((spectral_epsilon (E := E)).toLinearMap)
      = (spectralChiralMinusProjector (E := E)).toLinearMap := by
  ext u <;>
    simp [chiralProjectorMinus, spectralChiralMinusProjector, spectralMinusProj,
      spectral_epsilon_apply, one_div]

/-- The root bulk Dirac lane has trivial kernel because `D² = Id`. -/
@[rep_depth krein]
theorem rootDiracOddLane_kernel_eq_bot :
    LinearMap.ker (rootDiracOddLane (E := E)).toLinearMap = ⊥ := by
  change LinearMap.ker ((modular_j (E := E)).toLinearMap) = ⊥
  exact LinearMap.ker_eq_bot_of_injective (modular_jLE (E := E)).injective

/-- The positive chiral kernel slice of the root bulk Dirac lane is trivial. -/
@[rep_depth krein]
theorem rootDiracOddLane_chiralKernelSlicePlus_eq_bot :
    chiralKernelSlicePlus
        (rootDiracOddLane (E := E)).toLinearMap
        ((spectral_epsilon (E := E)).toLinearMap)
      = ⊥ := by
  unfold chiralKernelSlicePlus
  rw [rootDiracOddLane_kernel_eq_bot (E := E)]
  simp

/-- The negative chiral kernel slice of the root bulk Dirac lane is trivial. -/
@[rep_depth krein]
theorem rootDiracOddLane_chiralKernelSliceMinus_eq_bot :
    chiralKernelSliceMinus
        (rootDiracOddLane (E := E)).toLinearMap
        ((spectral_epsilon (E := E)).toLinearMap)
      = ⊥ := by
  unfold chiralKernelSliceMinus
  rw [rootDiracOddLane_kernel_eq_bot (E := E)]
  simp

/-- The root bulk Dirac lane has zero analytical index on finite-dimensional doubled carriers. -/
@[rep_depth krein]
theorem rootDiracOddLane_analyticalIndex_eq_zero
    [FiniteDimensional ℝ E] :
    analyticalIndex
        (rootDiracOddLane (E := E)).toLinearMap
        ((spectral_epsilon (E := E)).toLinearMap)
      = 0 := by
  unfold analyticalIndex
  rw [rootDiracOddLane_chiralKernelSlicePlus_eq_bot (E := E),
    rootDiracOddLane_chiralKernelSliceMinus_eq_bot (E := E)]
  simp

end Core

end ChiralHodgeIndexBridge
