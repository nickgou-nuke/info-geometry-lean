import InfoGeometry.Canonical.SuperchargeGapHessianBridge
import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ChiralHodgeDecomposition

Chiral Hodge package for the root doubled-carrier Dirac/supercharge lane.

This file stays owner-respecting:
- the chiral projectors are the existing spectral projectors `P± = (1 ± ε)/2`,
- the odd Dirac lane is the existing root operator `D := J`,
- the chiral arrows are the off-diagonal blocks `D⁺ = P₋ D P₊` and `D⁻ = P₊ D P₋`,
- the sector Laplace/Hodge loops are `Δ₊ = D⁻D⁺` and `Δ₋ = D⁺D⁻`,
- and the transported Lichnerowicz closure remains owned by the existing
  supercharge transport files.
-/

namespace InfoGeometry.Canonical.ChiralHodgeDecomposition

open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.SuperchargeGapHessianBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The chiral `ε = +1` projector on the doubled carrier. -/
@[rep_depth krein]
noncomputable abbrev spectralChiralPlusProjector : EndH := spectralPlusProj (E := E)

/-- The chiral `ε = -1` projector on the doubled carrier. -/
@[rep_depth krein]
noncomputable abbrev spectralChiralMinusProjector : EndH := spectralMinusProj (E := E)

/-- Root odd Dirac/supercharge lane on the doubled carrier. -/
@[rep_depth krein]
noncomputable abbrev rootDiracOddLane : EndH := modular_j (E := E)

/-- The `P₊ → P₋` chiral Dirac arrow. -/
@[rep_depth krein]
noncomputable abbrev rootDiracPlus : EndH :=
  (spectralChiralMinusProjector (E := E)).comp
    ((rootDiracOddLane (E := E)).comp (spectralChiralPlusProjector (E := E)))

/-- The `P₋ → P₊` chiral Dirac arrow. -/
@[rep_depth krein]
noncomputable abbrev rootDiracMinus : EndH :=
  (spectralChiralPlusProjector (E := E)).comp
    ((rootDiracOddLane (E := E)).comp (spectralChiralMinusProjector (E := E)))

/-- The positive-sector Hodge/Laplace loop `Δ₊ = D⁻D⁺`. -/
@[rep_depth krein]
noncomputable abbrev rootChiralLaplacianPlus : EndH :=
  (rootDiracMinus (E := E)).comp (rootDiracPlus (E := E))

/-- The negative-sector Hodge/Laplace loop `Δ₋ = D⁺D⁻`. -/
@[rep_depth krein]
noncomputable abbrev rootChiralLaplacianMinus : EndH :=
  (rootDiracPlus (E := E)).comp (rootDiracMinus (E := E))

@[rep_depth krein]
theorem rootDiracOddLane_is_spectral_odd :
    (spectral_epsilon (E := E)).comp (rootDiracOddLane (E := E))
      = -((rootDiracOddLane (E := E)).comp (spectral_epsilon (E := E))) := by
  simpa [rootDiracOddLane] using spectral_epsilon_comp_modular_j (E := E)

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem modular_j_plusPoint (x : E) :
    modular_j (plusPoint (E := E) x : H₂) = minusPoint (E := E) x := by
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint, modular_j_apply]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem modular_j_minusPoint (x : E) :
    modular_j (minusPoint (E := E) x : H₂) = plusPoint (E := E) x := by
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint, modular_j_apply]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem spectralChiralPlusProjector_apply_minusPoint (x : E) :
    spectralChiralPlusProjector (E := E) (minusPoint (E := E) x) = 0 := by
  rw [spectralPlusProj_apply_eq_plusPoint]
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem spectralChiralMinusProjector_apply_plusPoint (x : E) :
    spectralChiralMinusProjector (E := E) (plusPoint (E := E) x) = 0 := by
  rw [spectralMinusProj_apply_eq_minusPoint]
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint]

/-- Pointwise form of the `P₊ → P₋` chiral Dirac arrow. -/
@[rep_depth krein, simp] theorem rootDiracPlus_apply (u : H₂) :
    rootDiracPlus (E := E) u = minusPoint (E := E) (WithLp.fst u) := by
  rw [rootDiracPlus, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    spectralPlusProj_apply_eq_plusPoint, modular_j_plusPoint, spectralMinusProj_apply_eq_minusPoint]
  simp [minusPoint]

/-- Pointwise form of the `P₋ → P₊` chiral Dirac arrow. -/
@[rep_depth krein, simp] theorem rootDiracMinus_apply (u : H₂) :
    rootDiracMinus (E := E) u = plusPoint (E := E) (WithLp.snd u) := by
  rw [rootDiracMinus, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    spectralMinusProj_apply_eq_minusPoint, modular_j_minusPoint, spectralPlusProj_apply_eq_plusPoint]
  simp [plusPoint]

/-- The `P₊DP₊` diagonal block vanishes for the root odd Dirac lane. -/
@[rep_depth krein]
theorem rootDirac_plus_plus_block_eq_zero :
    (spectralChiralPlusProjector (E := E)).comp
        ((rootDiracOddLane (E := E)).comp (spectralChiralPlusProjector (E := E)))
      = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  change spectralPlusProj (E := E) (modular_j (spectralPlusProj (E := E) u)) = 0
  have hmod :
      modular_j (spectralPlusProj (E := E) u) = minusPoint (E := E) (WithLp.fst u) := by
    rw [spectralPlusProj_apply_eq_plusPoint, modular_j_plusPoint]
  rw [hmod, spectralChiralPlusProjector_apply_minusPoint]

/-- The `P₋DP₋` diagonal block vanishes for the root odd Dirac lane. -/
@[rep_depth krein]
theorem rootDirac_minus_minus_block_eq_zero :
    (spectralChiralMinusProjector (E := E)).comp
        ((rootDiracOddLane (E := E)).comp (spectralChiralMinusProjector (E := E)))
      = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  change spectralMinusProj (E := E) (modular_j (spectralMinusProj (E := E) u)) = 0
  have hmod :
      modular_j (spectralMinusProj (E := E) u) = plusPoint (E := E) (WithLp.snd u) := by
    rw [spectralMinusProj_apply_eq_minusPoint, modular_j_minusPoint]
  rw [hmod, spectralChiralMinusProjector_apply_plusPoint]

/-- The root odd Dirac lane splits into its two off-diagonal chiral arrows. -/
@[rep_depth krein]
theorem rootDiracOddLane_eq_chiral_sum :
    rootDiracOddLane (E := E) = rootDiracPlus (E := E) + rootDiracMinus (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.add_apply, rootDiracPlus_apply, rootDiracMinus_apply]
  change modular_j u = minusPoint (E := E) (WithLp.fst u) + plusPoint (E := E) (WithLp.snd u)
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint, modular_j_apply]

/-- The positive-sector Hodge loop is the `ε = +1` projector. -/
@[rep_depth krein]
theorem rootChiralLaplacianPlus_eq_spectralChiralPlusProjector :
    rootChiralLaplacianPlus (E := E) = spectralChiralPlusProjector (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  change rootDiracMinus (E := E) (rootDiracPlus (E := E) u) = spectralPlusProj (E := E) u
  rw [rootDiracPlus_apply, rootDiracMinus_apply, spectralPlusProj_apply_eq_plusPoint]
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint]

/-- The negative-sector Hodge loop is the `ε = -1` projector. -/
@[rep_depth krein]
theorem rootChiralLaplacianMinus_eq_spectralChiralMinusProjector :
    rootChiralLaplacianMinus (E := E) = spectralChiralMinusProjector (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  change rootDiracPlus (E := E) (rootDiracMinus (E := E) u) = spectralMinusProj (E := E) u
  rw [rootDiracMinus_apply, rootDiracPlus_apply, spectralMinusProj_apply_eq_minusPoint]
  apply DoubledSpace.ext <;> simp [plusPoint, minusPoint]

/-- The square of the root odd Dirac lane is the sum of the two chiral Hodge loops. -/
@[rep_depth krein]
theorem rootDiracOddLane_sq_eq_chiralLaplacian_sum :
    (rootDiracOddLane (E := E)).comp (rootDiracOddLane (E := E))
      =
    rootChiralLaplacianPlus (E := E) + rootChiralLaplacianMinus (E := E) := by
  calc
    (rootDiracOddLane (E := E)).comp (rootDiracOddLane (E := E))
      = ContinuousLinearMap.id ℝ H₂ := by
          simp [rootDiracOddLane]
    _ = spectralChiralPlusProjector (E := E) + spectralChiralMinusProjector (E := E) := by
          symm
          simpa [spectralChiralPlusProjector, spectralChiralMinusProjector] using
            spectralProj_sum (E := E)
    _ = rootChiralLaplacianPlus (E := E) + rootChiralLaplacianMinus (E := E) := by
          rw [rootChiralLaplacianPlus_eq_spectralChiralPlusProjector,
            rootChiralLaplacianMinus_eq_spectralChiralMinusProjector]

end Core

end InfoGeometry.Canonical.ChiralHodgeDecomposition
