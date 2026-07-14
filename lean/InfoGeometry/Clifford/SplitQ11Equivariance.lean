import InfoGeometry.Clifford.SplitQ11Projectors
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Clifford.SplitQ11Equivariance

Mathlib-canonical phase-flip equivariance on the split `Cl(1,1)` atom.

This file keeps the story entirely algebraic. It does not postulate
projector/anomaly language as primitives; it derives the first fixed and
anti-fixed combinations directly from the canonical `K`-axis phase flip.
-/

namespace SplitQ11Equivariance

open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors

/-- The phase-flip residual of an element of split `Cl(1,1)`. -/
@[rep_depth krein]
noncomputable def phaseFlipResidual (x : Alg) : Alg :=
  phaseFlipAlg x - x

/-- The projector sum is fixed by the canonical phase flip. -/
@[rep_depth krein, simp] theorem phaseFlip_apply_epsProjector_sum :
    phaseFlipAlg (epsMinusProjector + epsPlusProjector)
      = epsMinusProjector + epsPlusProjector := by
  rw [map_add, phaseFlip_apply_epsMinusProjector, phaseFlip_apply_epsPlusProjector]
  simp [add_comm]

/-- The projector difference is anti-fixed by the canonical phase flip. -/
@[rep_depth krein, simp] theorem phaseFlip_apply_epsProjector_diff :
    phaseFlipAlg (epsMinusProjector - epsPlusProjector)
      = -(epsMinusProjector - epsPlusProjector) := by
  calc
    phaseFlipAlg (epsMinusProjector - epsPlusProjector)
        = epsPlusProjector - epsMinusProjector := by
            simp [sub_eq_add_neg]
    _ = -(epsMinusProjector - epsPlusProjector) := by
          abel_nf

/-- The projector difference is exactly the negative pseudoscalar `-ε`. -/
@[rep_depth krein, simp] theorem epsProjector_diff_eq_neg_epsGen :
    epsMinusProjector - epsPlusProjector = -epsGen := by
  rw [epsMinusProjector_eq_half_one_sub_eps, epsPlusProjector_eq_half_one_add_eps]
  simp [sub_eq_add_neg, smul_add]
  module

/-- The phase-flip residual vanishes on the fixed projector sum. -/
@[rep_depth krein, simp] theorem phaseFlipResidual_epsProjector_sum :
    phaseFlipResidual (epsMinusProjector + epsPlusProjector) = 0 := by
  unfold phaseFlipResidual
  rw [phaseFlip_apply_epsProjector_sum, sub_self]

/-- The phase-flip residual of the projector difference is `-2` times that difference. -/
@[rep_depth krein, simp] theorem phaseFlipResidual_epsProjector_diff :
    phaseFlipResidual (epsMinusProjector - epsPlusProjector)
      = -((2 : ℝ) • (epsMinusProjector - epsPlusProjector)) := by
  unfold phaseFlipResidual
  rw [phaseFlip_apply_epsProjector_diff]
  module

/-- The phase-flip residual of `ε` is `-2 ε`. -/
@[rep_depth krein, simp] theorem phaseFlipResidual_epsGen :
    phaseFlipResidual epsGen = -((2 : ℝ) • epsGen) := by
  unfold phaseFlipResidual
  rw [phaseFlip_apply_epsGen]
  module

end SplitQ11Equivariance
