import InfoGeometry.Projective.SplitOctonions.ZornFlowRelativeVolume
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Zorn determinant-only base projection

This file packages the theorem-safe determinant/RN/log-volume cross-section of the
projective Zorn lane.

Closed content:
- determinant-ratio base projection;
- identity/cocycle laws;
- determinant-scaling and determinant-preserving specializations;
- negative-log barrier difference.

Open residue:
- no trace closure theorem;
- no measure-theoretic pushforward/pullback RN theorem;
- no infinite-limit/Fuglede-Kadison claim.
-/

namespace InfoGeometry.Projective.SplitOctonions

noncomputable section

namespace ZornCell

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- Determinant-only base projection from `X` to `Y`. -/
def baseProjection
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V) : ℝ :=
  flowRelativeVolumeRN B X Y

/-- `baseProjection` is definitionally the existing flow RN-style factor. -/
theorem baseProjection_eq_flowRelativeVolumeRN
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V) :
    baseProjection B X Y = flowRelativeVolumeRN B X Y :=
  rfl

/-- The determinant-only base projection of a point to itself is `1`. -/
theorem baseProjection_self
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    baseProjection B X X = 1 := by
  simpa [baseProjection] using flowRelativeVolumeRN_self B X hX

/-- Determinant-ratio cocycle for determinant-only base projection. -/
theorem baseProjection_comp
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y Z : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0)
    (hY : ZornCell.detZ B Y ≠ 0) :
    baseProjection B X Z =
      baseProjection B X Y * baseProjection B Y Z := by
  simpa [baseProjection] using flowRelativeVolumeRN_comp B X Y Z hX hY

/-- A determinant scaling law gives the corresponding base projection factor. -/
theorem baseProjection_of_det_scale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X scaledX : ZornCell ℝ V)
    (χ : ℝ)
    (hX : ZornCell.detZ B X ≠ 0)
    (h_scale : ZornCell.detZ B scaledX = χ * ZornCell.detZ B X) :
    baseProjection B X scaledX = χ := by
  simpa [baseProjection] using
    flowRelativeVolumeRN_of_det_scale B X scaledX χ hX h_scale

/-- Equal determinant gives trivial determinant-only base projection factor. -/
theorem baseProjection_det_preserving
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0)
    (h_pres : ZornCell.detZ B Y = ZornCell.detZ B X) :
    baseProjection B X Y = 1 := by
  simpa [baseProjection] using
    flowRelativeVolumeRN_det_preserving B X Y hX h_pres

/-- Scalar-square determinant scaling gives determinant-only base projection `u²`. -/
theorem baseProjection_scalarScale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X scaledX : ZornCell ℝ V)
    (u : ℝ)
    (hX : ZornCell.detZ B X ≠ 0)
    (h_scale : ZornCell.detZ B scaledX = u ^ 2 * ZornCell.detZ B X) :
    baseProjection B X scaledX = u ^ 2 := by
  simpa [baseProjection] using
    flowRelativeVolumeRN_scalarScale B X scaledX u hX h_scale

/-- Negative log base projection is the Zorn log-barrier difference. -/
theorem negLog_baseProjection_eq_zornLogBarrier_sub
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X)
    (hY : 0 < ZornCell.detZ B Y) :
    - Real.log (baseProjection B X Y) =
      zornLogBarrier B Y - zornLogBarrier B X := by
  simpa [baseProjection] using
    zornLogBarrier_flowDifference B X Y hX hY

end ZornCell

end

end InfoGeometry.Projective.SplitOctonions
