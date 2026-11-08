import InfoGeometry.Algebra.IwasawaRealKAN
import InfoGeometry.Volume.RealUnitScaleParity

/-!
# The determinant character of the concrete `SL(2, ℝ)` KAN product

The KAN matrices in `IwasawaRealKAN` are special linear matrices. Thus their
coordinate dilation in the `A` factor is not a nontrivial determinant scale:
the total determinant character has scale one and even parity.
-/

namespace InfoGeometry.Volume.IwasawaScaleParityBridge

open InfoGeometry.Algebra.IwasawaRealKAN
open InfoGeometry.Volume.RealUnitScaleParity

/-- Package the determinant of the concrete KAN product as a real unit. -/
noncomputable def kanDetUnit (θ t ξ : ℝ) : ℝˣ :=
  Units.mk0 (kanMatrix θ t ξ).det (by rw [kan_det]; norm_num)

/-- The determinant unit of the KAN product is the identity unit. -/
theorem kanDetUnit_eq_one (θ t ξ : ℝ) : kanDetUnit θ t ξ = 1 := by
  apply Units.ext
  simp [kanDetUnit, kan_det]

/-- In the concrete `SL(2, ℝ)` KAN chart, both the positive determinant scale
and the determinant parity are trivial. The hyperbolic coordinate dilation is
volume preserving because its two diagonal weights are reciprocal. -/
theorem kan_scaleParity_trivial (θ t ξ : ℝ) :
    realUnitScaleParityEquiv (kanDetUnit θ t ξ) = 1 := by
  rw [kanDetUnit_eq_one]
  simp [realUnitScaleParityEquiv, scaleParityEquiv, scaleParityHom,
    scaleComponent, absUnits, signUnits, signTypeUnitEquivZModTwo]

end InfoGeometry.Volume.IwasawaScaleParityBridge
