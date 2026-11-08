import InfoGeometry.Canonical.WeylGromovReadoutCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Canonical

/-!
# Conditional Weyl/GW density readout

This owner records only the elementary scalar consequence of an explicit
common-coordinate calibration.  It does not identify the common Weyl channel
with a partition function, and it does not assert a Jacobian, holography,
decoupling, or a KMS statement.
-/

variable {E : Type*}

noncomputable def weylTransportDensity
    (commonLogCoordinate : E → ℝ) (n : ℝ) (g : E) : ℝ :=
  Real.exp (n * commonLogCoordinate g)

noncomputable def partitionDensity
    (partition : E → ℝ) (n : ℝ) (g : E) : ℝ :=
  partition g ^ (n / 2)

theorem weylTransportDensity_eq_partitionDensity
    (commonLogCoordinate partition : E → ℝ)
    (g : E) (n : ℝ)
    (hcommon : commonLogCoordinate g = Real.log (partition g) / 2)
    (hpartition : 0 < partition g) :
    weylTransportDensity commonLogCoordinate n g =
      partitionDensity partition n g := by
  unfold weylTransportDensity partitionDensity
  rw [hcommon, Real.rpow_def_of_pos hpartition]
  congr 1
  ring

theorem partitionDensity_pos
    (partition : E → ℝ)
    (g : E) (n : ℝ)
    (hpartition : 0 < partition g) :
    0 < partitionDensity partition n g := by
  unfold partitionDensity
  exact Real.rpow_pos_of_pos hpartition _

theorem zero_scaled_readout
    (scale jacobian : ℝ) (hzero : jacobian = 0) :
    scale * jacobian = 0 := by
  rw [hzero, mul_zero]

end InfoGeometry.Canonical
