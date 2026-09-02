import Mathlib.RingTheory.GradedAlgebra.Basic
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge

/-! Native graded creation/projector transport on the three-mode exterior
algebra.  This uses Mathlib's graded-algebra projection, not coordinate
case-splitting. -/
namespace InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

noncomputable section
open scoped DirectSum
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

abbrev V3 := Fin 3 → ℝ
abbrev Exterior3 := ExteriorAlgebra ℝ V3
abbrev Exterior3End := Module.End ℝ Exterior3

def nativeExteriorProjector (k : ℕ) : Exterior3End :=
  GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) k

theorem exteriorGenerator_mem_degreeOne (v : V3) :
    ExteriorAlgebra.ι ℝ v ∈ (⋀[ℝ]^1 V3) := by
  simpa only [pow_one] using
    LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ : V3 →ₗ[ℝ] Exterior3) v

theorem nativeExteriorProjector_wedge_shift (v : V3) (k : ℕ) :
    (nativeExteriorProjector (k + 1)).comp (exteriorWedge3 v) =
      (exteriorWedge3 v).comp (nativeExteriorProjector k) := by
  apply LinearMap.ext
  intro x
  change GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) (k + 1)
      (ExteriorAlgebra.ι ℝ v * x) =
    ExteriorAlgebra.ι ℝ v *
      GradedAlgebra.proj (fun n : ℕ => ⋀[ℝ]^n V3) k x
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply]
  rw [show k + 1 = 1 + k by omega]
  exact DirectSum.coe_decompose_mul_add_of_left_mem
    (fun n : ℕ => ⋀[ℝ]^n V3) (exteriorGenerator_mem_degreeOne v)

theorem nativeExteriorProjector_wedge_shift_apply
    (v : V3) (k : ℕ) (x : Exterior3) :
    nativeExteriorProjector (k + 1) (exteriorWedge3 v x) =
      exteriorWedge3 v (nativeExteriorProjector k x) := by
  exact congrArg (fun T : Exterior3End => T x)
    (nativeExteriorProjector_wedge_shift v k)

/-! The first contraction boundary is available directly from Mathlib's
contraction API.  This is the honest endpoint before a general contraction
grading theorem: it records the annihilation of the vacuum without assuming a
Hodge-factorisation of contraction. -/
theorem exteriorContract3_vacuum (φ : Module.Dual ℝ V3) :
    exteriorContract3 φ (1 : Exterior3) = 0 := by
  exact CliffordAlgebra.contractLeft_one
    (Q := (0 : QuadraticForm ℝ V3)) φ

end
end InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge
