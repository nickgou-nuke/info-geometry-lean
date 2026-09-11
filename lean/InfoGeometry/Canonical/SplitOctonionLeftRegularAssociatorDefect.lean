import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

/-! The ambient carrier is only a rational vector space.  We lift its native
split-octonion multiplication to a linear operator; no associative ring
structure is introduced on the ambient carrier. -/
def leftMulOp (x : StandardRationalSplitOctonion) :
    StandardRationalSplitOctonion →ₗ[ℚ] StandardRationalSplitOctonion where
  toFun := fun z => splitOctonionMulQ x z
  map_add' := by
    intro y z
    exact splitOctonionMulQ_add_right x y z
  map_smul' := by
    intro a y
    exact splitOctonionMulQ_smul_right a x y

/-- Left multiplication restricted to an associative coloured core. -/
def colorCoreLeftMul
    (c : SplitOctonionColour)
    (x : colorCore c) :
    colorCore c →ₗ[ℚ] colorCore c where
  toFun := fun z =>
    ⟨splitOctonionMulQ x.1 z.1, colorCore_closed_mul c x.2 z.2⟩
  map_add' := by
    intro y z
    ext b
    exact congrFun (splitOctonionMulQ_add_right x.1 y.1 z.1) b
  map_smul' := by
    intro a y
    ext b
    exact congrFun (splitOctonionMulQ_smul_right a x.1 y.1) b

/-- The associator defect internal to one coloured core. -/
def colorCoreAssociatorOp
    (c : SplitOctonionColour)
    (x y : colorCore c) :
    colorCore c →ₗ[ℚ] colorCore c :=
  colorCoreLeftMul c
      ⟨splitOctonionMulQ x.1 y.1, colorCore_closed_mul c x.2 y.2⟩ -
    (colorCoreLeftMul c x).comp (colorCoreLeftMul c y)

@[simp] theorem colorCoreAssociatorOp_eq_zero
    (c : SplitOctonionColour)
    (x y : colorCore c) :
    colorCoreAssociatorOp c x y = 0 := by
  ext z b
  change splitOctonionMulQ (splitOctonionMulQ x.1 y.1) z.1 b -
      splitOctonionMulQ x.1 (splitOctonionMulQ y.1 z.1) b = 0
  calc
    _ = splitOctonionMulQ x.1 (splitOctonionMulQ y.1 z.1) b -
        splitOctonionMulQ x.1 (splitOctonionMulQ y.1 z.1) b := by
          rw [congrFun (colorCore_mul_assoc c x.2 y.2 z.2) b]
    _ = 0 := sub_self _

theorem colorCoreLeftRegular_map_mul
    (c : SplitOctonionColour)
    (x y : colorCore c) :
    (colorCoreLeftMul c x).comp (colorCoreLeftMul c y) =
      colorCoreLeftMul c
        ⟨splitOctonionMulQ x.1 y.1, colorCore_closed_mul c x.2 y.2⟩ := by
  have h := colorCoreAssociatorOp_eq_zero c x y
  exact (sub_eq_zero.mp h).symm

end
end InfoGeometry.Canonical
