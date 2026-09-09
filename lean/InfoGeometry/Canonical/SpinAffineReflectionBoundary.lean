import InfoGeometry.Physics.SpinAffineCasimirRigidity
import InfoGeometry.Clifford.ExteriorNegativeCliffordReflection

/-!
# Certified affine and exterior-reflection boundary

This is the valid subcone of the historical spin/affine packet.  The
state-space intertwiner is deliberately not imported here because its current
owner still has unresolved coordinate and inverse-equivalence obligations.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinAffineReflectionBoundary

open InfoGeometry.Algebra.AffineOperatorFrame
open InfoGeometry.Physics.SpinAffineCasimirRigidity
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Clifford.ExteriorNegativeCliffordReflection

theorem affine_recovery (M : FrameMatrixˣ) (b : Fin 3 → ℝ) :
    matrixFrame (↑(M⁻¹) : FrameMatrix)
        (affineFrame (↑M) b spinFrame - centralOffset b) = spinFrame :=
  inverse_affineFrame M b spinFrame

theorem affine_casimir (M : FrameMatrixˣ) (b : Fin 3 → ℝ) :
    operatorQuadratic
        ((↑(M⁻¹) : FrameMatrix).transpose * (↑(M⁻¹) : FrameMatrix))
        (affineFrame (↑M) b spinFrame - centralOffset b) =
          (3 / 4 : ℂ) • (1 : SpinMatrix) :=
  affine_spin_casimir M b

theorem reflection_square (n : V3) (hn : dotBilin n n = 1) :
    (reflectionUnit n hn : Exterior3End) * reflectionUnit n hn = -1 :=
  reflectionUnit_sq n hn

theorem reflection_vector (n v : V3) (hn : dotBilin n n = 1) :
    gamma n * gamma v * gamma n = gamma (planeReflection n v) := by
  exact gamma_reflection n v hn

end InfoGeometry.Canonical.SpinAffineReflectionBoundary
