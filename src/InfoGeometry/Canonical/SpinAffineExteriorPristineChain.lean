import InfoGeometry.Physics.SpinAffineCasimirRigidity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ExteriorZornCARIntertwiner
import InfoGeometry.Algebra.Zorn.SplitIdempotentTorus

/-!
# Spin affine frames, exterior CAR, and reflection: corrected combined statements

This module is a small native capstone.  It combines already-owned affine,
exterior-CAR, and negative-Clifford results without identifying their carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinAffineExteriorPristineChain

open InfoGeometry.Algebra.AffineOperatorFrame
open InfoGeometry.Physics.SpinAffineCasimirRigidity
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Clifford.ExteriorNegativeCliffordReflection
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

theorem affine_recovery_packet (M : FrameMatrixˣ) (b : Fin 3 → ℝ) :
    matrixFrame (↑(M⁻¹) : FrameMatrix)
        (affineFrame (↑M) b spinFrame - centralOffset b) = spinFrame ∧
      operatorQuadratic
        ((↑(M⁻¹) : FrameMatrix).transpose * (↑(M⁻¹) : FrameMatrix))
        (affineFrame (↑M) b spinFrame - centralOffset b) =
          (3 / 4 : ℂ) • (1 : SpinMatrix) :=
  ⟨inverse_affineFrame M b spinFrame, affine_spin_casimir M b⟩

theorem exterior_circular_CAR_packet (v : V3) (j : Fin 3) (ψ : Exterior3) :
    exteriorCircularCARLinearEquiv (exteriorWedge3 v ψ) =
        circularOperatorReadout (creationMap v) (exteriorCircularCARLinearEquiv ψ) ∧
      exteriorCircularCARLinearEquiv (exteriorContract3 (LinearMap.proj j) ψ) =
        circularOperatorReadout (annihilate j) (exteriorCircularCARLinearEquiv ψ) ∧
      exteriorCircularCARLinearEquiv (exteriorGrade3 ψ) =
        circularOperatorReadout regularParity (exteriorCircularCARLinearEquiv ψ) :=
  ⟨circular_creation_intertwiner v ψ, circular_annihilation_intertwiner j ψ,
    circular_parity_intertwiner ψ⟩

theorem negative_reflection_packet (n v : V3) (hn : dotBilin n n = 1) (ψ : Exterior3) :
    (reflectionUnit n hn : Exterior3End) * reflectionUnit n hn = -1 ∧
      gamma n * gamma v * gamma n = gamma (planeReflection n v) ∧
      exteriorGrade3 (gamma v ψ) = -(gamma v (exteriorGrade3 ψ)) :=
  ⟨reflectionUnit_sq n hn, gamma_reflection n v hn, gamma_odd v ψ⟩

end InfoGeometry.Canonical.SpinAffineExteriorPristineChain
