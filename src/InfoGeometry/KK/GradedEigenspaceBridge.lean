import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Physics.ChiralEigenspaceEquivalence

noncomputable section

namespace InfoGeometry.KK.GradedEigenspaceBridge

open InfoGeometry.Krein
open KreinGradedModule
open InfoGeometry.Physics.ChiralEigenspaceEquivalence

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert]
variable [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]
variable [KreinSpace Hilbert] [KreinGradedModule Hilbert]

theorem odd_anticommutes (operator : Hilbert →L[ℝ] Hilbert)
    (hodd : IsOdd operator) :
    operator.toLinearMap.comp (gradeCLM (H := Hilbert)).toLinearMap =
      -((gradeCLM (H := Hilbert)).toLinearMap.comp operator.toLinearMap) := by
  ext vector
  have hequality := congrArg
    (fun current : Hilbert →L[ℝ] Hilbert => current (grade (H := Hilbert) vector)) hodd
  have hreverse : grade (H := Hilbert) (operator vector) =
      -(operator (grade (H := Hilbert) vector)) := by
    simpa [gradeConj, grade_invol] using hequality
  change operator (grade (H := Hilbert) vector) = -(grade (H := Hilbert) (operator vector))
  simpa using (congrArg Neg.neg hreverse).symm

def oddEigenspaceEquiv (operator : Hilbert →L[ℝ] Hilbert)
    (hodd : IsOdd operator) (eigenvalue : ℝ) :
    Module.End.eigenspace operator.toLinearMap eigenvalue ≃ₗ[ℝ]
      Module.End.eigenspace operator.toLinearMap (-eigenvalue) :=
  eigenspaceEquiv operator.toLinearMap (gradeCLM (H := Hilbert)).toLinearMap
    (odd_anticommutes operator hodd) (by
      ext vector
      exact grade_invol vector) eigenvalue

variable {LeftAlgebra RightAlgebra : Type*}
variable [NormedRing LeftAlgebra] [NormedRing RightAlgebra]
variable [NormedAlgebra ℝ LeftAlgebra] [NormedAlgebra ℝ RightAlgebra]

def phaseEigenspaceEquiv
    (cycle : RealSplitKreinKasparovCycle LeftAlgebra RightAlgebra Hilbert)
    (eigenvalue : ℝ) :
    Module.End.eigenspace cycle.F.toLinearMap eigenvalue ≃ₗ[ℝ]
      Module.End.eigenspace cycle.F.toLinearMap (-eigenvalue) :=
  oddEigenspaceEquiv cycle.F cycle.F_odd eigenvalue

end InfoGeometry.KK.GradedEigenspaceBridge
