import InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG
import InfoGeometry.Algebra.SplitQuaternionMatrices

noncomputable section

namespace InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdGTests

open InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG
open InfoGeometry.Algebra.SplitQuaternionMatrices

def matrixAxes : SplitQuaternionPair (Matrix (Fin 2) (Fin 2) ℝ) where
  elliptic := sqI
  split := sqJ
  elliptic_sq := sqI_sq
  split_sq := sqJ_sq
  anticommute := by rw [sqI_mul_sqJ, sqJ_mul_sqI, neg_neg]

example : matrixAxes.third = sqK := sqI_mul_sqJ

example : matrixAxes.third * matrixAxes.third = 1 := matrixAxes.third_sq

example (core : InfoGeometry.Quantum.AnticommutingInvolutionCore) :
    (SplitQuaternionPair.ofInvolutionCore core).third *
      (SplitQuaternionPair.ofInvolutionCore core).third = 1 :=
  (SplitQuaternionPair.ofInvolutionCore core).third_sq

example : ((0 : ℝ) + 0) * (0 + 0) = 0 := by
  simpa using scalar_square_of_anticommutation (0 : ℝ) 0 0 0
    (by simp) (by simp) (by simp)

#print axioms InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG.SplitQuaternionPair.third_sq
#print axioms InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG.equilibrium_reduction
#print axioms InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG.scalar_square_of_anticommutation

end InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdGTests
