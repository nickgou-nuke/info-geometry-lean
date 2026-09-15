import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Mul

namespace InfoGeometry.Physics.ParticleGammaCorrelation

open Algebra.FiniteSpin

noncomputable section

def signedCorrelation (particle photon : Vec3R) (sign : ℝ) : ℝ :=
  sign * dotProduct particle photon

theorem correlation_difference (particle photon : Vec3R) :
    signedCorrelation particle photon 1 - signedCorrelation particle photon (-1) =
      2 * dotProduct particle photon := by
  unfold signedCorrelation
  ring

theorem correlation_separates_iff (particle photon : Vec3R) :
    signedCorrelation particle photon 1 ≠ signedCorrelation particle photon (-1) ↔
      dotProduct particle photon ≠ 0 := by
  rw [← sub_ne_zero, correlation_difference, mul_ne_zero_iff]
  simp

theorem correlation_simultaneous_reversal (particle photon : Vec3R) (sign : ℝ) :
    signedCorrelation (-particle) (-photon) sign = signedCorrelation particle photon sign := by
  simp only [signedCorrelation, neg_dotProduct_neg]

theorem nonzero_vectors_need_not_separate :
    ∃ particle photon : Vec3R, particle ≠ 0 ∧ photon ≠ 0 ∧
      signedCorrelation particle photon 1 = signedCorrelation particle photon (-1) := by
  refine ⟨![1, 0, 0], ![0, 1, 0], ?_, ?_, ?_⟩
  · intro equal
    have coordinate := congrFun equal 0
    norm_num at coordinate
  · intro equal
    have coordinate := congrFun equal 1
    norm_num at coordinate
  · norm_num [signedCorrelation, dotProduct, Fin.sum_univ_succ]

end

end InfoGeometry.Physics.ParticleGammaCorrelation
