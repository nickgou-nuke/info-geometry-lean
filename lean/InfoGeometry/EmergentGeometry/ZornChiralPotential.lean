import InfoGeometry.Algebra.ZornMatrix
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace InfoGeometry.EmergentGeometry.ZornChiralPotential

open InfoGeometry.Algebra

def positiveSlice (temporal : ℝ) (spatial : Vec3 ℝ) : ZornMatrix ℝ where
  a := temporal
  b := temporal
  v := spatial
  w := -spatial

theorem positiveSlice_norm (temporal : ℝ) (spatial : Vec3 ℝ) :
    ZornMatrix.zornNorm (positiveSlice temporal spatial) =
      temporal ^ 2 + Vec3.dot spatial spatial := by
  simp only [positiveSlice, ZornMatrix.zornNorm, Vec3.dot, Pi.neg_apply]
  ring

theorem positiveSlice_norm_nonneg (temporal : ℝ) (spatial : Vec3 ℝ) :
    0 ≤ ZornMatrix.zornNorm (positiveSlice temporal spatial) := by
  rw [positiveSlice_norm]
  unfold Vec3.dot
  nlinarith [sq_nonneg temporal, sq_nonneg (spatial 0), sq_nonneg (spatial 1),
    sq_nonneg (spatial 2)]

theorem sqrt_sub_spatial (temporal : ℝ) (spatial : Vec3 ℝ) :
    Real.sqrt (ZornMatrix.zornNorm (positiveSlice temporal spatial) - Vec3.dot spatial spatial) =
      |temporal| := by
  rw [positiveSlice_norm, add_sub_cancel_right, Real.sqrt_sq_eq_abs]

theorem sqrt_sub_spatial_of_nonneg (temporal : ℝ) (spatial : Vec3 ℝ)
    (temporal_nonneg : 0 ≤ temporal) :
    Real.sqrt (ZornMatrix.zornNorm (positiveSlice temporal spatial) - Vec3.dot spatial spatial) =
      temporal := by
  rw [sqrt_sub_spatial, abs_of_nonneg temporal_nonneg]

theorem positiveSlice_norm_not_injective :
    ¬ Function.Injective (fun spatial : Vec3 ℝ =>
      ZornMatrix.zornNorm (positiveSlice 1 spatial)) := by
  intro injective
  have equal : (positiveSlice 1 ![1, 0, 0]).zornNorm =
      (positiveSlice 1 ![0, 1, 0]).zornNorm := by
    norm_num [positiveSlice_norm, Vec3.dot, Matrix.cons_val_two]
  have vectors := injective equal
  have coordinate := congrFun vectors 0
  norm_num at coordinate

theorem zornNorm_can_be_negative :
    ∃ element : ZornMatrix ℝ, element.zornNorm < 0 := by
  refine ⟨{ a := 1, b := -1, v := 0, w := 0 }, ?_⟩
  norm_num [ZornMatrix.zornNorm, Vec3.dot]

end InfoGeometry.EmergentGeometry.ZornChiralPotential
