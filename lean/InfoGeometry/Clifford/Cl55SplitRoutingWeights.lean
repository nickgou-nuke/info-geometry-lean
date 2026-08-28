import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic

open Filter Topology

namespace InfoGeometry.Clifford.Cl55SplitRoutingWeights

noncomputable def sigmoid (x : ℝ) : ℝ :=
  Real.exp x / (Real.exp x + 1)

theorem sigmoid_eq_real_sigmoid (x : ℝ) : sigmoid x = Real.sigmoid x := by
  unfold sigmoid Real.sigmoid
  rw [Real.exp_neg]
  field_simp

theorem sigmoid_tendsto_atTop : Tendsto sigmoid atTop (𝓝 (1 : ℝ)) := by
  have hfun : sigmoid = Real.sigmoid := funext sigmoid_eq_real_sigmoid
  rw [hfun]
  exact Real.tendsto_sigmoid_atTop

theorem sigmoid_tendsto_atBot : Tendsto sigmoid atBot (𝓝 (0 : ℝ)) := by
  have hfun : sigmoid = Real.sigmoid := funext sigmoid_eq_real_sigmoid
  rw [hfun]
  exact Real.tendsto_sigmoid_atBot

theorem sigmoid_add_neg (x : ℝ) : sigmoid x + sigmoid (-x) = 1 := by
  unfold sigmoid
  have hx : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  rw [Real.exp_neg]
  field_simp [hx]
  ring

noncomputable def normalizedPlus (t : ℝ) : ℝ := sigmoid (2 * t)

noncomputable def normalizedMinus (t : ℝ) : ℝ := sigmoid (-(2 * t))

theorem normalized_weights_sum (t : ℝ) :
    normalizedPlus t + normalizedMinus t = 1 := by
  exact sigmoid_add_neg (2 * t)

theorem normalizedPlus_eq_exp_ratio (t : ℝ) :
    normalizedPlus t = Real.exp t / (Real.exp t + Real.exp (-t)) := by
  unfold normalizedPlus sigmoid
  rw [show (2 : ℝ) * t = t - (-t) by ring, Real.exp_sub]
  have hneg : Real.exp (-t) ≠ 0 := ne_of_gt (Real.exp_pos (-t))
  field_simp [hneg]

theorem normalizedMinus_eq_exp_ratio (t : ℝ) :
    normalizedMinus t = Real.exp (-t) / (Real.exp t + Real.exp (-t)) := by
  unfold normalizedMinus sigmoid
  rw [show -(2 * t) = (-t) - t by ring, Real.exp_sub]
  have ht : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  field_simp [ht]
  ring

theorem normalizedPlus_tendsto_atTop :
    Tendsto normalizedPlus atTop (𝓝 (1 : ℝ)) := by
  exact sigmoid_tendsto_atTop.comp
    ((tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 2 by norm_num)).mpr tendsto_id)

theorem normalizedMinus_tendsto_atTop :
    Tendsto normalizedMinus atTop (𝓝 (0 : ℝ)) := by
  have harg : Tendsto (fun t : ℝ => -(2 * t)) atTop atBot := by
    simpa only [neg_mul] using
      (tendsto_neg_atTop_atBot.comp
        ((tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 2 by norm_num)).mpr tendsto_id))
  exact sigmoid_tendsto_atBot.comp harg

theorem normalizedPlus_tendsto_atBot :
    Tendsto normalizedPlus atBot (𝓝 (0 : ℝ)) := by
  have harg : Tendsto (fun t : ℝ => 2 * t) atBot atBot := by
    exact (tendsto_const_mul_atBot_of_pos (show (0 : ℝ) < 2 by norm_num)).mpr tendsto_id
  exact sigmoid_tendsto_atBot.comp harg

theorem normalizedMinus_tendsto_atBot :
    Tendsto normalizedMinus atBot (𝓝 (1 : ℝ)) := by
  have harg : Tendsto (fun t : ℝ => -(2 * t)) atBot atTop := by
    simpa only [neg_mul] using
      (tendsto_neg_atBot_atTop.comp
        ((tendsto_const_mul_atBot_of_pos (show (0 : ℝ) < 2 by norm_num)).mpr tendsto_id))
  exact sigmoid_tendsto_atTop.comp harg

end InfoGeometry.Clifford.Cl55SplitRoutingWeights
