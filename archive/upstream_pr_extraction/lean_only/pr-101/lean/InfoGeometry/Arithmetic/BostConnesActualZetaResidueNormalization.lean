import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

open scoped Topology

namespace InfoGeometry.Arithmetic.BostConnesActualZetaResidueNormalization

open Filter
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

/-!
# Actual right-hand residue normalization for `riemannZeta`

This is the exact first-order consequence of the already proved real Laurent
remainder at `1`.  It is not an asymptotic formula for the Fisher metric or
for derivatives of `riemannZeta`.
-/

theorem actualRiemannZeta_residue_normalization_right :
    Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) * riemannZeta β)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hβ : Tendsto (fun β : ℝ => ((β - 1 : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcoe : Tendsto (fun β : ℝ => (β : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds
    simpa using hcoe.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)))
  have hrem := actualRiemannZeta_sub_one_div_tendsto_nhds_right
  have hprod : Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) *
        (riemannZeta β - 1 / ((β - 1 : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hβ.mul hrem
  have hsum : Tendsto
      (fun β : ℝ => 1 + ((β - 1 : ℝ) : ℂ) *
        (riemannZeta β - 1 / ((β - 1 : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using tendsto_const_nhds.add hprod
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβpos
  have hβpos' : 1 < β := hβpos
  have hne : (β - 1 : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr hβpos')
  have hne' : ((β - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hne
  rw [mul_sub]
  field_simp [hne']
  ring

theorem partitionSeries_residue_normalization_right :
    Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) *
        partitionSeries (β : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  apply actualRiemannZeta_residue_normalization_right.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : 1 < β := hβ
  have hpart : partitionSeries (β : ℂ) = riemannZeta (β : ℂ) := by
    apply partitionSeries_eq_riemannZeta
    simpa using hβ'
  rw [hpart]

theorem actualRiemannZeta_residue_inverse_normalization_right :
    Tendsto
      (fun β : ℝ =>
        (((β - 1 : ℝ) : ℂ) * riemannZeta β)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  simpa using
    actualRiemannZeta_residue_normalization_right.inv₀ one_ne_zero

theorem partitionSeries_residue_inverse_normalization_right :
    Tendsto
      (fun β : ℝ =>
        (((β - 1 : ℝ) : ℂ) * partitionSeries (β : ℂ))⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  simpa using
    partitionSeries_residue_normalization_right.inv₀ one_ne_zero

end InfoGeometry.Arithmetic.BostConnesActualZetaResidueNormalization
