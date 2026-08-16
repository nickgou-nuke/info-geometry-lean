import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hRe
    simp at hRe
  have hs1 : s - 1 ≠ 0 := by
    intro hs
    have hs' : s = 1 := sub_eq_zero.mp hs
    rw [hs'] at hRe'
    norm_num at hRe'
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hRe
  have hcompleted : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs0
    exact (eq_div_iff hGamma).mp h |>.symm
  unfold riemannXi
  rw [hcompleted]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact (hs0 h).elim
      · exact (hs1 h).elim
    · rcases mul_eq_zero.mp h with hZ | hG
      · exact hZ
      · exact (hGamma hG).elim
  · intro h
    simp [h]

noncomputable def riemannXiCayley (z : ℂ) : ℂ :=
  riemannXi (cayleyToTemperature z)

theorem cayleyToTemperature_inv_eq_one_sub
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    cayleyToTemperature z⁻¹ = 1 - cayleyToTemperature z := by
  unfold cayleyToTemperature
  field_simp [hz, hz']
  have hden : z + 1 ≠ 0 := by simpa [add_comm] using hz'
  rw [show 1 + z = z + 1 by ring, div_self hden]
  ring

theorem riemannXiCayley_inv_eq
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    riemannXiCayley z⁻¹ = riemannXiCayley z := by
  unfold riemannXiCayley
  rw [cayleyToTemperature_inv_eq_one_sub hz hz',
    InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi_one_sub]

/-- The Cayley-composed completed Xi zero locus is invariant under the
involution `z ↦ z⁻¹` on its domain. -/
theorem riemannXiCayley_zero_inv_iff
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    riemannXiCayley z⁻¹ = 0 ↔ riemannXiCayley z = 0 := by
  rw [riemannXiCayley_inv_eq hz hz']

theorem riemannXiCayley_zero_iff_riemannZeta_zero_of_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannZeta s = 0 ↔
      riemannXiCayley (cayleyToFugacity s) = 0 := by
  have hs1 : 1 - s ≠ 0 := by
    intro hs
    have hs' : s = 1 := (sub_eq_zero.mp hs).symm
    rw [hs'] at hRe'
    norm_num at hRe'
  rw [riemannXiCayley, cayleyToTemperature_cayleyToFugacity s hs1]
  exact (riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip hRe hRe').symm

end InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
