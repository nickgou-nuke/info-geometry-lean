import Mathlib
import InfoGeometry.Canonical.WittenMoebiusChiralParityIndex

noncomputable section

namespace InfoGeometry.Canonical.MoebiusCore

open InfoGeometry.Canonical.WittenMoebiusChiralParityIndex
open InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-- **Definition**: Möbius Inversion Transform z ↦ -1/z on ℝ for non-zero points. -/
def moebiusInversion (z : ℝ) : ℝ :=
  - (1 / z)

/-- **Theorem**: Involution of Möbius Inversion (-1 / (-1 / z) = z). -/
theorem moebiusInversion_involutive (z : ℝ) (hz : z ≠ 0) :
    moebiusInversion (moebiusInversion z) = z := by
  dsimp [moebiusInversion]
  have h_ne : - (1 / z) ≠ 0 := by
    intro h0
    rw [neg_eq_zero, div_eq_zero_iff] at h0
    cases h0 with
    | inl h1 => norm_num at h1
    | inr h2 => exact hz h2
  field_simp


end InfoGeometry.Canonical.MoebiusCore
