/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CFT.VirasoroVOAZeta
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# The first resonant central defect outside the Virasoro `sl₂` wedge

The mode pair `(1,-1)` has no central correction, while `(2,-2)` differs from
its Witt component by a nonzero multiple of the central generator.  These are
specializations of the actual Virasoro central-extension bracket, not a claim
about zeta scaling or a numerical central charge representation.
-/

namespace InfoGeometry.Canonical.VirasoroVOAZetaCapstone

open VirasoroProject.VirasoroAlgebra

/-- The lowest resonant wedge bracket has no central contribution. -/
theorem wedge_resonance_has_zero_central_component :
    ⁅lgen ℝ 1, lgen ℝ (-1)⁆ = (2 : ℝ) • lgen ℝ 0 := by
  rw [lgen_bracket]
  norm_num

/-- The first resonant bracket beyond the wedge has the exact central defect. -/
theorem first_outer_resonance_central_defect :
    ⁅lgen ℝ 2, lgen ℝ (-2)⁆ - (4 : ℝ) • lgen ℝ 0 =
      (1 / 2 : ℝ) • cgen ℝ := by
  rw [lgen_bracket]
  norm_num

/-- The mode-two resonance cannot reduce to its Witt component. -/
theorem first_outer_resonance_is_not_witt_bracket :
    ⁅lgen ℝ 2, lgen ℝ (-2)⁆ ≠ (4 : ℝ) • lgen ℝ 0 := by
  intro h
  have hdefect := first_outer_resonance_central_defect
  rw [h] at hdefect
  have hzero : (1 / 2 : ℝ) • cgen ℝ = 0 := by
    calc
      (1 / 2 : ℝ) • cgen ℝ =
          (4 : ℝ) • lgen ℝ 0 - (4 : ℝ) • lgen ℝ 0 := hdefect.symm
      _ = 0 := sub_self _
  have hc : cgen ℝ ≠ 0 := by
    intro hc
    have hs := congrArg
      (fun z : VirasoroProject.VirasoroAlgebra ℝ => z.snd) hc
    have hunit : (cgen ℝ).snd = 1 := by
      rw [VirasoroProject.VirasoroAlgebra.cgen_eq']
    rw [hunit] at hs
    change (1 : ℝ) = 0 at hs
    norm_num at hs
  rcases smul_eq_zero.mp hzero with hhalf | hc0
  · norm_num at hhalf
  · exact hc hc0

end InfoGeometry.Canonical.VirasoroVOAZetaCapstone
