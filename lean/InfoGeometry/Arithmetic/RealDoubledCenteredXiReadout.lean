/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.RealDoubledDirichletReadout
import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Canonical.ActualNativeZetaCenteredXiBridge

/-!
# Concrete centered Xi in the existing real Hestenes representation

This file identifies the two-real-coordinate value readout with the existing
Hestenes scalar map, then transports the actual zeta/centered-Xi zero
equivalence in the open critical strip. It introduces no abstract zero chart.

The strip restriction is essential for the repository's totalized
`riemannXi = (1/2) * s * (s - 1) * completedRiemannZeta s`: its values at the
endpoints cannot be used as an unrestricted entire-Xi zero statement.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout

open InfoGeometry.Krein
open InfoGeometry.Arithmetic.RealDoubledDirichletReadout
open InfoGeometry.Canonical.HestenesComplexTranslation
open InfoGeometry.Canonical.ActualCenteredXiDataBridge
open InfoGeometry.Canonical.ActualNativeZetaDatumBridge
open InfoGeometry.Canonical.ActualNativeZetaCenteredXiBridge
open InfoGeometry.Canonical.MasterRH

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-coordinate map is exactly the existing Hestenes scalar map. -/
theorem scalarOp_eq_hestenesScalar (a b : ℝ) :
    scalarOp (E := E) a b = hestenesScalar (E := E) ⟨a, b⟩ := rfl

/-- Evaluate the actual centered Xi and represent its value over `ℝ`. -/
def centeredXiReadout (offset height : ℝ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  scalarOp (actualCenteredXiData.xi ⟨offset, height⟩).re
    (actualCenteredXiData.xi ⟨offset, height⟩).im

theorem centeredXiReadout_eq_zero_iff [Nontrivial E] (offset height : ℝ) :
    centeredXiReadout (E := E) offset height = 0 ↔
      actualCenteredXiData.xi ⟨offset, height⟩ = 0 := by
  rw [centeredXiReadout, scalarOp_eq_zero_iff]
  exact ⟨fun h => Complex.ext h.1 h.2,
    fun h => ⟨congrArg Complex.re h, congrArg Complex.im h⟩⟩

/-- The zero equivalence uses the concrete native arithmetic owner. -/
theorem zetaReadout_eq_zero_iff_centeredXiReadout_zero [Nontrivial E]
    (sigma height : ℝ) (h0 : 0 < sigma) (h1 : sigma < 1) :
    zetaReadout (E := E) sigma height = 0 ↔
      centeredXiReadout (E := E) (sigma - 1 / 2) height = 0 := by
  rw [zetaReadout_eq_zero_iff, centeredXiReadout_eq_zero_iff]
  have hs : (⟨sigma, height⟩ : ℂ) ∈ criticalStrip := ⟨h0, h1⟩
  have hcoord : (⟨sigma, height⟩ : ℂ) - (1 / 2 : ℂ) =
      ⟨sigma - 1 / 2, height⟩ := by
    apply Complex.ext <;> simp
  simpa only [actualNativeZetaDatum_zeta, hcoord] using
    actualNativeZetaDatum_strip_zero_iff_centeredXi_zero hs

/-- The actual Schwarz identity becomes real modular conjugation. -/
theorem modular_j_conjugates_centeredXiReadout (offset height : ℝ) :
    modular_j * centeredXiReadout (E := E) offset height * modular_j =
      centeredXiReadout offset (-height) := by
  have hc : actualCenteredXiData.xi (⟨offset, -height⟩ : ℂ) =
      star (actualCenteredXiData.xi (⟨offset, height⟩ : ℂ)) := by
    exact actualCenteredXiData_conj (⟨offset, height⟩ : ℂ)
  simp only [centeredXiReadout, modular_j_conjugates_scalarOp, hc]
  simp

end InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout
