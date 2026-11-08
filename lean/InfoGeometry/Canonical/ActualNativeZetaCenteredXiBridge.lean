import InfoGeometry.Canonical.ActualNativeZetaDatumBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualCenteredXiDataBridge

/-!
# Actual zeta/centered-Xi zero transport

This owner connects the concrete `NativeZetaDatum` zero equivalence to the
concrete centered `CompletedXiData` readout.  The bridge is only the affine
coordinate change `s = 1 / 2 + (s - 1 / 2)`; it adds no new analytic claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualNativeZetaCenteredXiBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.ActualCenteredXiDataBridge
open InfoGeometry.Canonical.ActualNativeZetaDatumBridge
open InfoGeometry.Canonical.NativeZeta
open InfoGeometry.Canonical.MasterRH

theorem actualNativeZetaDatum_strip_zero_iff_centeredXi_zero
    {s : ℂ} (hs : s ∈ criticalStrip) :
    actualNativeZetaDatum.zeta s = 0 ↔
      actualCenteredXiData.xi (s - (1 / 2 : ℂ)) = 0 := by
  rw [actualNativeZetaDatum_zeta, actualCenteredXiData_xi]
  have harg : (1 / 2 : ℂ) + (s - (1 / 2 : ℂ)) = s := by
    ring
  rw [harg]
  exact actualNativeZetaDatum_strip_zero_equivalence hs

theorem actualNativeZetaDatum_strip_zero_iff_centeredXi_zero_of_re_imag
    {s : ℂ} (hs : s ∈ criticalStrip) (u tau : ℝ)
    (hs_coord : s = (1 / 2 : ℂ) + u + Complex.I * tau) :
    actualNativeZetaDatum.zeta s = 0 ↔
      actualCenteredXiData.xi (u + Complex.I * tau) = 0 := by
  rw [actualNativeZetaDatum_strip_zero_iff_centeredXi_zero hs]
  rw [hs_coord]
  dsimp [actualCenteredXiData]
  ring_nf

end InfoGeometry.Canonical.ActualNativeZetaCenteredXiBridge
