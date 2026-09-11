import InfoGeometry.Canonical.WeylGaugeAsanoEndpointBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.AsanoRuelle.MobiusPoleScaleAction

/-!
# Coherence of the affine Möbius scale owners

The repository contains two theorem-safe presentations of the same affine
dilation: the legacy complex-parameter `weylGaugeAction`/`weylGaugeOrbit`
readout and the canonical real-unit `poleScale`/`poleScaleAction` owner.
This file supplies only their exact real-unit comparison.  It does not add a
Weyl metric, a compactification, or a colimit construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeylGaugeAsanoScaleCoherence

open InfoGeometry.AsanoRuelle
open InfoGeometry.Canonical.WeylGaugeAsanoEndpoint

theorem weylGaugeAction_realUnit_eq_poleScale
    (C D : ℂ) (lam : ℝˣ) (z : ℂ) :
    weylGaugeAction C D (lam : ℂ) z =
      poleScale (-(C / D)) (lam : ℝ) z := by
  simp [weylGaugeAction, poleScale]
  ring

theorem weylGaugeOrbit_realUnit_eq_poleScalePoint
    (C D : ℂ) (lam : ℝˣ) (v : ℂ) :
    weylGaugeOrbit C D (lam : ℂ) v =
      poleScalePoint C D (lam : ℝ) v := by
  simp [weylGaugeOrbit, poleScalePoint]
  ring

theorem weylGaugeAction_realUnit_eq_poleScaleAction
    (C D : ℂ) (lam : ℝˣ) (z : ℂ) :
    weylGaugeAction C D (lam : ℂ) z =
      poleScaleAction (-(C / D)) lam z := by
  rw [weylGaugeAction_realUnit_eq_poleScale]
  rfl

theorem weylGaugeOrbit_realUnit_eq_poleScaleAction_polePoint
    (C D : ℂ) (lam : ℝˣ) (v : ℂ) :
    weylGaugeOrbit C D (lam : ℂ) v =
      poleScaleAction (-(C / D)) lam (-(C / D) + v) := by
  rw [weylGaugeOrbit_realUnit_eq_poleScalePoint]
  symm
  exact poleScaleAction_polePoint C D lam v

end InfoGeometry.Canonical.WeylGaugeAsanoScaleCoherence
