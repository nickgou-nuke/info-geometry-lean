import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarCriticalPhase
import InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge
import Mathlib.Tactic

/-!
# Critical-line windows and translated vortex carriers

A marked point on the critical line is not automatically a vortex of the base
bipolar logarithmic form `dq/q`; that form is singular only at `0` and `1`.
This file therefore separates:

* critical-line nodes `1/2 + iγ`;
* windows between ordered node heights;
* genuine critical-line zero readouts, supplied by an explicit zero hypothesis;
* an optional translated logarithmic pole `1/(z-ρ)` attached to a marked node.

No Riemann-hypothesis statement and no automatic identification of a zero with
an Aharonov--Bohm vortex is made.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCriticalWindowsVortex

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-- A marked point at height `γ` on the critical line. -/
def criticalNode (γ : ℝ) : ℂ := criticalLine γ

@[simp] theorem criticalNode_re (γ : ℝ) : (criticalNode γ).re = 1 / 2 :=
  criticalLine_re γ

@[simp] theorem criticalNode_im (γ : ℝ) : (criticalNode γ).im = γ :=
  criticalLine_im γ

/-- Every critical node avoids the two original punctures. -/
theorem criticalNode_mem_punctured01 (γ : ℝ) : criticalNode γ ∈ punctured01 :=
  criticalLine_mem_punctured01 γ

/-- Hence the base bipolar logarithmic differential is regular and nonzero there. -/
theorem base_dlog_nonzero_at_criticalNode (γ : ℝ) :
    dlog01 (criticalNode γ) ≠ 0 := by
  rw [dlog01_eq_one_div_mul (criticalNode_mem_punctured01 γ)]
  exact one_div_ne_zero
    (mul_ne_zero (criticalLine_ne_zero γ)
      (one_sub_ne_zero_of_mem (criticalNode_mem_punctured01 γ)))

/-- An open interval between two ordered critical-line heights. -/
structure CriticalWindow where
  lower : ℝ
  upper : ℝ
  ordered : lower < upper

namespace CriticalWindow

/-- Lower endpoint node. -/
def lowerNode (W : CriticalWindow) : ℂ := criticalNode W.lower

/-- Upper endpoint node. -/
def upperNode (W : CriticalWindow) : ℂ := criticalNode W.upper

/-- The two endpoint nodes are distinct. -/
theorem nodes_ne (W : CriticalWindow) : W.lowerNode ≠ W.upperNode := by
  intro h
  have him : W.lower = W.upper := by
    have := congrArg Complex.im h
    simpa [lowerNode, upperNode, criticalNode] using this
  exact (ne_of_lt W.ordered) him

/-- Membership of a height in the open window. -/
def Contains (W : CriticalWindow) (y : ℝ) : Prop := W.lower < y ∧ y < W.upper

end CriticalWindow

/-- A translated logarithmic pole coefficient centered at `ρ`. -/
def translatedPoleCoeff (ρ z : ℂ) : ℂ := 1 / (z - ρ)

/-- Away from the chosen center, the translated pole has residue coefficient one. -/
theorem translatedPole_mul {ρ z : ℂ} (hz : z ≠ ρ) :
    (z - ρ) * translatedPoleCoeff ρ z = 1 := by
  simp [translatedPoleCoeff, sub_ne_zero.mpr hz]

/-- A marked critical-line node equipped with an independent vortex residue. -/
structure CriticalVortexDatum where
  height : ℝ
  residue : ℂ

namespace CriticalVortexDatum

/-- Center of the optional translated pole. -/
def center (V : CriticalVortexDatum) : ℂ := criticalNode V.height

/-- Coefficient of the attached translated logarithmic form. -/
def coeff (V : CriticalVortexDatum) (z : ℂ) : ℂ :=
  V.residue / (z - V.center)

/-- The attached pole has the prescribed local residue coefficient. -/
theorem local_residue_readout (V : CriticalVortexDatum) {z : ℂ}
    (hz : z ≠ V.center) :
    (z - V.center) * V.coeff z = V.residue := by
  unfold coeff
  field_simp [sub_ne_zero.mpr hz]

end CriticalVortexDatum

/-- Convert a centered zero readout known to lie on the critical line into the
same complex critical node determined by its tangent coordinate. -/
theorem critical_zero_to_node
    (z : CenteredZeroReadout) (hz : z.OnCriticalLine) :
    (fromCentered z.coord).toComplex = criticalNode z.tangentCoordinate := by
  apply Complex.ext
  · dsimp [fromCentered, criticalNode, criticalLine,
      ZetaAffineChart.toComplex]
    rw [show z.coord.u = 0 from hz]
    ring
  · dsimp [fromCentered, criticalNode, criticalLine,
      ZetaAffineChart.toComplex, CenteredZeroReadout.tangentCoordinate]
    ring

/-- The zero law remains an explicit hypothesis carried by the readout; critical
location alone does not manufacture a zero. -/
theorem critical_zero_law
    (z : CenteredZeroReadout) (hz : z.OnCriticalLine) :
    InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement.ZeroAt
      z.zeroFunction (criticalNode z.tangentCoordinate) := by
  rw [← critical_zero_to_node z hz]
  exact z.isZero

/-- Compact separation packet for node, zero, and optional vortex data. -/
theorem critical_node_separation_packet (γ : ℝ) :
    (criticalNode γ).re = 1 / 2 ∧
      (criticalNode γ).im = γ ∧
      criticalNode γ ∈ punctured01 ∧
      dlog01 (criticalNode γ) ≠ 0 := by
  exact ⟨criticalNode_re γ, criticalNode_im γ,
    criticalNode_mem_punctured01 γ,
    base_dlog_nonzero_at_criticalNode γ⟩

end InfoGeometry.Analysis.BipolarCriticalWindowsVortex
