import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarElementaryContourPeriods
import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import InfoGeometry.Canonical.ApolloniusGradientCircularBridge
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Canonical.BipolarPauliRootWeights
import InfoGeometry.Canonical.BipolarDeckPathClass

/-!
# Bipolar conformal logos

This capstone records the exact mathematical spine recovered from a physically
phrased note.  The hierarchy is deliberately strict:

1. Möbius coordinate `q(s)=s/(1-s)`;
2. principal logarithmic readout `W=log q` where a branch is chosen;
3. branch-independent meromorphic differential `dq/q`;
4. determinant-one diagonal `2 × 2` realization.

No electrostatic, Maxwell, superconducting, Lorentz, or global Hodge assertion
is part of this owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarConformalLogos

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarPauliRootWeights


/-- Exact multiplicative/additive/differential packet on the punctured domain. -/
theorem bipolar_logos_packet {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
    dlog01 s = 1 / (s * (1 - s)) ∧
    crossRatio01 s * dlog01 s = 1 / (1 - s) ^ 2 ∧
    Matrix.det (torusLift s) = 1 := by
  exact ⟨exp_bipolarLog hs, dlog01_eq_one_div_mul hs,
    crossRatio01_mul_dlog01 hs, torusLift_det hs⟩

/-- Exact source/sink exchange packet.  The coordinate is inverted, the
coefficient of the logarithmic form is symmetric, and the pulled-back one-form
is odd because the involution has derivative `-1`. -/
theorem exchange_packet {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ ∧
    eta (1 - s) = -eta s ∧
    dlog01 (1 - s) = dlog01 s ∧
    (-1 : ℂ) * dlog01 (1 - s) = -dlog01 s := by
  exact ⟨crossRatio01_one_sub hs, eta_one_sub hs, dlog01_one_sub s,
    pullback_one_sub_dlog01 s⟩

/-- Exact reflection packet. -/
theorem conjugation_packet (s : ℂ) :
    crossRatio01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (crossRatio01 s) ∧
    dlog01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dlog01 s) := by
  exact ⟨crossRatio01_conj s, dlog01_conj s⟩

/-- The midpoint vertical line is exactly the zero radial-logarithm locus for
the canonical Cayley coordinate, and its multiplicative image has unit norm. -/
theorem critical_line_packet (y : ℝ) :
    eta (criticalLine y) = 0 ∧
    ‖crossRatio01 (criticalLine y)‖ = 1 := by
  exact ⟨eta_criticalLine y, norm_crossRatio01_criticalLine y⟩

/-- Exact real compactification packet. -/
theorem logistic_packet (t : ℝ) :
    0 < logistic t ∧ logistic t < 1 ∧
    crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) ∧
    eta (logistic t : ℂ) = t := by
  exact ⟨logistic_pos t, logistic_lt_one t, crossRatio01_logistic t, eta_logistic t⟩

/-- The two-pole residue balance is `(+1)+(-1)=0`. -/
theorem residue_balance_packet :
    residuePair = ((1 : ℂ), (-1 : ℂ)) ∧ residuePair.1 + residuePair.2 = 0 := by
  exact ⟨rfl, residuePair_sum_zero⟩

/-- The logarithmic Cartan coordinate acts on the two native Pauli root
directions with opposite weights. -/
theorem pauli_root_weight_packet (s : ℂ) :
    commutator (cartan s)
        InfoGeometry.Physics.ChiralCausalCone.σPlus =
      bipolarLog s • InfoGeometry.Physics.ChiralCausalCone.σPlus ∧
      commutator (cartan s)
          InfoGeometry.Physics.ChiralCausalCone.σMinus =
        -bipolarLog s • InfoGeometry.Physics.ChiralCausalCone.σMinus :=
  cartan_root_weight_packet s

end InfoGeometry.Canonical.BipolarConformalLogos
