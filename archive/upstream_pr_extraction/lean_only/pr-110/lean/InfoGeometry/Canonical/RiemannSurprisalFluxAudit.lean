import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannHypothesisProjectiveFormulation
import InfoGeometry.Canonical.SimplexSurprisalMetriplectic
import InfoGeometry.Canonical.ThreeColorNativeBracketTable
import InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

/-!
# Riemann surprisal and logarithmic-flux audit

This module extracts the theorem-safe mathematical content of the proposed
``electrostatic / surprisal / chiral-flux'' picture and connects it to the
existing canonical owners.

The exact content is:

* the Cayley coordinate `s / (1 - s)` exchanges the marked points `0` and `1`
  under `s ↦ 1 - s`;
* its real logarithmic modulus defines a relative-surprisal potential whose
  zero set, away from the marked points, is exactly `Re s = 1 / 2`;
* asking every nontrivial zeta zero to have zero Cayley surprisal is precisely
  an equivalent formulation of the Riemann hypothesis, not a proof of it;
* an integer logarithmic pole has an integer normalized contour period, so a
  source of charge `+1` and a sink of charge `-1` have cancelling periods;
* the repository-owned rational split-octonion chiral generators satisfy the
  exact local ladder commutator, anticommutator, and nilpotence relations.

No theorem below identifies a Riemann zero with a contour puncture, derives
zero locations from a conductor analogy, or derives contour quantization from
the split-octonion bracket table.  Those would require additional analytic or
physical hypotheses not present in the source argument.
-/

noncomputable section

namespace InfoGeometry.Canonical.RiemannSurprisalFluxAudit

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Arithmetic.RiemannHypothesisProjectiveFormulation
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

/-! ## 1. Cayley relative surprisal -/

/--
Real relative surprisal of the marked pair `(0, 1)` in the Cayley coordinate.
It is `-log |s / (1-s)|`, written without a square root as
`-(1/2) log ‖s/(1-s)‖²`.
-/
def cayleyRelativeSurprisal (s : ℂ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (Complex.normSq (cayleyToFugacity s))

/-- Away from the marked source and sink, the squared Cayley modulus is
strictly positive. -/
theorem cayleyToFugacity_normSq_pos
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    0 < Complex.normSq (cayleyToFugacity s) := by
  unfold cayleyToFugacity
  rw [Complex.normSq_div]
  have hden : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  exact div_pos (Complex.normSq_pos.mpr hs0) (Complex.normSq_pos.mpr hden)

/-- Every point of the critical line has zero Cayley relative surprisal. -/
theorem cayleyRelativeSurprisal_eq_zero_of_criticalLine
    {s : ℂ} (hs : OnCriticalLine s) :
    cayleyRelativeSurprisal s = 0 := by
  have hcircle := (criticalLine_iff_cayley_unitCircle s).mp hs
  change Complex.normSq (cayleyToFugacity s) = 1 at hcircle
  simp [cayleyRelativeSurprisal, hcircle]

/--
Away from `0` and `1`, zero Cayley relative surprisal is exactly the critical
line.  The endpoint hypotheses are mathematically necessary because division
and logarithm are totalized in Lean.
-/
theorem cayleyRelativeSurprisal_eq_zero_iff_criticalLine
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    cayleyRelativeSurprisal s = 0 ↔ OnCriticalLine s := by
  constructor
  · intro hzero
    have hlog : Real.log (Complex.normSq (cayleyToFugacity s)) = 0 := by
      unfold cayleyRelativeSurprisal at hzero
      linarith
    have hpos := cayleyToFugacity_normSq_pos s hs0 hs1
    rcases (Real.log_eq_zero).mp hlog with hnorm_zero | hnorm_one | hnorm_neg_one
    · exact (ne_of_gt hpos hnorm_zero).elim
    · apply (criticalLine_iff_cayley_unitCircle s).mpr
      change Complex.normSq (cayleyToFugacity s) = 1
      exact hnorm_one
    · exfalso
      linarith
  · exact cayleyRelativeSurprisal_eq_zero_of_criticalLine

/-- Standard parametrization of the complete critical line. -/
def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (t : ℂ)

@[simp] theorem criticalLinePoint_re (t : ℝ) :
    (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

/-- Every real height, not only zeta-zero heights, lies on the zero-surprisal
Cayley level set. -/
theorem criticalLinePoint_relativeSurprisal_zero (t : ℝ) :
    cayleyRelativeSurprisal (criticalLinePoint t) = 0 := by
  apply cayleyRelativeSurprisal_eq_zero_of_criticalLine
  exact criticalLinePoint_re t

/-! ## 2. Exact status of the Riemann-zero claim -/

/-- Nontrivial zeros in the selected open critical strip cannot be the marked
source `0`. -/
theorem nontrivialZero_ne_zero
    {s : ℂ} (hs : s ∈ nontrivialZeroSet) : s ≠ 0 := by
  change IsNontrivialZero s at hs
  have hre : 0 < s.re := hs.2.1
  intro h
  subst s
  norm_num at hre

/-- Nontrivial zeros in the selected open critical strip cannot be the marked
sink `1`. -/
theorem nontrivialZero_ne_one
    {s : ℂ} (hs : s ∈ nontrivialZeroSet) : s ≠ 1 := by
  change IsNontrivialZero s at hs
  have hre : s.re < 1 := hs.2.2
  intro h
  subst s
  norm_num at hre

/-- The source document's ``all zero punctures are grounded'' assertion,
expressed without physical terminology. -/
def RiemannHypothesisZeroSurprisal : Prop :=
  ∀ s ∈ nontrivialZeroSet, cayleyRelativeSurprisal s = 0

/--
The zero-surprisal assertion is exactly equivalent to the existing canonical
critical-line formulation of RH.  Hence the electrostatic vocabulary does not
supply a proof: it restates the same unresolved zero-location proposition.
-/
theorem riemannHypothesisCriticalLine_iff_zeroSurprisal :
    RiemannHypothesisCriticalLine ↔ RiemannHypothesisZeroSurprisal := by
  constructor
  · intro hRH s hs
    exact cayleyRelativeSurprisal_eq_zero_of_criticalLine (hRH s hs)
  · intro hground s hs
    exact
      (cayleyRelativeSurprisal_eq_zero_iff_criticalLine s
        (nontrivialZero_ne_zero hs) (nontrivialZero_ne_one hs)).mp
        (hground s hs)

/-! ## 3. Integer logarithmic contour periods -/

/-- A logarithmic current of integer charge `n` centered at `rho`.
The sign is chosen so that its normalized positively oriented circle period is
exactly `n`. -/
def integerLogarithmicFlux (rho : ℂ) (n : ℤ) (z : ℂ) : ℂ :=
  logarithmicPole rho (-n) z

/-- The normalized circle period of an integer logarithmic current is the
integer charge. -/
theorem normalized_integerLogarithmicFlux_circleIntegral
    (rho : ℂ) (n : ℤ) {R : ℝ} (hR : 0 < R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), integerLogarithmicFlux rho n z) =
      (n : ℂ) := by
  simpa [integerLogarithmicFlux] using
    (normalized_logarithmicPole_circleIntegral rho (-n) hR)

/-- Marked source of charge `+1`. -/
def sourcePole : ℂ := 0

/-- Marked sink of charge `-1`. -/
def sinkPole : ℂ := 1

/-- Source logarithmic current. -/
def sourceFlux (z : ℂ) : ℂ :=
  integerLogarithmicFlux sourcePole 1 z

/-- Sink logarithmic current. -/
def sinkFlux (z : ℂ) : ℂ :=
  integerLogarithmicFlux sinkPole (-1) z

/-- The normalized source period is `+1`. -/
theorem sourceFlux_normalized_circleIntegral
    {R : ℝ} (hR : 0 < R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(sourcePole, R), sourceFlux z) = 1 := by
  simpa [sourceFlux] using
    (normalized_integerLogarithmicFlux_circleIntegral sourcePole (1 : ℤ) hR)

/-- The normalized sink period is `-1`. -/
theorem sinkFlux_normalized_circleIntegral
    {R : ℝ} (hR : 0 < R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(sinkPole, R), sinkFlux z) = -1 := by
  simpa [sinkFlux] using
    (normalized_integerLogarithmicFlux_circleIntegral sinkPole (-1 : ℤ) hR)

/-- Source and sink normalized periods cancel exactly. -/
theorem source_sink_normalized_flux_neutrality
    {Rsource Rsink : ℝ} (hsource : 0 < Rsource) (hsink : 0 < Rsink) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(sourcePole, Rsource), sourceFlux z) +
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(sinkPole, Rsink), sinkFlux z) = 0 := by
  rw [sourceFlux_normalized_circleIntegral hsource,
    sinkFlux_normalized_circleIntegral hsink]
  ring

/-! ## 4. Native circular chiral split-octonion relations -/

/--
The exact same-colour circular ladder table in the native rational
split-octonion carrier.  It includes the two grading commutators, the mixed
commutator and CAR relation, and square-zero raising/lowering generators.
-/
theorem nativeCircularChiralLadderRelations
    (c : SplitOctonionColour) :
    nativeCommutator fundamentalSymmetry (modularSigmaPlus c) =
        (2 : ℚ) • modularSigmaPlus c ∧
    nativeCommutator fundamentalSymmetry (modularSigmaMinus c) =
        (-2 : ℚ) • modularSigmaMinus c ∧
    nativeCommutator (modularSigmaPlus c) (modularSigmaMinus c) =
        fundamentalSymmetry ∧
    nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus c) =
        rationalBasis .one ∧
    splitOctonionMulQ (modularSigmaPlus c) (modularSigmaPlus c) = 0 ∧
    splitOctonionMulQ (modularSigmaMinus c) (modularSigmaMinus c) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nativeCommutator
    rw [fundamentalSymmetry_mul_modularSigmaPlus,
      modularSigmaPlus_mul_fundamentalSymmetry]
    module
  · unfold nativeCommutator
    rw [fundamentalSymmetry_mul_modularSigmaMinus,
      modularSigmaMinus_mul_fundamentalSymmetry]
    module
  · simpa using nativeSigmaPlusSigmaMinus_commutator c c
  · simpa using nativeSigmaPlusSigmaMinus_anticommutator c c
  · exact modularSigmaPlus_sq_zero c
  · exact modularSigmaMinus_sq_zero c

end InfoGeometry.Canonical.RiemannSurprisalFluxAudit

end noncomputable section
