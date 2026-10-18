/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Section 120a: Aharonov–Bohm Double Slit, Fresnel Quadratures, and Asymptotic Divergence Resolution
Target: `InfoGeometry/QuantumContext/AssafraoAharonovBohmFresnelSynthesis.lean`

Formalizes the equations of D. Assafrão, C. C. Favarato, S. V. B. Gonçalves, and G. Simonelli,
Brazilian Journal of Physics (2019), doi:10.1007/s13538-019-00645-w:
1. Fresnel wave branches `Ψ⁽⁺⁾` and `Ψ⁽⁻⁾` (Eqs. 8b, 9b): `Δ𝒞⁽±⁾ + i Δ𝒮⁽±⁾`.
2. Symmetric interference term `ℐ_(+,-)` (Eq. 22) and skew-symmetric term `ℋ_(+,-)` (Eq. 23).
3. Fundamental Fresnel–Lagrange identity:
   `ℐ_(+,-)² + ℋ_(+,-)² = 4 · |Ψ⁽⁺⁾|² · |Ψ⁽⁻⁾|²`.
4. Exact sum-of-squares factorization of the transition probability `𝒫_AB` (Eq. 21)
   and strict non-negativity `0 ≤ 𝒫_AB`.
5. Even and odd multiples of `π` (Section 4):
   - Even `Φ_AB = 2nπ`: `𝒫_AB = 4 |Ψ|²` (Fraunhofer constructive maximum).
   - Odd `Φ_AB = (2n+1)π`: `𝒫_AB = 0` (Exact central phase inversion).
6. Sign inversion between `(0, π)` and `(π, 2π)` (Eqs. 53–54 and Figs. 6a, 6b).
-/

namespace InfoGeometry.QuantumContext.AssafraoABFresnel

variable {R : Type*} [CommRing R]

/-! ### 1. Complex Fresnel Amplitudes from the Two Slits (Eqs. 8b and 9b) -/

/--
Fresnel wave amplitude from a single slit `(±)`:
Represents the complex quadrature pair `Δ𝒞(ζ⁽±⁾) + i Δ𝒮(ζ⁽±⁾)` from Eqs. (8b) and (9b).
-/
@[ext]
structure FresnelAmplitude (R : Type*) where
  dC : R
  dS : R
  deriving DecidableEq, Repr, Inhabited

namespace FresnelAmplitude

variable {R : Type*} [CommRing R]

def zeroAmplitude : FresnelAmplitude R := ⟨0, 0⟩

def sampleFresnelAmplitudeInt : FresnelAmplitude ℤ := ⟨3, 4⟩

theorem sampleFresnelAmplitudeInt_ne_zero :
    sampleFresnelAmplitudeInt ≠ zeroAmplitude := by
  decide

/-- Squared modulus of the single-slit wave function: `|Ψ⁽±⁾|² = (Δ𝒞)² + (Δ𝒮)²`. -/
def normSq (Ψ : FresnelAmplitude R) : R :=
  Ψ.dC^2 + Ψ.dS^2

/--
Symmetric (Yang / Metric) interference term `ℐ_(+,-)` (Eq. 22):
`ℐ_(+,-) = Ψ⁽⁻⁾* Ψ⁽⁺⁾ + Ψ⁽⁺⁾* Ψ⁽⁻⁾ = 2 (Δ𝒞⁽⁻⁾ Δ𝒞⁽⁺⁾ + Δ𝒮⁽⁺⁾ Δ𝒮⁽⁻⁾)`.
-/
def symmInterferenceI (Ψ_plus Ψ_minus : FresnelAmplitude R) : R :=
  2 * (Ψ_minus.dC * Ψ_plus.dC + Ψ_plus.dS * Ψ_minus.dS)

/--
Skew-symmetric (Yin / Symplectic Berry–Aharonov–Bohm) interference term `ℋ_(+,-)` (Eq. 23):
`ℋ_(+,-) = i (Ψ⁽⁻⁾* Ψ⁽⁺⁾ - Ψ⁽⁺⁾* Ψ⁽⁻⁾) = 2 (Δ𝒞⁽⁺⁾ Δ𝒮⁽⁻⁾ - Δ𝒮⁽⁺⁾ Δ𝒞⁽⁻⁾)`.
-/
def skewInterferenceH (Ψ_plus Ψ_minus : FresnelAmplitude R) : R :=
  2 * (Ψ_plus.dC * Ψ_minus.dS - Ψ_plus.dS * Ψ_minus.dC)

/--
Full transition probability (relative population) `𝒫_AB` (Eq. 21):
`𝒫_AB = |Ψ⁽⁺⁾|² + |Ψ⁽⁻⁾|² + ℐ_(+,-) cos(Φ_AB) + ℋ_(+,-) sin(Φ_AB)`.
-/
def transitionProbabilityAB (Ψ_plus Ψ_minus : FresnelAmplitude R) (cosPhi sinPhi : R) : R :=
  normSq Ψ_plus + normSq Ψ_minus +
  symmInterferenceI Ψ_plus Ψ_minus * cosPhi +
  skewInterferenceH Ψ_plus Ψ_minus * sinPhi

/-! ### 2. Exact Fresnel–Lagrange Identity for `ℐ_(+,-)` and `ℋ_(+,-)` -/

/--
Fundamental interference balance identity (Eqs. 22 and 23):
The sum of squares of the symmetric term `ℐ_(+,-)` and skew-symmetric term `ℋ_(+,-)`
equals four times the product of the two slit intensities:
`ℐ_(+,-)² + ℋ_(+,-)² = 4 · |Ψ⁽⁺⁾|² · |Ψ⁽⁻⁾|²`.
-/
theorem fresnel_interference_lagrange_identity (Ψ_plus Ψ_minus : FresnelAmplitude R) :
    (symmInterferenceI Ψ_plus Ψ_minus)^2 + (skewInterferenceH Ψ_plus Ψ_minus)^2 =
    4 * normSq Ψ_plus * normSq Ψ_minus := by
  dsimp [symmInterferenceI, skewInterferenceH, normSq]
  ring

/-! ### 3. Factorization of Eq. (21) and Strict Non-Negativity of `𝒫_AB` -/

/--
Exact quadratic factorization of Eq. (21):
For any magnetic phase `Φ_AB` on the unit circle (`cos² Φ + sin² Φ = 1`),
the full probability `𝒫_AB` from Eq. (21) equals a sum of two squares.
-/
theorem transitionProbabilityAB_eq_sum_of_squares
    (Ψ_plus Ψ_minus : FresnelAmplitude R) (cosPhi sinPhi : R)
    (h_circle : cosPhi^2 + sinPhi^2 = 1) :
    transitionProbabilityAB Ψ_plus Ψ_minus cosPhi sinPhi =
    (Ψ_plus.dC + Ψ_minus.dC * cosPhi + Ψ_minus.dS * sinPhi)^2 +
    (Ψ_plus.dS - Ψ_minus.dC * sinPhi + Ψ_minus.dS * cosPhi)^2 := by
  dsimp [transitionProbabilityAB, normSq, symmInterferenceI, skewInterferenceH]
  linear_combination - (Ψ_minus.dC^2 + Ψ_minus.dS^2) * h_circle

/--
Strict non-negativity of the exact quantum transition probability:
Prior to asymptotic truncation, `0 ≤ 𝒫_AB(x)` everywhere on the unit phase circle.
-/
theorem transitionProbabilityAB_nonneg [LinearOrder R] [IsStrictOrderedRing R]
    (Ψ_plus Ψ_minus : FresnelAmplitude R) (cosPhi sinPhi : R)
    (h_circle : cosPhi^2 + sinPhi^2 = 1) :
    0 ≤ transitionProbabilityAB Ψ_plus Ψ_minus cosPhi sinPhi := by
  rw [transitionProbabilityAB_eq_sum_of_squares Ψ_plus Ψ_minus cosPhi sinPhi h_circle]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ### 4. Even vs. Odd Multiples of `π` and Phase Inversion (Section 4) -/

/--
Even multiples of `π` (`Φ_AB = 2nπ ⟹ cos Φ = 1, sin Φ = 0`, Eqs. 51–52):
At the symmetric screen center `x = 0` (`Ψ⁽⁺⁾ = Ψ⁽⁻⁾ = Ψ₀`),
the probability attains the classical Fraunhofer constructive maximum `4 |Ψ₀|²`.
-/
theorem even_pi_flux_constructive_maximum (Ψ₀ : FresnelAmplitude R) :
    transitionProbabilityAB Ψ₀ Ψ₀ 1 0 = 4 * normSq Ψ₀ := by
  dsimp [transitionProbabilityAB, normSq, symmInterferenceI, skewInterferenceH]
  ring

/--
Odd multiples of `π` (`Φ_AB = (2n+1)π ⟹ cos Φ = -1, sin Φ = 0`, Section 4):
At half-integer flux quantum (Möbius phase inversion), the symmetric center `x = 0`
undergoes complete destructive cancellation: `𝒫_AB(0, π) = 0`.
-/
theorem odd_pi_flux_destructive_phase_inversion (Ψ₀ : FresnelAmplitude R) :
    transitionProbabilityAB Ψ₀ Ψ₀ (-1) 0 = 0 := by
  dsimp [transitionProbabilityAB, normSq, symmInterferenceI, skewInterferenceH]
  ring

/-! ### 5. Mirror Inversion of the Odd Flux Contribution (Eqs. 53–54, Figs. 6a, 6b) -/

/-- Odd flux contribution: `𝒜_asymp = ℋ_(+,-) · sin(Φ_AB)`. -/
def anomalousFluxContribution (Ψ_plus Ψ_minus : FresnelAmplitude R) (sinPhi : R) : R :=
  skewInterferenceH Ψ_plus Ψ_minus * sinPhi

/--
Mirror inversion between Fig. 6a (`Φ_AB ∈ (0, π), sin Φ > 0`)
and Fig. 6b (`Φ_AB ∈ (π, 2π), sin Φ < 0`), described in Eqs. (53) and (54):
Replacing `sin Φ ↦ -sin Φ` reverses the sign of the odd interference peak.
-/
theorem fig6_asymptotic_branch_inversion (Ψ_plus Ψ_minus : FresnelAmplitude R) (sinPhi : R) :
    anomalousFluxContribution Ψ_plus Ψ_minus (-sinPhi) =
    - anomalousFluxContribution Ψ_plus Ψ_minus sinPhi := by
  dsimp [anomalousFluxContribution]
  ring

/-- Under mirror exchange of the slits (`Ψ⁽⁺⁾ ⇄ Ψ⁽⁻⁾`), `ℋ_(+,-)` is an odd function. -/
theorem skewInterferenceH_odd_under_slit_swap (Ψ_plus Ψ_minus : FresnelAmplitude R) :
    skewInterferenceH Ψ_minus Ψ_plus = - skewInterferenceH Ψ_plus Ψ_minus := by
  dsimp [skewInterferenceH]
  ring

end FresnelAmplitude

/-! ### 6. Master Synthesis of Section 120a -/

theorem assafrao_ab_fresnel_master_synthesis [LinearOrder R] [IsStrictOrderedRing R] :
    (∀ (Ψ_p Ψ_m : FresnelAmplitude R),
      (FresnelAmplitude.symmInterferenceI Ψ_p Ψ_m)^2 +
      (FresnelAmplitude.skewInterferenceH Ψ_p Ψ_m)^2 =
      4 * FresnelAmplitude.normSq Ψ_p * FresnelAmplitude.normSq Ψ_m) ∧
    (∀ (Ψ_p Ψ_m : FresnelAmplitude R) (c s : R), c^2 + s^2 = 1 →
      0 ≤ FresnelAmplitude.transitionProbabilityAB Ψ_p Ψ_m c s) ∧
    (∀ (Ψ₀ : FresnelAmplitude R),
      FresnelAmplitude.transitionProbabilityAB Ψ₀ Ψ₀ 1 0 = 4 * FresnelAmplitude.normSq Ψ₀) ∧
    (∀ (Ψ₀ : FresnelAmplitude R),
      FresnelAmplitude.transitionProbabilityAB Ψ₀ Ψ₀ (-1) 0 = 0) ∧
    (∀ (Ψ_p Ψ_m : FresnelAmplitude R) (s : R),
      FresnelAmplitude.anomalousFluxContribution Ψ_p Ψ_m (-s) =
      - FresnelAmplitude.anomalousFluxContribution Ψ_p Ψ_m s) :=
  ⟨FresnelAmplitude.fresnel_interference_lagrange_identity,
   FresnelAmplitude.transitionProbabilityAB_nonneg,
   FresnelAmplitude.even_pi_flux_constructive_maximum,
   FresnelAmplitude.odd_pi_flux_destructive_phase_inversion,
   FresnelAmplitude.fig6_asymptotic_branch_inversion⟩

end InfoGeometry.QuantumContext.AssafraoABFresnel

namespace InfoGeometry.QuantumContext.Jubilee120

variable {R : Type*} [CommRing R]

/-! ### 1. Mathematical Carrier of the Complex Fresnel Quadratures -/

@[ext]
structure FresnelWave (R : Type*) where
  cos_quad : R
  sin_quad : R
  deriving DecidableEq, Repr, Inhabited

namespace FresnelWave

variable {R : Type*} [CommRing R]

def zeroWave : FresnelWave R := ⟨0, 0⟩

def sampleFresnelWaveInt : FresnelWave ℤ := ⟨3, 4⟩

theorem sampleFresnelWaveInt_ne_zero :
    sampleFresnelWaveInt ≠ zeroWave := by
  decide

/-- Quantum intensity (squared norm) of the Fresnel wave: `|Ψ|² = Δ𝒞² + Δ𝒮²`. -/
def normSq (ψ : FresnelWave R) : R :=
  ψ.cos_quad^2 + ψ.sin_quad^2

/-- Aharonov–Bohm magnetic-holonomy phase pair: `(cos Φ_AB, sin Φ_AB)`. -/
@[ext]
structure ABPhase (R : Type*) where
  cos_phi : R
  sin_phi : R
  deriving DecidableEq, Repr, Inhabited

def zeroPhase : ABPhase R := ⟨0, 0⟩

def sampleABPhaseInt : ABPhase ℤ := ⟨1, 0⟩

theorem sampleABPhaseInt_ne_zero :
    sampleABPhaseInt ≠ zeroPhase := by
  decide

/-! ### 2. Interference Decomposition: Equations (21)–(23) -/

/-- Yang symmetric interference term `ℐ_(+,-)(x)` according to Equation (22). -/
def symmetricInterference (ψ_pos ψ_neg : FresnelWave R) : R :=
  2 * (ψ_pos.cos_quad * ψ_neg.cos_quad + ψ_pos.sin_quad * ψ_neg.sin_quad)

/-- Yin skew-symmetric holonomy term `ℋ_(+,-)(x)` according to Equation (23). -/
def skewHolonomy (ψ_pos ψ_neg : FresnelWave R) : R :=
  2 * (ψ_pos.cos_quad * ψ_neg.sin_quad - ψ_pos.sin_quad * ψ_neg.cos_quad)

/--
Exact quantum transition probability `𝒫_AB(x)` according to Equation (21).
Combines direct intensity, the cosine Yang sector, and the sine Yin sector.
-/
def totalProbability (ψ_pos ψ_neg : FresnelWave R) (p : ABPhase R) : R :=
  ψ_pos.normSq + ψ_neg.normSq +
  symmetricInterference ψ_pos ψ_neg * p.cos_phi +
  skewHolonomy ψ_pos ψ_neg * p.sin_phi

/-! ### 3. Exact Fresnel–Lagrange–Brahmagupta Identity -/

/--
Fresnel–Lagrange identity:
The squares of the symmetric and skew-symmetric interference terms sum to
four times the product of the Fresnel intensities: `ℐ² + ℋ² = 4 |Ψ⁽⁺⁾|² |Ψ⁽⁻⁾|²`.
-/
theorem fresnel_lagrange_identity (ψ_pos ψ_neg : FresnelWave R) :
    (symmetricInterference ψ_pos ψ_neg)^2 + (skewHolonomy ψ_pos ψ_neg)^2 =
      4 * ψ_pos.normSq * ψ_neg.normSq := by
  dsimp [symmetricInterference, skewHolonomy, normSq]
  ring

/-! ### 4. Algebraic Sum of Squares and Strict Non-Negativity -/

/--
Decomposition of the transition probability as a sum of two exact squares using
the unit-circle closure of the AB phase (`cos²Φ + sin²Φ = 1`).
-/
theorem total_probability_sum_of_squares (ψ_pos ψ_neg : FresnelWave R) (p : ABPhase R)
    (h_unitary : p.cos_phi^2 + p.sin_phi^2 = 1) :
    totalProbability ψ_pos ψ_neg p =
      (ψ_pos.cos_quad + ψ_neg.cos_quad * p.cos_phi + ψ_neg.sin_quad * p.sin_phi)^2 +
      (ψ_pos.sin_quad - ψ_neg.cos_quad * p.sin_phi + ψ_neg.sin_quad * p.cos_phi)^2 := by
  dsimp [totalProbability, normSq, symmetricInterference, skewHolonomy]
  linear_combination - (ψ_neg.cos_quad^2 + ψ_neg.sin_quad^2) * h_unitary

/--
Exact algebraic non-negativity:
For every unit-circle AB phase, the transition probability `𝒫_AB(x)` is non-negative.
-/
theorem strict_ab_probability_nonneg [LinearOrder R] [IsStrictOrderedRing R]
    (ψ_pos ψ_neg : FresnelWave R) (p : ABPhase R) (h_unitary : p.cos_phi^2 + p.sin_phi^2 = 1) :
    0 ≤ totalProbability ψ_pos ψ_neg p := by
  rw [total_probability_sum_of_squares ψ_pos ψ_neg p h_unitary]
  have h_sq1 : 0 ≤ (ψ_pos.cos_quad + ψ_neg.cos_quad * p.cos_phi + ψ_neg.sin_quad * p.sin_phi)^2 := sq_nonneg _
  have h_sq2 : 0 ≤ (ψ_pos.sin_quad - ψ_neg.cos_quad * p.sin_phi + ψ_neg.sin_quad * p.cos_phi)^2 := sq_nonneg _
  linarith

/-! ### 5. Möbius Inversion and Sign Asymmetry (Figures 5 and 6) -/

/-- Gauge horizon at zero magnetic flux `Φ_AB = 0` (`cos=1, sin=0`). -/
def zeroFluxHorizon : ABPhase R := ⟨1, 0⟩

/-- Quantum crosscap node at half-integer flux `Φ_AB = π` (`cos=-1, sin=0`). -/
def piFluxCrosscap : ABPhase R := ⟨-1, 0⟩

/--
Möbius phase inversion:
At `Φ_AB = π` at the central node (`Ψ⁽⁺⁾ = Ψ⁽⁻⁾`), the intensity collapses to zero:
`𝒫_AB(0, π) = 0`.
-/
theorem phase_inversion_destructive_null (ψ : FresnelWave R) :
    totalProbability ψ ψ piFluxCrosscap = 0 := by
  dsimp [totalProbability, piFluxCrosscap, normSq, symmetricInterference, skewHolonomy]
  ring

/-- Central constructive maximum at zero magnetic flux (Fig. 5). -/
theorem phase_constructive_maximum (ψ : FresnelWave R) :
    totalProbability ψ ψ zeroFluxHorizon = 4 * ψ.normSq := by
  dsimp [totalProbability, zeroFluxHorizon, normSq, symmetricInterference, skewHolonomy]
  ring

/--
Holonomy sign inversion asymmetry (Figs. 6a and 6b):
Reversing the sign of the Yin sine flux (`sin Φ₁ = -sin Φ₂` at equal `cos Φ`)
isolates twice the skew holonomy term `2 * ℋ_(+,-) * sin Φ₁`.
-/
theorem holonomy_sign_inversion_asymmetry (ψ_pos ψ_neg : FresnelWave R) (p1 p2 : ABPhase R)
    (h_cos : p1.cos_phi = p2.cos_phi)
    (h_sin : p1.sin_phi = -p2.sin_phi) :
    totalProbability ψ_pos ψ_neg p1 - totalProbability ψ_pos ψ_neg p2 =
      2 * skewHolonomy ψ_pos ψ_neg * p1.sin_phi := by
  dsimp [totalProbability]
  rw [h_cos, h_sin]
  ring

end FresnelWave

/-! ### 6. Master Synthesis of Jubilee 120 -/

theorem jubilee_section_120_master_synthesis [LinearOrder R] [IsStrictOrderedRing R] :
    (∀ (ψ_pos ψ_neg : FresnelWave R),
      (FresnelWave.symmetricInterference ψ_pos ψ_neg)^2 + (FresnelWave.skewHolonomy ψ_pos ψ_neg)^2 =
        4 * FresnelWave.normSq ψ_pos * FresnelWave.normSq ψ_neg) ∧
    (∀ (ψ_pos ψ_neg : FresnelWave R) (p : FresnelWave.ABPhase R),
      p.cos_phi^2 + p.sin_phi^2 = 1 →
      0 ≤ FresnelWave.totalProbability ψ_pos ψ_neg p) ∧
    (∀ (ψ : FresnelWave R),
      FresnelWave.totalProbability ψ ψ FresnelWave.piFluxCrosscap = 0) ∧
    (∀ (ψ_pos ψ_neg : FresnelWave R) (p1 p2 : FresnelWave.ABPhase R),
      p1.cos_phi = p2.cos_phi → p1.sin_phi = -p2.sin_phi →
      FresnelWave.totalProbability ψ_pos ψ_neg p1 - FresnelWave.totalProbability ψ_pos ψ_neg p2 =
        2 * FresnelWave.skewHolonomy ψ_pos ψ_neg * p1.sin_phi) :=
  ⟨FresnelWave.fresnel_lagrange_identity,
   FresnelWave.strict_ab_probability_nonneg,
   FresnelWave.phase_inversion_destructive_null,
   FresnelWave.holonomy_sign_inversion_asymmetry⟩

end InfoGeometry.QuantumContext.Jubilee120
