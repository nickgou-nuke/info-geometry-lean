import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.HestenesKreinSouriauCompatibility

/-!
# Real spectral calibration for the projective-null phase lane

This file records the finite calibration which is independent of any complex
spinor carrier: the centered real part is the boost coordinate and the
imaginary part is the elliptic coordinate.  Projective null descent remains
owned by `PrimonProjectiveNullDescent`; rotor algebra remains owned by the
Hestenes--Krein compatibility owner.

No identification with a Riemann zero, analytic continuation, or affine-chart
quotient is made here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectiveConePhaseOrbit

open InfoGeometry.Clifford
open InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
open InfoGeometry.Clifford.HestenesKreinSouriauCompatibility

/-- The centered hyperbolic coordinate of a complex spectral parameter. -/
def spectralBoostCoordinate (s : ℂ) : ℝ := s.re - (1 / 2 : ℝ)

/-- The elliptic height of a complex spectral parameter. -/
def spectralPhaseCoordinate (s : ℂ) : ℝ := s.im

theorem spectralBoostCoordinate_eq_zero_iff (s : ℂ) :
    spectralBoostCoordinate s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  unfold spectralBoostCoordinate
  constructor <;> intro h <;> linarith

theorem spectralCalibration_injective :
    Function.Injective (fun s : ℂ =>
      (spectralBoostCoordinate s, spectralPhaseCoordinate s)) := by
  intro s t h
  apply Complex.ext
  · dsimp [spectralBoostCoordinate] at h
    linarith [congrArg Prod.fst h]
  · exact congrArg Prod.snd h

theorem spectralBoostCoordinate_one_sub (s : ℂ) :
    spectralBoostCoordinate (1 - s) = -spectralBoostCoordinate s := by
  simp [spectralBoostCoordinate]
  ring

theorem spectralPhaseCoordinate_one_sub (s : ℂ) :
    spectralPhaseCoordinate (1 - s) = -spectralPhaseCoordinate s := by
  simp [spectralPhaseCoordinate]

theorem spectralCalibration_one_sub (s : ℂ) :
    (spectralBoostCoordinate (1 - s), spectralPhaseCoordinate (1 - s)) =
      (-spectralBoostCoordinate s, -spectralPhaseCoordinate s) := by
  rw [spectralBoostCoordinate_one_sub, spectralPhaseCoordinate_one_sub]

theorem calibratedLoxodromicRotor_one_sub_mul (s : ℂ) :
    loxodromicRotor (spectralBoostCoordinate s)
        (spectralPhaseCoordinate s) *
      loxodromicRotor (spectralBoostCoordinate (1 - s))
        (spectralPhaseCoordinate (1 - s)) =
      (1 : Operator) := by
  rw [spectralBoostCoordinate_one_sub, spectralPhaseCoordinate_one_sub]
  exact loxodromicRotor_inverse
    (spectralBoostCoordinate s) (spectralPhaseCoordinate s)

theorem calibratedLoxodromicRotor_inverse (s : ℂ) :
    loxodromicRotor (spectralBoostCoordinate s) (spectralPhaseCoordinate s) *
        loxodromicRotor (-spectralBoostCoordinate s)
          (-spectralPhaseCoordinate s) =
      (1 : Operator) := by
  exact loxodromicRotor_inverse
    (spectralBoostCoordinate s) (spectralPhaseCoordinate s)

theorem calibratedLoxodromicRotor_factorization (s : ℂ) :
    loxodromicRotor (spectralBoostCoordinate s) (spectralPhaseCoordinate s) =
      boostRotor (spectralBoostCoordinate s) *
        phaseRotor (spectralPhaseCoordinate s) := by
  exact loxodromicRotor_factorization
    (spectralBoostCoordinate s) (spectralPhaseCoordinate s)

theorem calibratedHestenesBoost_projector_weights (s : ℂ) :
    Real.cosh (spectralBoostCoordinate s) +
          Real.sinh (spectralBoostCoordinate s) =
        Real.exp (spectralBoostCoordinate s) ∧
      Real.cosh (spectralBoostCoordinate s) -
          Real.sinh (spectralBoostCoordinate s) =
        Real.exp (-spectralBoostCoordinate s) := by
  exact hestenes_boost_projector_weights (spectralBoostCoordinate s)

end InfoGeometry.Arithmetic.ProjectiveConePhaseOrbit
