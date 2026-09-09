import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import InfoGeometry.Krein.SplitBoost

/-!
# Split-Octonion Projective Rapidity, Triad Flow and Monodromy Bridge

This module formalizes:
1. **The Projective Chiral Ratio and Hyperbolic Rapidity**:
   $$z = \frac{x_+}{x_-}, \qquad \eta = \frac{1}{2} \ln z = \frac{1}{2} \ln\left(\frac{x_+}{x_-}\right)$$
2. **🏆 THEOREM 1 (Chiral Inversion / Reflection Identity)**:
   $$\kappa : (x_+, x_-) \mapsto (x_-, x_+) \implies z \mapsto z^{-1} \implies \eta \mapsto -\eta$$
3. **🏆 THEOREM 2 (Symmetric Section Zero Rapidity)**:
   $$x_+ = x_- \implies z = 1 \implies \eta = 0$$
4. **🏆 THEOREM 3 (Loxodromic Boost Flow as Rapidity Translation)**:
   $$\eta(e^{2s} x_+, x_-) = \eta(x_+, x_-) + s$$
5. **🏆 THEOREM 4 (Information Surprisal Difference Alignment)**:
   $$-\ln p_+ + \ln p_- = -2 \eta(p_+, p_-)$$
6. **🏆 THEOREM 5 (Complex Phase $2\pi$ Monodromy / Winding Periodicity)**:
   $$e^{I (\theta + 2\pi)} = e^{I \theta}$$
-/

noncomputable section

open Real Complex

namespace InfoGeometry.Lie.SplitOctonionProjectiveRapidityMonodromyBridge

/-- Projective ratio $z = x_+ / x_-$. -/
def projZ (xp xm : ℝ) : ℝ := xp / xm

/-- Hyperbolic rapidity $\eta = \frac{1}{2} \ln(x_+ / x_-)$. -/
def rapidity (xp xm : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (projZ xp xm)

/-- 🏆 THEOREM 1: Symmetric section has zero rapidity ($z = 1 \implies \eta = 0$). -/
theorem rapidity_symm (x : ℝ) (hx : x ≠ 0) :
    rapidity x x = 0 := by
  dsimp [rapidity, projZ]
  rw [div_self hx, Real.log_one, mul_zero]

/-- 🏆 THEOREM 2: Chiral reflection inverts the ratio: $z(x_-, x_+) = (z(x_+, x_-))^{-1}$. -/
theorem projZ_inv (xp xm : ℝ) :
    projZ xm xp = (projZ xp xm)⁻¹ := by
  dsimp [projZ]
  exact (inv_div xp xm).symm

/-- 🏆 THEOREM 3: Chiral reflection negates the rapidity: $\eta(x_-, x_+) = -\eta(x_+, x_-)$. -/
theorem rapidity_neg (xp xm : ℝ) (hxp : 0 < xp) (hxm : 0 < xm) :
    rapidity xm xp = - rapidity xp xm := by
  dsimp [rapidity, projZ]
  have hpos : 0 < xp / xm := div_pos hxp hxm
  rw [← inv_div xp xm]
  rw [Real.log_inv]
  ring

/-- 🏆 THEOREM 4: Loxodromic dilation / boost acts as an affine translation in rapidity. -/
theorem rapidity_boost (xp xm s : ℝ) (hxp : 0 < xp) (hxm : 0 < xm) :
    rapidity (xp * Real.exp (2 * s)) xm = rapidity xp xm + s := by
  dsimp [rapidity, projZ]
  have hpos : 0 < xp / xm := div_pos hxp hxm
  rw [mul_div_right_comm]
  rw [Real.log_mul (ne_of_gt hpos) (ne_of_gt (Real.exp_pos (2 * s)))]
  rw [Real.log_exp]
  ring

/-! The canonical split boost and the projective rapidity use the same
parameter.  This is the transport theorem between the native `SplitComplex`
boost owner and the ratio readout above. -/

theorem rapidity_boostElement_mul
    (t : ℝ) :
    rapidity
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.leftPart
          (InfoGeometry.Krein.SplitBoost.boostElement t))
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart
          (InfoGeometry.Krein.SplitBoost.boostElement t)) =
      t := by
  unfold rapidity projZ
  simp [InfoGeometry.Krein.SplitBoost.boostElement,
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.leftPart,
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart,
    Real.cosh_add_sinh, Real.cosh_sub_sinh,
    Real.log_div (ne_of_gt (Real.exp_pos t))
      (ne_of_gt (Real.exp_pos (-t)))]
  ring

theorem rapidity_boostElement_action
    (xp xm t : ℝ) (hxp : 0 < xp) (hxm : 0 < xm) :
    rapidity
      (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.leftPart
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul
          (InfoGeometry.Krein.SplitBoost.boostElement t)
          (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.reconstruct
            xp xm)))
      (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul
          (InfoGeometry.Krein.SplitBoost.boostElement t)
          (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.reconstruct
            xp xm))) =
      rapidity xp xm + t := by
  rw [InfoGeometry.Krein.SplitBoost.boost_leftPart_mul,
    InfoGeometry.Krein.SplitBoost.boost_rightPart_mul]
  simp only [InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.leftPart,
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart,
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.reconstruct]
  have hleft : Real.exp t * ((xp + xm) / 2 + (xp - xm) / 2) =
      Real.exp t * xp := by ring
  have hright : Real.exp (-t) * ((xp + xm) / 2 - (xp - xm) / 2) =
      Real.exp (-t) * xm := by ring
  rw [hleft, hright]
  unfold rapidity projZ
  have hratio :
      (Real.exp t * xp) / (Real.exp (-t) * xm) =
        (xp * Real.exp (2 * t)) / xm := by
    field_simp [ne_of_gt (Real.exp_pos t), ne_of_gt (Real.exp_pos (-t)),
      ne_of_gt hxp, ne_of_gt hxm]
    rw [← Real.exp_add]
    ring_nf
  rw [hratio]
  exact rapidity_boost xp xm t hxp hxm

/-- 🏆 THEOREM 5: Information surprisal difference matches $-2 \times$ rapidity. -/
theorem surprisal_eq_rapidity (pp pm : ℝ) (hpp : 0 < pp) (hpm : 0 < pm) :
    - Real.log pp + Real.log pm = - 2 * rapidity pp pm := by
  dsimp [rapidity, projZ]
  rw [Real.log_div (ne_of_gt hpp) (ne_of_gt hpm)]
  ring

/-- 🏆 THEOREM 6: Complex phase $2\pi$ winding periodicity around the apex (Monodromy). -/
theorem complex_phase_winding (θ : ℝ) :
    Complex.exp (Complex.I * ((θ : ℂ) + 2 * Real.pi)) = Complex.exp (Complex.I * (θ : ℂ)) := by
  have : Complex.I * ((θ : ℂ) + 2 * Real.pi) = Complex.I * (θ : ℂ) + (2 * Real.pi) * Complex.I := by ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

end InfoGeometry.Lie.SplitOctonionProjectiveRapidityMonodromyBridge
