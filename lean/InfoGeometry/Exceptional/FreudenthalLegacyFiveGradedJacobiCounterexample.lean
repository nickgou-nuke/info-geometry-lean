import Mathlib
import InfoGeometry.Exceptional.FreudenthalSymplecticContactRepresentation
import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure
import InfoGeometry.Exceptional.FreudenthalSymplecticMixedTripleCounterexample

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-! The second extreme Jacobi cell is useful as a direct diagnostic of the
    legacy sign convention.  It is kept beside, rather than merged into, the
    already established negative-charge cell below. -/

theorem legacy_extreme_extreme_plus_jacobiator
    (y : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D 1) (genEminus D 1)
        (injChargePlus D y) =
      injChargePlus D ((-2 : ℝ) • y) := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveJacobiator, fiveGradedBracket, genEplus, genEminus,
      genHscale, injChargePlus] <;>
    module

theorem legacy_minus1_plus2 (x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (genEplus D 1) =
      injChargePlus D x := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, injChargeMinus, injChargePlus, genEplus]

theorem legacy_minus2_plus1 (x : FreudenthalCharge J) :
    fiveGradedBracket D (genEminus D 1) (injChargePlus D x) =
      injChargeMinus D x := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, genEminus, injChargePlus, injChargeMinus]

theorem legacy_plus2_minus2 :
    fiveGradedBracket D (genEplus D 1) (genEminus D 1) =
      genHscale D 1 := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, genEplus, genEminus, genHscale]

theorem legacy_minus1_scale (x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (genHscale D 1) =
      injChargeMinus D x := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, injChargeMinus, genHscale]

theorem legacy_minus2_minus1 (x : FreudenthalCharge J) :
    fiveGradedBracket D (genEminus D 1) (injChargeMinus D x) = 0 := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, genEminus, injChargeMinus]

theorem legacy_extreme_charge_jacobi_readout (x : FreudenthalCharge J) :
    fiveGradedBracket D (genEminus D 1)
        (fiveGradedBracket D (injChargeMinus D x) (genEplus D 1)) +
      fiveGradedBracket D (injChargeMinus D x)
        (fiveGradedBracket D (genEplus D 1) (genEminus D 1)) +
      fiveGradedBracket D (genEplus D 1)
        (fiveGradedBracket D (genEminus D 1) (injChargeMinus D x)) =
      injChargeMinus D ((2 : ℝ) • x) := by
  rw [legacy_minus1_plus2, legacy_minus2_plus1,
    legacy_plus2_minus2, legacy_minus1_scale,
    legacy_minus2_minus1]
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, injChargeMinus, genEplus, two_smul]

theorem two_smul_alphaCharge_ne_zero :
    (2 : ℝ) • alphaCharge (J := J) ≠ 0 := by
  intro h
  have hα := congrArg
    (fun x : FreudenthalCharge J => x.alpha) h
  change (2 : ℝ) * 1 = 0 at hα
  norm_num at hα

theorem injected_two_alphaCharge_ne_zero :
    injChargeMinus D ((2 : ℝ) • alphaCharge (J := J)) ≠ 0 := by
  intro h
  have hm := congrArg
    (fun u : FiveGradedCarrier D => u.minus1) h
  exact two_smul_alphaCharge_ne_zero (J := J)
    (by simpa [injChargeMinus] using hm)

theorem legacy_fiveGradedBracket_not_jacobi :
    ¬ (∀ u v w : FiveGradedCarrier D,
      fiveGradedBracket D u (fiveGradedBracket D v w) +
        fiveGradedBracket D v (fiveGradedBracket D w u) +
        fiveGradedBracket D w (fiveGradedBracket D u v) = 0) := by
  intro h
  have hj := h
    (genEminus D 1)
    (injChargeMinus D (alphaCharge (J := J)))
    (genEplus D 1)
  rw [legacy_extreme_charge_jacobi_readout] at hj
  exact injected_two_alphaCharge_ne_zero D hj

end InfoGeometry.Exceptional.Freudenthal
