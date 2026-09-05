import Mathlib
import InfoGeometry.Exceptional.FreudenthalSymplecticContactRepresentation

/-!
# Explicit Jacobi counterexample for the legacy five-grade bracket

The old operation `fiveGradedBracket` cannot receive a native Lie-algebra
instance.  Its failure is already visible in the elementary homogeneous triple

`(E₋, x₋, E₊)`.

For every negative charge `x`, the cyclic Jacobi expression evaluates to
`2 • x` in grade `-1`.  Choosing the nonzero scalar-coordinate charge
`alphaCharge` gives an unconditional counterexample.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- In the legacy operation, a negative charge bracketed with the positive
extreme is sent to the positive charge lane. -/
theorem legacy_minus1_plus2
    (x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (genEplus D 1) =
      injChargePlus D x := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, injChargeMinus, injChargePlus, genEplus]

/-- In the legacy operation, the negative extreme sends a positive charge
back to the negative charge lane with the same sign. -/
theorem legacy_minus2_plus1
    (x : FreudenthalCharge J) :
    fiveGradedBracket D (genEminus D 1) (injChargePlus D x) =
      injChargeMinus D x := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, genEminus, injChargePlus, injChargeMinus]

/-- The legacy extreme bracket has the intended scale readout. -/
theorem legacy_plus2_minus2 :
    fiveGradedBracket D (genEplus D 1) (genEminus D 1) =
      genHscale D 1 := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, genEplus, genEminus, genHscale]

/-- A negative charge bracketed on the right with the scale generator has
weight `+1`. -/
theorem legacy_minus1_scale
    (x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (genHscale D 1) =
      injChargeMinus D x := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, injChargeMinus, genHscale]

/-- The negative extreme and a negative charge bracket trivially in the
legacy operation. -/
theorem legacy_minus2_minus1
    (x : FreudenthalCharge J) :
    fiveGradedBracket D (genEminus D 1) (injChargeMinus D x) = 0 := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket, genEminus, injChargeMinus]

/-- Exact cyclic Jacobi readout on `(E₋,x₋,E₊)`. -/
theorem legacy_extreme_charge_jacobi_readout
    (x : FreudenthalCharge J) :
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
  simp [injChargeMinus]

/-- The selected scalar-coordinate charge is nonzero after multiplication by
`2`. -/
theorem two_smul_alphaCharge_ne_zero :
    (2 : ℝ) • alphaCharge (J := J) ≠ 0 := by
  intro h
  have hα := congrArg
    (fun x : FreudenthalCharge J => x.alpha) h
  norm_num [alphaCharge] at hα

/-- Its negative-grade injection is nonzero. -/
theorem injected_two_alphaCharge_ne_zero :
    injChargeMinus D ((2 : ℝ) • alphaCharge (J := J)) ≠ 0 := by
  intro h
  have hm := congrArg
    (fun u : FiveGradedCarrier D => u.minus1) h
  exact two_smul_alphaCharge_ne_zero (J := J) (by simpa [injChargeMinus] using hm)

/-- The legacy bracket fails the Jacobi identity.  This theorem blocks any
attempt to install a `LieRing` or `LieAlgebra` instance using that operation. -/
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
