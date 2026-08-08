import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.WeylA1Character

Finite rank-one Weyl character identity.

This file does not attempt to formalize the full Weyl character formula for an
arbitrary root system. It records the honest `A1` / `SU(2)` geometric-series
identity behind the character computation:

* a finite alternating sum of weights `x^i y^(m-i)`;
* the denominator factor `x - y`;
* the cancellation identity

  `(\sum_{i=0}^m x^i y^(m-i)) * (x - y) = x^(m+1) - y^(m+1)`.

The `SU(2)` specialization is obtained by taking `y = x⁻¹`.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.WeylA1Character

/-- The finite `A1` character numerator. -/
@[rep_depth thermo]
def a1CharacterSum {R : Type*} [Semiring R] (x y : R) (m : ℕ) : R :=
  Finset.sum (Finset.range (m + 1)) (fun i => x ^ i * y ^ (m - i))

/-- The `A1` denominator factor `x - y`. -/
@[rep_depth thermo]
def a1Denominator {R : Type*} [Ring R] (x y : R) : R :=
  x - y

/-- Finite `A1` numerator/denominator cancellation. -/
@[rep_depth thermo]
theorem a1CharacterSum_mul_denominator
    {R : Type*} [CommRing R]
    (x y : R) (m : ℕ) :
    a1CharacterSum x y m * a1Denominator x y =
      x ^ (m + 1) - y ^ (m + 1) := by
  simpa [a1CharacterSum, a1Denominator, Nat.succ_eq_add_one,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (geom_sum₂_mul x y (m + 1))

/-- Finite `A1` numerator as a quotient by the denominator factor. -/
@[rep_depth thermo]
theorem a1CharacterSum_eq_div
    {R : Type*} [Field R]
    (x y : R) (m : ℕ) (hxy : x ≠ y) :
    a1CharacterSum x y m =
      (x ^ (m + 1) - y ^ (m + 1)) / (x - y) := by
  rw [eq_div_iff (sub_ne_zero.mpr hxy)]
  exact a1CharacterSum_mul_denominator (R := R) x y m

/-- The `SU(2)` specialization: `y = x⁻¹`. -/
@[rep_depth thermo]
def su2Character {R : Type*} [DivisionRing R] (x : R) (m : ℕ) : R :=
  a1CharacterSum x x⁻¹ m

/-- The `SU(2)` character multiplied by its denominator factor. -/
@[rep_depth thermo]
theorem su2Character_mul_denominator
    {R : Type*} [Field R]
    (x : R) (m : ℕ) :
    su2Character x m * a1Denominator x x⁻¹ =
      x ^ (m + 1) - (x ^ (m + 1))⁻¹ := by
  simpa [su2Character, a1Denominator, inv_pow] using
    (a1CharacterSum_mul_denominator (R := R) x x⁻¹ m)

/-- Euler's denominator identity `e^{iθ} - e^{-iθ} = 2 i sin θ`. -/
@[rep_depth thermo]
theorem exp_I_sub_exp_neg_I_eq_two_I_sin
    (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ)) =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  have h₁ : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
  have h₂ : -Complex.I * (θ : ℂ) = (-(θ : ℂ)) * Complex.I := by ring
  rw [h₁, h₂, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.ofReal_sin]
  ring

/--
The diagonal-torus `SU(2)` character identity in exponential form:
`χ_m(e^{iθ}) (e^{iθ} - e^{-iθ}) = e^{i(m+1)θ} - e^{-i(m+1)θ}`.
-/
@[rep_depth thermo]
theorem su2Character_exp_mul_denominator
    (θ : ℝ) (m : ℕ) :
    su2Character (Complex.exp (Complex.I * (θ : ℂ))) m *
        (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) =
      Complex.exp ((m + 1) • (Complex.I * (θ : ℂ))) -
        Complex.exp (-((m + 1) • (Complex.I * (θ : ℂ)))) := by
  set z : ℂ := Complex.I * (θ : ℂ)
  have hbase :
      su2Character (Complex.exp z) m * a1Denominator (Complex.exp z) (Complex.exp z)⁻¹ =
        (Complex.exp z) ^ (m + 1) - ((Complex.exp z) ^ (m + 1))⁻¹ :=
    su2Character_mul_denominator (R := ℂ) (x := Complex.exp z) m
  have hinv : (Complex.exp z)⁻¹ = Complex.exp (-z) := by
    rw [← Complex.exp_neg]
  have hpow : (Complex.exp z) ^ (m + 1) = Complex.exp ((m + 1) • z) :=
    (Complex.exp_nsmul z (m + 1)).symm
  have hneg : -Complex.I * (θ : ℂ) = -z := by
    change -Complex.I * (θ : ℂ) = -(Complex.I * (θ : ℂ))
    ring
  rw [hneg]
  change su2Character (Complex.exp z) m * (Complex.exp z - Complex.exp (-z)) =
      Complex.exp ((m + 1) • z) - Complex.exp (-((m + 1) • z))
  calc
    su2Character (Complex.exp z) m * (Complex.exp z - Complex.exp (-z))
        = su2Character (Complex.exp z) m * a1Denominator (Complex.exp z) (Complex.exp z)⁻¹ := by
            rw [a1Denominator, hinv]
    _ = (Complex.exp z) ^ (m + 1) - ((Complex.exp z) ^ (m + 1))⁻¹ := hbase
    _ = Complex.exp ((m + 1) • z) - Complex.exp (-((m + 1) • z)) := by
          rw [hpow, ← Complex.exp_neg]

/-- `SU(2)` character written as the Weyl-type quotient. -/
@[rep_depth thermo]
theorem su2Character_eq_div
    {R : Type*} [Field R]
    (x : R) (m : ℕ) (hx : x ≠ x⁻¹) :
    su2Character x m =
      (x ^ (m + 1) - (x ^ (m + 1))⁻¹) / (x - x⁻¹) := by
  simpa [su2Character, a1Denominator, inv_pow] using
    (a1CharacterSum_eq_div (R := R) x x⁻¹ m hx)

/--
The diagonal-torus `SU(2)` Weyl quotient
`χ_m(e^{iθ}) = (e^{i(m+1)θ} - e^{-i(m+1)θ}) / (e^{iθ} - e^{-iθ})`,
under the explicit nonzero-denominator property.
-/
@[rep_depth thermo]
theorem su2Character_exp_eq_div
    (θ : ℝ) (m : ℕ)
    (hθ :
      Complex.exp (Complex.I * (θ : ℂ)) ≠ Complex.exp (-Complex.I * (θ : ℂ))) :
    su2Character (Complex.exp (Complex.I * (θ : ℂ))) m =
      (Complex.exp ((m + 1) • (Complex.I * (θ : ℂ))) -
          Complex.exp (-((m + 1) • (Complex.I * (θ : ℂ))))) /
        (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) := by
  rw [eq_div_iff (sub_ne_zero.mpr hθ)]
  exact su2Character_exp_mul_denominator θ m

/--
The diagonal-torus `SU(2)` Weyl quotient in the classical sine form
`χ_m(e^{iθ}) = sin((m+1)θ) / sin θ`, under the explicit nonzero-denominator
property.
-/
@[rep_depth thermo]
theorem su2Character_exp_eq_sin_div
    (θ : ℝ) (m : ℕ)
    (hθ : Real.sin θ ≠ 0) :
    su2Character (Complex.exp (Complex.I * (θ : ℂ))) m =
      (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) / (Real.sin θ : ℂ) := by
  have hden :
      Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ)) =
        2 * Complex.I * (Real.sin θ : ℂ) :=
    exp_I_sub_exp_neg_I_eq_two_I_sin θ
  have hden_ne :
      Complex.exp (Complex.I * (θ : ℂ)) ≠ Complex.exp (-Complex.I * (θ : ℂ)) := by
    intro h
    have hz :
        (2 * Complex.I) * (Real.sin θ : ℂ) = 0 := by
      simpa [h, mul_assoc] using hden
    have hsin_complex : (Real.sin θ : ℂ) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    exact hθ (Complex.ofReal_eq_zero.mp hsin_complex)
  rw [su2Character_exp_eq_div θ m hden_ne]
  have harg :
      (m + 1) • (Complex.I * (θ : ℂ)) =
        Complex.I * ((((m + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) := by
    simp [nsmul_eq_mul]
    ring
  have hnum :
      Complex.exp ((m + 1) • (Complex.I * (θ : ℂ))) -
          Complex.exp (-((m + 1) • (Complex.I * (θ : ℂ)))) =
        2 * Complex.I * (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) := by
    rw [harg]
    simpa using exp_I_sub_exp_neg_I_eq_two_I_sin (((m + 1 : ℕ) : ℝ) * θ)
  rw [hnum, hden]
  have hsin_complex_ne : (Real.sin θ : ℂ) ≠ 0 := by
    exact_mod_cast hθ
  field_simp [hsin_complex_ne, Complex.I_ne_zero]

/-- The `SU(2)` character as a finite alternating weight sum. -/
@[simp, rep_depth thermo]
theorem su2Character_eq_sum
    {R : Type*} [Field R]
    (x : R) (m : ℕ) :
    su2Character x m = a1CharacterSum x x⁻¹ m := rfl

end InfoGeometry.Canonical.WeylA1Character
