import Mathlib.Tactic

/-!
# InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics

Native split-complex carrier for the Hestenes--Krein prime thermodynamic lane.

This module keeps the algebra explicit:

* split-complex numbers as a real/ hyperbolic pair,
* the hyperbolic unit `j`,
* split Souriau temperatures `σ + j t`,
* the split reflection `σ ↦ 1 - σ` with `t` fixed,
* a finite normalized prime holonomy readout.

No placeholder interfaces.
No certificates.
No analytic continuation theorem.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics

/-- A split-complex number in the standard `a + j b` basis. -/
@[ext]
structure SplitComplex where
  re : ℝ
  hyp : ℝ

namespace SplitComplex

/-- Addition of split-complex numbers. -/
def add (x y : SplitComplex) : SplitComplex :=
  ⟨x.re + y.re, x.hyp + y.hyp⟩

/-- Negation of split-complex numbers. -/
def neg (x : SplitComplex) : SplitComplex :=
  ⟨-x.re, -x.hyp⟩

/-- Multiplication of split-complex numbers. -/
def mul (x y : SplitComplex) : SplitComplex :=
  ⟨x.re * y.re + x.hyp * y.hyp, x.re * y.hyp + x.hyp * y.re⟩

/-- Scalar multiplication of split-complex numbers. -/
def smul (a : ℝ) (x : SplitComplex) : SplitComplex :=
  ⟨a * x.re, a * x.hyp⟩

/-- The additive zero split-complex number. -/
def zero : SplitComplex :=
  ⟨0, 0⟩

/-- The multiplicative identity split-complex number. -/
def one : SplitComplex :=
  ⟨1, 0⟩

/-- The hyperbolic unit `j`. -/
def j : SplitComplex :=
  ⟨0, 1⟩

/-- Left chiral coordinate `x + y`. -/
def leftPart (x : SplitComplex) : ℝ :=
  x.re + x.hyp

/-- Right chiral coordinate `x - y`. -/
def rightPart (x : SplitComplex) : ℝ :=
  x.re - x.hyp

/-- Split norm readout `leftPart * rightPart`. -/
def norm (x : SplitComplex) : ℝ :=
  leftPart x * rightPart x

/-- Reconstruct a split-complex number from its left/right coordinates. -/
def reconstruct (u v : ℝ) : SplitComplex :=
  ⟨(u + v) / 2, (u - v) / 2⟩

@[simp]
theorem leftPart_reconstruct (u v : ℝ) :
    leftPart (reconstruct u v) = u := by
  unfold leftPart reconstruct
  ring

@[simp]
theorem rightPart_reconstruct (u v : ℝ) :
    rightPart (reconstruct u v) = v := by
  unfold rightPart reconstruct
  ring

@[simp]
theorem norm_reconstruct (u v : ℝ) :
    norm (reconstruct u v) = u * v := by
  unfold norm reconstruct leftPart rightPart
  ring

@[simp]
theorem j_mul_j : mul j j = one := by
  ext <;> simp [mul, j, one]

/--
The split generator `j` produces explicit nonzero zero divisors:
`(1 + j)(1 - j) = 0`.

This is the precise split-sign theorem.  The factors are zero divisors, but
they are not nilpotent.
-/
theorem one_add_j_mul_one_sub_j_zero :
    mul (add one j) (add one (neg j)) = zero := by
  ext <;> norm_num [add, mul, neg, one, j, zero]

theorem one_add_j_ne_zero :
    add one j ≠ zero := by
  intro h
  have h' := congrArg SplitComplex.re h
  norm_num [add, one, j, zero] at h'

theorem one_sub_j_ne_zero :
    add one (neg j) ≠ zero := by
  intro h
  have h' := congrArg SplitComplex.re h
  norm_num [add, neg, one, j, zero] at h'

/-- The zero divisors are not nilpotent. -/
theorem one_add_j_sq :
    mul (add one j) (add one j) = add (add one j) (add one j) := by
  ext <;> norm_num [add, mul, one, j]

theorem one_sub_j_sq :
    mul (add one (neg j)) (add one (neg j)) = add (add one (neg j)) (add one (neg j)) := by
  ext <;> norm_num [add, mul, neg, one, j]

theorem one_add_j_sq_ne_zero :
    mul (add one j) (add one j) ≠ zero := by
  rw [one_add_j_sq]
  intro h
  have h' := congrArg SplitComplex.re h
  norm_num [add, one, j, zero] at h'

theorem one_sub_j_sq_ne_zero :
    mul (add one (neg j)) (add one (neg j)) ≠ zero := by
  rw [one_sub_j_sq]
  intro h
  have h' := congrArg SplitComplex.re h
  norm_num [add, neg, one, j, zero] at h'

/-- The split sign has explicit nonzero zero divisors. -/
theorem split_sign_has_nonzero_zero_divisors :
    ∃ u v : SplitComplex, u ≠ zero ∧ v ≠ zero ∧ mul u v = zero := by
  refine ⟨add one j, add one (neg j), one_add_j_ne_zero, one_sub_j_ne_zero, ?_⟩
  exact one_add_j_mul_one_sub_j_zero

@[simp]
theorem leftPart_mul (x y : SplitComplex) :
    leftPart (mul x y) = leftPart x * leftPart y := by
  cases x <;> cases y <;> simp [leftPart, mul] <;> ring

@[simp]
theorem rightPart_mul (x y : SplitComplex) :
    rightPart (mul x y) = rightPart x * rightPart y := by
  cases x <;> cases y <;> simp [rightPart, mul] <;> ring

/-- Multiplication diagonalizes in the left/right coordinate basis. -/
theorem reconstruct_mul (u v u' v' : ℝ) :
    mul (reconstruct u v) (reconstruct u' v') =
      reconstruct (u * u') (v * v') := by
  ext <;> simp [mul, reconstruct] <;> ring

/-- Split conjugation reverses the hyperbolic coordinate. -/
def reverse (x : SplitComplex) : SplitComplex :=
  reconstruct (rightPart x) (leftPart x)

theorem mul_reverse_eq_norm_smul_one (x : SplitComplex) :
    mul x (reverse x) = smul (norm x) one := by
  cases x <;>
    simp [reverse, norm, leftPart, rightPart, reconstruct, mul, smul, one] <;>
    constructor <;> ring

theorem mul_reverse_eq_one_of_norm_one
    (x : SplitComplex) (hx : norm x = 1) :
    mul x (reverse x) = one := by
  rw [mul_reverse_eq_norm_smul_one, hx]
  simp [smul, one]

/-- The split norm is multiplicative. -/
theorem norm_mul (x y : SplitComplex) :
    norm (mul x y) = norm x * norm y := by
  cases x <;> cases y <;> simp [norm, leftPart, rightPart, mul] <;> ring

/-- Left multiplication by a norm-one split-complex unit preserves the split norm. -/
theorem norm_mul_left_of_norm_one (x y : SplitComplex) (hx : norm x = 1) :
    norm (mul x y) = norm y := by
  rw [norm_mul, hx, one_mul]

/-- Right multiplication by a norm-one split-complex unit preserves the split norm. -/
theorem norm_mul_right_of_norm_one (x y : SplitComplex) (hx : norm x = 1) :
    norm (mul y x) = norm y := by
  rw [norm_mul, hx, mul_one]

end SplitComplex

open SplitComplex

/-- Split Souriau temperature `σ + j t`. -/
@[ext]
structure SplitSouriauTemperature where
  sigma : ℝ
  time : ℝ

/-- View a split Souriau temperature as a split-complex number. -/
def splitTemperatureAsNumber (s : SplitSouriauTemperature) : SplitComplex :=
  ⟨s.sigma, s.time⟩

/-- Left light-cone coordinate `u = σ + t`. -/
def leftCone (s : SplitSouriauTemperature) : ℝ :=
  s.sigma + s.time

/-- Right light-cone coordinate `v = σ - t`. -/
def rightCone (s : SplitSouriauTemperature) : ℝ :=
  s.sigma - s.time

/-- Split reflection with `t` fixed. -/
def splitReflection (s : SplitSouriauTemperature) : SplitSouriauTemperature :=
  ⟨1 - s.sigma, s.time⟩

/-- Compatibility alias for the split reflection. -/
abbrev antiunitaryReflection := splitReflection

/-- Carrier-level split reflection in left/right coordinates. -/
def splitReflectionComplex (z : SplitComplex) : SplitComplex :=
  reconstruct (1 - rightPart z) (1 - leftPart z)

/-- Critical line in the split-temperature plane. -/
def CriticalLine (s : SplitSouriauTemperature) : Prop :=
  s.sigma = (1 / 2 : ℝ)

@[simp]
theorem antiunitaryReflection_involutive (s : SplitSouriauTemperature) :
    splitReflection (splitReflection s) = s := by
  cases s
  simp [splitReflection]

/-- The antiunitary reflection preserves the critical line. -/
theorem antiunitaryReflection_preserves_criticalLine
    (s : SplitSouriauTemperature) (hs : CriticalLine s) :
    CriticalLine (splitReflection s) := by
  unfold CriticalLine splitReflection at *
  linarith

@[simp]
theorem splitReflectionComplex_leftPart (z : SplitComplex) :
    leftPart (splitReflectionComplex z) = 1 - rightPart z := by
  simp [splitReflectionComplex]

@[simp]
theorem splitReflectionComplex_rightPart (z : SplitComplex) :
    rightPart (splitReflectionComplex z) = 1 - leftPart z := by
  simp [splitReflectionComplex]

@[simp]
theorem splitReflectionComplex_involutive (z : SplitComplex) :
    splitReflectionComplex (splitReflectionComplex z) = z := by
  cases z
  ext <;> simp [splitReflectionComplex, leftPart, rightPart, reconstruct] <;> ring

/-- The carrier-level split reflection matches the split-temperature reflection. -/
theorem splitReflectionComplex_eq_splitTemperatureAsNumber
    (s : SplitSouriauTemperature) :
    splitReflectionComplex (splitTemperatureAsNumber s) =
      splitTemperatureAsNumber (splitReflection s) := by
  cases s
  ext <;> simp [splitReflectionComplex, splitTemperatureAsNumber,
    splitReflection, leftPart, rightPart, reconstruct] <;> ring

/-- Split-complex normalized holonomy on a finite prime cutoff. -/
def normalizedPrimeHolonomySplit (sigma t period : ℝ) : SplitComplex :=
  reconstruct
    (Real.exp ((((1 : ℝ) / 2) - sigma - t) * period))
    (Real.exp ((((1 : ℝ) / 2) - sigma + t) * period))

/-- On the critical line, the split norm of the normalized holonomy is `1`. -/
theorem normalizedPrimeHolonomySplit_norm_eq_one_of_critical
    (sigma t period : ℝ) (hσ : sigma = (1 / 2 : ℝ)) :
    SplitComplex.norm (normalizedPrimeHolonomySplit sigma t period) = 1 := by
  rw [hσ]
  simp [normalizedPrimeHolonomySplit, SplitComplex.norm]
  rw [← Real.exp_add]
  have hsum : (-(t * period) + t * period) = 0 := by
    ring
  rw [hsum, Real.exp_zero]

/-- The critical normalized holonomy has the explicit split inverse `reverse`. -/
theorem normalizedPrimeHolonomySplit_mul_reverse_eq_one_of_critical
    (sigma t period : ℝ) (hσ : sigma = (1 / 2 : ℝ)) :
    SplitComplex.mul
        (normalizedPrimeHolonomySplit sigma t period)
        (SplitComplex.reverse
          (normalizedPrimeHolonomySplit sigma t period)) =
      SplitComplex.one := by
  apply SplitComplex.mul_reverse_eq_one_of_norm_one
  exact normalizedPrimeHolonomySplit_norm_eq_one_of_critical sigma t period hσ

end InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
