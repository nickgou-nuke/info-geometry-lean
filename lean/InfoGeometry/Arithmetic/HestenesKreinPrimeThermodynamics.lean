import Mathlib

/-!
# InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics

Native split-complex carrier for the Hestenes--Krein prime thermodynamic lane.

This module keeps the algebra explicit:

* split-complex numbers as a real/ hyperbolic pair,
* the hyperbolic unit `j`,
* split Souriau temperatures `σ + j t`,
* the antiunitary reflection `s ↦ 1 - \bar s`,
* a finite normalized prime holonomy readout.

No sockets.
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

/-- The split norm is multiplicative. -/
theorem norm_mul (x y : SplitComplex) :
    norm (mul x y) = norm x * norm y := by
  cases x <;> cases y <;> simp [norm, leftPart, rightPart, mul] <;> ring

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

/-- Split reflection swapping the light-cone coordinates. -/
def antiunitaryReflection (s : SplitSouriauTemperature) : SplitSouriauTemperature :=
  ⟨1 - s.sigma, s.time⟩

/-- Critical line in the split-temperature plane. -/
def CriticalLine (s : SplitSouriauTemperature) : Prop :=
  s.sigma = (1 / 2 : ℝ)

@[simp]
theorem antiunitaryReflection_involutive (s : SplitSouriauTemperature) :
    antiunitaryReflection (antiunitaryReflection s) = s := by
  cases s
  simp [antiunitaryReflection]

/-- The antiunitary reflection preserves the critical line. -/
theorem antiunitaryReflection_preserves_criticalLine
    (s : SplitSouriauTemperature) (hs : CriticalLine s) :
    CriticalLine (antiunitaryReflection s) := by
  unfold CriticalLine antiunitaryReflection at *
  linarith

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

end InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
