/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.ThermodynamicSL2MobiusFlow
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Operator-valued matrix lift of the thermodynamic Möbius flow

The scalar thermodynamic exponential matrix is mapped entrywise into
`Matrix (Fin 2) (Fin 2) A`, where `A` is an arbitrary (possibly
noncommutative) operator algebra over `ℂ`.  The resulting operator matrix acts
on arbitrary pairs of operators by the repository's denominator-free matrix
action.  The group law is proved in that operator-matrix carrier.  No scalar
projective coordinate is identified with an operator.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ThermodynamicSL2OperatorLift

open InfoGeometry.Topology.ThermodynamicSL2MobiusFlow
open InfoGeometry.OperatorAlgebra

section OrderedOperatorRiccati

variable {B : Type*} [Ring B]

/-- A trace-patterned `2 × 2` infinitesimal matrix with genuinely
operator-valued coefficients. -/
def operatorRiccatiGenerator (d b c : B) : OperatorMatrix B :=
  !![d, b; c, -d]

/-- Ordered noncommutative Riccati velocity associated with the generator
`[[d,b],[c,-d]]`.  The two dilation terms retain their distinct orders. -/
def operatorRiccatiVelocity (d b c z : B) : B :=
  b + d * z + z * d - z * c * z

/-- The two components of the operator-matrix action on the homogeneous
operator pair `(z,1)` are the numerator and denominator tangent components. -/
theorem operatorRiccatiGenerator_homogeneous_components
    (d b c z : B) :
    operatorMobiusAction (operatorRiccatiGenerator d b c) ![z, 1] 0 = d * z + b ∧
    operatorMobiusAction (operatorRiccatiGenerator d b c) ![z, 1] 1 = c * z - d := by
  constructor <;>
    simp [operatorMobiusAction_apply, operatorRiccatiGenerator, Fin.sum_univ_two] <;>
      noncomm_ring

/-- The projective tangent numerator is the order-sensitive operator Riccati
expression.  This is an identity in any unital associative ring; no quotient
or commuting coefficient assumption is used. -/
theorem operatorRiccatiGenerator_projective_tangent
    (d b c z : B) :
    operatorMobiusAction (operatorRiccatiGenerator d b c) ![z, 1] 0 -
        z * operatorMobiusAction (operatorRiccatiGenerator d b c) ![z, 1] 1 =
      operatorRiccatiVelocity d b c z := by
  rw [(operatorRiccatiGenerator_homogeneous_components d b c z).1,
    (operatorRiccatiGenerator_homogeneous_components d b c z).2]
  simp only [operatorRiccatiVelocity]
  noncomm_ring

/-- The ordered operator Riccati vector field is natural under ring
representations. In particular, a representation transports each product in
the same order; no commutation of the image coefficients is needed. -/
theorem operatorRiccatiVelocity_map
    {C : Type*} [Ring C] (φ : B →+* C) (d b c z : B) :
    φ (operatorRiccatiVelocity d b c z) =
      operatorRiccatiVelocity (φ d) (φ b) (φ c) (φ z) := by
  simp [operatorRiccatiVelocity, map_add, map_mul, map_sub]

end OrderedOperatorRiccati

section AlgebraicOperatorMatrixFlow

variable {B : Type*} [Ring B]

/-- The exact integer-time exponential along a square-zero generator in the
operator-matrix ring.  Since `G * G = 0`, its exponential polynomial truncates
to `1 + n • G`; the entries of `G` remain arbitrary elements of `B`. -/
def nilpotentOperatorMatrixFlow (G : OperatorMatrix B) (n : ℤ) : OperatorMatrix B :=
  1 + n • G

/-- The square-zero operator-matrix flow obeys the additive-time law. -/
theorem nilpotentOperatorMatrixFlow_add
    (G : OperatorMatrix B) (hG : G * G = 0) (m n : ℤ) :
    nilpotentOperatorMatrixFlow G (m + n) =
      nilpotentOperatorMatrixFlow G m * nilpotentOperatorMatrixFlow G n := by
  simp only [nilpotentOperatorMatrixFlow, zsmul_eq_mul]
  calc
    1 + ((m + n : ℤ) : OperatorMatrix B) * G =
        1 + (m : OperatorMatrix B) * G + (n : OperatorMatrix B) * G := by
          simp only [Int.cast_add, add_mul]
          abel
    _ = (1 + (m : OperatorMatrix B) * G) *
        (1 + (n : OperatorMatrix B) * G) := by
          have hcomm : G * (n : OperatorMatrix B) =
              (n : OperatorMatrix B) * G := (Int.commute_cast G n).eq
          have hcross : ((m : OperatorMatrix B) * G) *
              ((n : OperatorMatrix B) * G) = 0 := by
            calc
              ((m : OperatorMatrix B) * G) * ((n : OperatorMatrix B) * G) =
                  (m : OperatorMatrix B) * (n : OperatorMatrix B) * (G * G) := by
                    calc
                      ((m : OperatorMatrix B) * G) * ((n : OperatorMatrix B) * G) =
                          (m : OperatorMatrix B) * (G * (n : OperatorMatrix B)) * G := by
                            noncomm_ring
                      _ = (m : OperatorMatrix B) * ((n : OperatorMatrix B) * G) * G := by
                            rw [hcomm]
                      _ = (m : OperatorMatrix B) * (n : OperatorMatrix B) * (G * G) := by
                            noncomm_ring
              _ = 0 := by rw [hG]; simp
          calc
            1 + (m : OperatorMatrix B) * G + (n : OperatorMatrix B) * G =
                1 + (m : OperatorMatrix B) * G +
                  (n : OperatorMatrix B) * G +
                  ((m : OperatorMatrix B) * G) * ((n : OperatorMatrix B) * G) := by
                    rw [hcross]
                    abel
            _ = (1 + (m : OperatorMatrix B) * G) *
                (1 + (n : OperatorMatrix B) * G) := by
                  noncomm_ring

/-- Negative integer time is a two-sided inverse in `M₂(B)`. -/
theorem nilpotentOperatorMatrixFlow_inverse
    (G : OperatorMatrix B) (hG : G * G = 0) (n : ℤ) :
    nilpotentOperatorMatrixFlow G (-n) * nilpotentOperatorMatrixFlow G n = 1 ∧
    nilpotentOperatorMatrixFlow G n * nilpotentOperatorMatrixFlow G (-n) = 1 := by
  constructor
  · rw [← nilpotentOperatorMatrixFlow_add G hG (-n) n]
    simp [nilpotentOperatorMatrixFlow]
  · rw [← nilpotentOperatorMatrixFlow_add G hG n (-n)]
    simp [nilpotentOperatorMatrixFlow]

end AlgebraicOperatorMatrixFlow

section PeirceAdaptedOperatorPowers

variable {A : Type*} [Ring A]

/-- The symmetry-adapted Peirce-odd generator in `M₂(A)`. Its off-diagonal
entries are arbitrary operators and retain their order under multiplication. -/
def peirceOffDiagonalGenerator (a c : A) : OperatorMatrix A :=
  !![0, a; c, 0]

/-- The diagonal operator matrix containing the two ordered corner products. -/
def peirceEvenPower (a c : A) (n : ℕ) : OperatorMatrix A :=
  !![(a * c) ^ n, 0; 0, (c * a) ^ n]

/-- Squaring the Peirce-odd generator gives the two corner metrics `ac` and
`ca`; no equality between those products is assumed. -/
theorem peirceOffDiagonalGenerator_sq (a c : A) :
    peirceOffDiagonalGenerator a c * peirceOffDiagonalGenerator a c =
      peirceEvenPower a c 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceOffDiagonalGenerator, peirceEvenPower, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Every even power of a symmetry-adapted off-diagonal operator generator is
diagonal, with the two ordered corner powers `(ac)^n` and `(ca)^n`. -/
theorem peirceOffDiagonalGenerator_pow_even (a c : A) (n : ℕ) :
    peirceOffDiagonalGenerator a c ^ (2 * n) = peirceEvenPower a c n := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [peirceEvenPower]
  | succ n ih =>
      have hGsq : peirceOffDiagonalGenerator a c ^ 2 = peirceEvenPower a c 1 := by
        simpa only [pow_two] using peirceOffDiagonalGenerator_sq a c
      calc
        peirceOffDiagonalGenerator a c ^ (2 * (n + 1)) =
            peirceOffDiagonalGenerator a c ^ (2 * n + 2) := by
              congr 1 <;> omega
        _ = peirceOffDiagonalGenerator a c ^ (2 * n) *
            peirceOffDiagonalGenerator a c ^ 2 := by rw [pow_add]
        _ = peirceEvenPower a c n * peirceEvenPower a c 1 := by rw [ih, hGsq]
        _ = peirceEvenPower a c (n + 1) := by
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [peirceEvenPower, Matrix.mul_apply, Fin.sum_univ_two,
                  pow_succ, mul_assoc]

/-- Every odd power is the preceding diagonal corner power followed by the
original Peirce-odd generator. This fixes multiplication order explicitly. -/
theorem peirceOffDiagonalGenerator_pow_odd (a c : A) (n : ℕ) :
    peirceOffDiagonalGenerator a c ^ (2 * n + 1) =
      peirceEvenPower a c n * peirceOffDiagonalGenerator a c := by
  rw [pow_add, pow_one, peirceOffDiagonalGenerator_pow_even]

end PeirceAdaptedOperatorPowers

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The thermodynamic exponential flow with every entry regarded as an
operator in `A` through its canonical complex algebra map. -/
def thermodynamicOperatorMatrixFlow
    (translation dilation specialConformal : ℝ) (t : ℂ) : OperatorMatrix A :=
  fun i j => algebraMap ℂ A
    (thermodynamicSL2MatrixFlow translation dilation specialConformal t i j)

/-- The operator-valued coefficient matrices inherit the finite
one-parameter group law. -/
theorem thermodynamicOperatorMatrixFlow_add
    (translation dilation specialConformal : ℝ) (s t : ℂ) :
    thermodynamicOperatorMatrixFlow (A := A) translation dilation specialConformal (s + t) =
      thermodynamicOperatorMatrixFlow translation dilation specialConformal s *
        thermodynamicOperatorMatrixFlow translation dilation specialConformal t := by
  ext i j
  change algebraMap ℂ A
      (thermodynamicSL2MatrixFlow translation dilation specialConformal (s + t) i j) =
    ∑ k, algebraMap ℂ A
        (thermodynamicSL2MatrixFlow translation dilation specialConformal s i k) *
      algebraMap ℂ A
        (thermodynamicSL2MatrixFlow translation dilation specialConformal t k j)
  rw [thermodynamicSL2MatrixFlow_add]
  simp [Matrix.mul_apply]

@[simp] theorem thermodynamicOperatorMatrixFlow_zero
    (translation dilation specialConformal : ℝ) :
    thermodynamicOperatorMatrixFlow (A := A) translation dilation specialConformal 0 = 1 := by
  ext i j
  change algebraMap ℂ A
      (thermodynamicSL2MatrixFlow translation dilation specialConformal 0 i j) =
    (1 : OperatorMatrix A) i j
  rw [thermodynamicSL2MatrixFlow_zero]
  simp only [Matrix.one_apply]
  split <;> simp

/-- The thermodynamic exponential acts on a pair of arbitrary, potentially
noncommuting operators using a `2 × 2` matrix whose entries lie in the
operator ring. -/
def thermodynamicOperatorMobiusFlow
    (translation dilation specialConformal : ℝ) (t : ℂ)
    (v : OperatorPair A) : OperatorPair A :=
  operatorMobiusAction
    (thermodynamicOperatorMatrixFlow (A := A) translation dilation specialConformal t) v

/-- The operator-valued Möbius action has the same additive-time composition
law as its source exponential matrix.  The equality is in `A²` and uses the
noncommutative operator-matrix multiplication law. -/
theorem thermodynamicOperatorMobiusFlow_add
    (translation dilation specialConformal : ℝ) (s t : ℂ)
    (v : OperatorPair A) :
    thermodynamicOperatorMobiusFlow (A := A) translation dilation specialConformal (s + t) v =
      thermodynamicOperatorMobiusFlow translation dilation specialConformal s
        (thermodynamicOperatorMobiusFlow translation dilation specialConformal t v) := by
  unfold thermodynamicOperatorMobiusFlow
  rw [thermodynamicOperatorMatrixFlow_add, operatorMobiusAction_mul]

/-- The lifted operator-pair flow is exactly reversible by negative time. -/
theorem thermodynamicOperatorMobiusFlow_inverse
    (translation dilation specialConformal : ℝ) (t : ℂ)
    (v : OperatorPair A) :
    thermodynamicOperatorMobiusFlow (A := A) translation dilation specialConformal (-t)
        (thermodynamicOperatorMobiusFlow translation dilation specialConformal t v) = v ∧
    thermodynamicOperatorMobiusFlow translation dilation specialConformal t
        (thermodynamicOperatorMobiusFlow translation dilation specialConformal (-t) v) = v := by
  constructor
  · calc
      thermodynamicOperatorMobiusFlow (A := A) translation dilation specialConformal (-t)
          (thermodynamicOperatorMobiusFlow translation dilation specialConformal t v) =
        thermodynamicOperatorMobiusFlow translation dilation specialConformal ((-t) + t) v :=
          (thermodynamicOperatorMobiusFlow_add translation dilation specialConformal (-t) t v).symm
      _ = v := by
        rw [show (-t) + t = 0 by ring, thermodynamicOperatorMobiusFlow,
          thermodynamicOperatorMatrixFlow_zero, operatorMobiusAction_one]
  · calc
      thermodynamicOperatorMobiusFlow (A := A) translation dilation specialConformal t
          (thermodynamicOperatorMobiusFlow translation dilation specialConformal (-t) v) =
        thermodynamicOperatorMobiusFlow translation dilation specialConformal (t + (-t)) v :=
          (thermodynamicOperatorMobiusFlow_add translation dilation specialConformal t (-t) v).symm
      _ = v := by
        rw [show t + (-t) = 0 by ring, thermodynamicOperatorMobiusFlow,
          thermodynamicOperatorMatrixFlow_zero, operatorMobiusAction_one]

end InfoGeometry.OperatorAlgebra.ThermodynamicSL2OperatorLift

end
