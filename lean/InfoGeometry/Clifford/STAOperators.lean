import InfoGeometry.Clifford.CrawfordDiracBispinorDensities
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite spacetime-algebra operator dictionary

This module records the Lean-native finite matrix lane suggested by Doran,
Lasenby, and Gull's spacetime-algebra translation of states and operators.

It deliberately proves only coordinate facts over the existing Crawford/Dirac
gamma matrices.  No spacetime-algebra witness packet is introduced: the scalar
imaginary replacement and the two-sided gamma actions are concrete matrix
operations with kernel-checked square laws.
-/

namespace InfoGeometry
namespace Clifford
namespace STAOperators

open CrawfordDiracBispinorDensities

/-! ## Abstract two-sided operator calculus -/

/-- Left multiplication as a bare algebraic operation. -/
def leftMul {A : Type*} [Mul A] (a : A) (x : A) : A :=
  a * x

/-- Right multiplication as a bare algebraic operation. -/
def rightMul {A : Type*} [Mul A] (b : A) (x : A) : A :=
  x * b

/-- Two-sided STA-style operation `x ↦ a x b`. -/
def twoSidedOp {A : Type*} [Mul A] (a b : A) (x : A) : A :=
  a * x * b

/--
Left and right multiplication commute in any associative multiplication.

This is the algebraic core of the STA replacement of one-sided matrix
operators by two-sided multivector operations.
-/
theorem leftMul_rightMul_commute
    {A : Type*} [Semigroup A] (a b x : A) :
    leftMul a (rightMul b x) = rightMul b (leftMul a x) := by
  simp [leftMul, rightMul, mul_assoc]

/-- Composition law for two-sided operations: `(a,-,b) ∘ (c,-,d) = (ac,-,db)`. -/
theorem twoSidedOp_comp
    {A : Type*} [Semigroup A] (a b c d : A) :
    Function.comp (twoSidedOp a b) (twoSidedOp c d) = twoSidedOp (a * c) (d * b) := by
  funext x
  simp [Function.comp, twoSidedOp, mul_assoc]

/-- Pointwise composition law for two-sided operations. -/
theorem twoSidedOp_comp_apply
    {A : Type*} [Semigroup A] (a b c d x : A) :
    twoSidedOp a b (twoSidedOp c d x) = twoSidedOp (a * c) (d * b) x := by
  simpa using congrFun (twoSidedOp_comp (A := A) a b c d) x

/-- A fixed right phase `I` with `I² = -1` squares to negation as a right action. -/
theorem rightMul_square_eq_neg
    {A : Type*} [Ring A] {I : A} (hI : I * I = -1) (x : A) :
    rightMul I (rightMul I x) = -x := by
  calc
    rightMul I (rightMul I x) = x * (I * I) := by
      simp [rightMul, mul_assoc]
    _ = x * (-1) := by rw [hI]
    _ = -x := by simp

/-- A fixed left phase `I` with `I² = -1` squares to negation as a left action. -/
theorem leftMul_square_eq_neg
    {A : Type*} [Ring A] {I : A} (hI : I * I = -1) (x : A) :
    leftMul I (leftMul I x) = -x := by
  calc
    leftMul I (leftMul I x) = (I * I) * x := by
      simp [leftMul, mul_assoc]
    _ = (-1) * x := by rw [hI]
    _ = -x := by simp

/-! ## Right multiplication replacements for scalar complex operators -/

/-- STA spin-plane phase bivector corresponding to right multiplication by `iσ₃`. -/
def staPhaseBivector : DiracMatrix :=
  gamma2 * gamma1

/-- STA spatial spin axis `σ₃ = γ₃γ₀`, used as the right chirality operator. -/
def staSigma3 : DiracMatrix :=
  gamma3 * gamma0

/-- Right multiplication by the STA phase bivector. -/
def rightPhase (ψ : DiracMatrix) : DiracMatrix :=
  ψ * staPhaseBivector

/-- Right multiplication by the STA spin axis. -/
def rightSigma3 (ψ : DiracMatrix) : DiracMatrix :=
  ψ * staSigma3

/-- The fixed real spin-plane phase squares to `-1`. -/
theorem staPhaseBivector_mul_self :
    staPhaseBivector * staPhaseBivector = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [staPhaseBivector, gamma1, gamma2, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.neg_apply]

/-- The right phase action is a concrete square root of `-1`. -/
theorem rightPhase_rightPhase (ψ : DiracMatrix) :
    rightPhase (rightPhase ψ) = -ψ := by
  simpa [rightPhase, rightMul] using
    rightMul_square_eq_neg (A := DiracMatrix) staPhaseBivector_mul_self ψ

/-- The STA spin-axis square is `1`. -/
theorem staSigma3_mul_self :
    staSigma3 * staSigma3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [staSigma3, gamma0, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Right multiplication by `σ₃` is an involution. -/
theorem rightSigma3_rightSigma3 (ψ : DiracMatrix) :
    rightSigma3 (rightSigma3 ψ) = ψ := by
  simp [rightSigma3, Matrix.mul_assoc, staSigma3_mul_self]

/-! ## Two-sided matrix shadows of the STA gamma action -/

/-- STA-style two-sided action: `ψ ↦ γ_μ ψ γ₀`. -/
def twoSidedGamma (mu : Fin 4) (ψ : DiracMatrix) : DiracMatrix :=
  gamma mu * ψ * gamma0

/-- Left action by a concrete Dirac gamma matrix. -/
def leftGamma (mu : Fin 4) (ψ : DiracMatrix) : DiracMatrix :=
  leftMul (gamma mu) ψ

/--
Left gamma action commutes with the fixed right STA phase action.

This is the concrete finite version of separating matrix-side operators from
the STA right-bivector replacement of the scalar imaginary.
-/
theorem leftGamma_rightPhase_commute (mu : Fin 4) (ψ : DiracMatrix) :
    leftGamma mu (rightPhase ψ) = rightPhase (leftGamma mu ψ) := by
  simpa [leftGamma, rightPhase] using
    leftMul_rightMul_commute (A := DiracMatrix) (gamma mu) staPhaseBivector ψ

/-- Minkowski square sign for the `(+---)` Dirac generators. -/
def gammaSquareSign (mu : Fin 4) : ℂ :=
  if mu = 0 then 1 else -1

/-- The two-sided `γ₀` action is an involution. -/
theorem twoSidedGamma_zero_twice (ψ : DiracMatrix) :
    twoSidedGamma 0 (twoSidedGamma 0 ψ) = ψ := by
  calc
    twoSidedGamma 0 (twoSidedGamma 0 ψ) = gamma0 * (gamma0 * ψ) := by
      simp [twoSidedGamma, gamma, gamma0_mul_self, Matrix.mul_assoc]
    _ = (gamma0 * gamma0) * ψ := by
      rw [Matrix.mul_assoc]
    _ = ψ := by
      simp [gamma0_mul_self]

/-- The two-sided `γ₁` action squares to minus the identity. -/
theorem twoSidedGamma_one_twice (ψ : DiracMatrix) :
    twoSidedGamma 1 (twoSidedGamma 1 ψ) = -ψ := by
  calc
    twoSidedGamma 1 (twoSidedGamma 1 ψ) = gamma1 * (gamma1 * ψ) := by
      simp [twoSidedGamma, gamma, gamma0_mul_self, Matrix.mul_assoc]
    _ = (gamma1 * gamma1) * ψ := by
      rw [Matrix.mul_assoc]
    _ = -ψ := by
      simp [gamma1_mul_self]

/-- The two-sided `γ₂` action squares to minus the identity. -/
theorem twoSidedGamma_two_twice (ψ : DiracMatrix) :
    twoSidedGamma 2 (twoSidedGamma 2 ψ) = -ψ := by
  calc
    twoSidedGamma 2 (twoSidedGamma 2 ψ) = gamma2 * (gamma2 * ψ) := by
      simp [twoSidedGamma, gamma, gamma0_mul_self, Matrix.mul_assoc]
    _ = (gamma2 * gamma2) * ψ := by
      rw [Matrix.mul_assoc]
    _ = -ψ := by
      simp [gamma2_mul_self]

/-- The two-sided `γ₃` action squares to minus the identity. -/
theorem twoSidedGamma_three_twice (ψ : DiracMatrix) :
    twoSidedGamma 3 (twoSidedGamma 3 ψ) = -ψ := by
  calc
    twoSidedGamma 3 (twoSidedGamma 3 ψ) = gamma3 * (gamma3 * ψ) := by
      simp [twoSidedGamma, gamma, gamma0_mul_self, Matrix.mul_assoc]
    _ = (gamma3 * gamma3) * ψ := by
      rw [Matrix.mul_assoc]
    _ = -ψ := by
      simp [gamma3_mul_self]

/--
Uniform square law for the two-sided STA gamma action.  This is the concrete
matrix form of `γ_μ ψ γ₀` carrying the same `(+---)` signs as the gamma
generators.
-/
theorem twoSidedGamma_twice (mu : Fin 4) (ψ : DiracMatrix) :
    twoSidedGamma mu (twoSidedGamma mu ψ) = gammaSquareSign mu • ψ := by
  fin_cases mu
  · simp [gammaSquareSign, twoSidedGamma_zero_twice]
  · simp [gammaSquareSign, twoSidedGamma_one_twice]
  · simp [gammaSquareSign, twoSidedGamma_two_twice]
  · simp [gammaSquareSign, twoSidedGamma_three_twice]

end STAOperators
end Clifford
end InfoGeometry
