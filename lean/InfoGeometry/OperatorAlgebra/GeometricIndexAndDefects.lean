/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce

/-!
# Algebraic matrix identities for graded index, defects, and gluing

All carrier-level claims in this file concern `M₂(A)` for an arbitrary
noncommutative ring `A`; the gluing-adjoint claims additionally assume
`[StarRing A]`.  No Fredholm operator, determinant line, projective state
space, positivity cone, cobordism functor, or analytic index is constructed.

The dependency order is a common matrix/Peirce base followed by independent
families: lift multiplication and its defect (D₁); a diagonal-difference
invariance identity (D₂); graded square and associative Bianchi identities
(D₃); Peirce and Walsh defect relations (D₄); and, with a star structure,
adjoint gluing decomposition (D₅).  These algebraic families do not imply one
another's geometric or analytic interpretations.
-/

namespace InfoGeometry.OperatorAlgebra.GeometricIndexAndDefects

open Matrix
open InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce

variable {A : Type*} [Ring A]

abbrev Op₂ (A : Type*) := Matrix (Fin 2) (Fin 2) A

def opComm {R : Type*} [Ring R] (x y : R) : R := x * y - y * x
def opAnticomm {R : Type*} [Ring R] (x y : R) : R := x * y + y * x

/-! ## D₁. Lift multiplication defect and diagonal correction
The cocycle terminology below means the displayed associativity equation for
the multiplication defect.  It does not package a projective representation
or a physical anomaly theory.
-/

def liftW (a b : A) : Op₂ A := !![1, a; b, 1]

def liftDefect (a₁ b₁ a₂ b₂ : A) : Op₂ A :=
  !![a₁ * b₂, 0; 0, b₁ * a₂]

theorem liftW_mul_defect (a₁ b₁ a₂ b₂ : A) :
    liftW a₁ b₁ * liftW a₂ b₂ =
      liftW (a₁ + a₂) (b₁ + b₂) + liftDefect a₁ b₁ a₂ b₂ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [liftW, liftDefect, Matrix.mul_apply, Fin.sum_univ_two] <;> abel

/-- After subtracting the additive lift, the multiplication defect lies wholly
in the even Peirce sector. This identifies the diagonal obstruction with the
existing operator grading rather than treating it as an untyped correction. -/
theorem liftW_defect_even (a₁ b₁ a₂ b₂ : A) :
    evenPart (liftW a₁ b₁ * liftW a₂ b₂ -
      liftW (a₁ + a₂) (b₁ + b₂)) = liftDefect a₁ b₁ a₂ b₂ := by
  have hdev : liftW a₁ b₁ * liftW a₂ b₂ -
      liftW (a₁ + a₂) (b₁ + b₂) = liftDefect a₁ b₁ a₂ b₂ := by
    rw [liftW_mul_defect]
    noncomm_ring
  rw [hdev]
  ext i j; fin_cases i <;> fin_cases j <;> simp [evenPart, liftDefect]

/-- The same lift defect has no odd Peirce component. -/
theorem liftW_defect_odd_zero (a₁ b₁ a₂ b₂ : A) :
    oddPart (liftW a₁ b₁ * liftW a₂ b₂ -
      liftW (a₁ + a₂) (b₁ + b₂)) = 0 := by
  have hdev : liftW a₁ b₁ * liftW a₂ b₂ -
      liftW (a₁ + a₂) (b₁ + b₂) = liftDefect a₁ b₁ a₂ b₂ := by
    rw [liftW_mul_defect]
    noncomm_ring
  rw [hdev]
  ext i j; fin_cases i <;> fin_cases j <;> simp [oddPart, liftDefect]

theorem liftDefect_associativity (a₁ b₁ a₂ b₂ a₃ b₃ : A) :
    liftDefect a₁ b₁ a₂ b₂ + liftDefect (a₁ + a₂) (b₁ + b₂) a₃ b₃ =
      liftDefect a₁ b₁ (a₂ + a₃) (b₂ + b₃) + liftDefect a₂ b₂ a₃ b₃ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [liftDefect] <;> noncomm_ring

def countertermLift (a b cPlus cMinus : A) : Op₂ A :=
  !![1 + cPlus, a; b, 1 + cMinus]

theorem liftDefect_cancelled_by_counterterm (a₁ b₁ a₂ b₂ : A) :
    liftW a₁ b₁ * liftW a₂ b₂ +
        (countertermLift 0 0 (-a₁ * b₂) (-b₁ * a₂) - 1) =
      liftW (a₁ + a₂) (b₁ + b₂) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [liftW, countertermLift]; abel

def mellinDilation (u : Aˣ) : Op₂ A := !![(u : A), 0; 0, (↑u⁻¹ : A)]

theorem liftW_mellin_covariant (a b : A) (u : Aˣ) :
    mellinDilation u * liftW a b * mellinDilation u⁻¹ =
      liftW ((u : A) * a * (u : A)) ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) := by
  have h₁ : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h₂ : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mellinDilation, liftW, h₁, h₂]

def mellinConjugateDefect (a₁ b₁ a₂ b₂ : A) (u : Aˣ) : Op₂ A :=
  mellinDilation u * liftDefect a₁ b₁ a₂ b₂ * mellinDilation u⁻¹

theorem liftDefect_mellin_covariant (a₁ b₁ a₂ b₂ : A) (u : Aˣ) :
    liftDefect
        ((u : A) * a₁ * (u : A)) ((↑u⁻¹ : A) * b₁ * (↑u⁻¹ : A))
        ((u : A) * a₂ * (u : A)) ((↑u⁻¹ : A) * b₂ * (↑u⁻¹ : A)) =
      mellinConjugateDefect a₁ b₁ a₂ b₂ u := by
  have h₁ : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h₂ : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  ext i j; fin_cases i <;> fin_cases j
  · simp [liftDefect, mellinConjugateDefect, mellinDilation,
      Matrix.mul_apply, Fin.sum_univ_two]
    calc
      ((u : A) * a₁ * (u : A)) * ((↑u⁻¹ : A) * b₂ * (↑u⁻¹ : A)) =
          (u : A) * (a₁ * ((u : A) * (↑u⁻¹ : A)) * b₂) * (↑u⁻¹ : A) := by
            noncomm_ring
      _ = (u : A) * (a₁ * b₂) * (↑u⁻¹ : A) := by rw [h₁]; noncomm_ring
  · simp [liftDefect, mellinConjugateDefect, mellinDilation]
  · simp [liftDefect, mellinConjugateDefect, mellinDilation]
  · simp [liftDefect, mellinConjugateDefect, mellinDilation,
      Matrix.mul_apply, Fin.sum_univ_two]
    calc
      ((↑u⁻¹ : A) * b₁ * (↑u⁻¹ : A)) * ((u : A) * a₂ * (u : A)) =
          (↑u⁻¹ : A) * (b₁ * ((↑u⁻¹ : A) * (u : A)) * a₂) * (u : A) := by
            noncomm_ring
      _ = (↑u⁻¹ : A) * (b₁ * a₂) * (u : A) := by rw [h₂]; noncomm_ring

/-! The proposed supertrace/index-jump claim is intentionally not represented
by a difference of two matrix entries here: over a noncommutative coefficient
ring that functional is not generally cyclic, and an equal-diagonal-shift
calculation alone is not an index theorem.  The actual Peirce grading lives in
`InfoGeometry.Algebra.PeirceDeWittChiralSplit`; Fredholm/index consequences
require additional analytic structure.
-/

/-! ## D₃. Graded matrix square, Bianchi identity, and algebraic transgression -/

def evenConnection (aPlus aMinus : A) : Op₂ A := !![aPlus, 0; 0, aMinus]
def oddOperator (lPlus lMinus : A) : Op₂ A := !![0, lMinus; lPlus, 0]
def superconnectionMatrix (aPlus aMinus lPlus lMinus : A) : Op₂ A :=
  evenConnection aPlus aMinus + oddOperator lPlus lMinus

theorem superconnection_square_even (aPlus aMinus lPlus lMinus : A) :
    evenPart (superconnectionMatrix aPlus aMinus lPlus lMinus *
      superconnectionMatrix aPlus aMinus lPlus lMinus) =
      !![aPlus * aPlus + lMinus * lPlus, 0; 0, aMinus * aMinus + lPlus * lMinus] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, superconnectionMatrix, evenConnection, oddOperator,
      Matrix.mul_apply, Fin.sum_univ_two]; abel

theorem superconnection_square_odd (aPlus aMinus lPlus lMinus : A) :
    oddPart (superconnectionMatrix aPlus aMinus lPlus lMinus *
      superconnectionMatrix aPlus aMinus lPlus lMinus) =
      opAnticomm (evenConnection aPlus aMinus) (oddOperator lPlus lMinus) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddPart, opAnticomm, superconnectionMatrix, evenConnection,
      oddOperator, Matrix.mul_apply, Fin.sum_univ_two]; abel

theorem associative_bianchi (X : Op₂ A) : opComm X (X * X) = 0 := by
  dsimp [opComm]
  noncomm_ring

def bianchiDerivative {R : Type*} [Ring R] (D Φ : R) : R := opComm D Φ
def totalCurvature {R : Type*} [Ring R] (Φ D : R) : R := Φ + D * D
def chernSimonsElement {R : Type*} [Ring R] (Φ D : R) : R :=
  Φ * D + D * Φ + D * D * D

theorem algebraic_chern_simons_transgression {R : Type*} [Ring R] (Φ D : R) :
    opAnticomm D (chernSimonsElement Φ D) -
        opComm (bianchiDerivative D Φ) D + 2 * (Φ * Φ) =
      2 * (totalCurvature Φ D * totalCurvature Φ D) := by
  dsimp [opAnticomm, opComm, bianchiDerivative, chernSimonsElement,
    totalCurvature]
  noncomm_ring

/-! ## D₄. Peirce and Walsh defect operator identities -/

def chiralHamiltonian (hPlus hMinus : A) : Op₂ A := !![hPlus, 0; 0, hMinus]

theorem pPlus_commutes_chiralHamiltonian (hPlus hMinus : A) :
    opComm (pPlus : Op₂ A) (chiralHamiltonian hPlus hMinus) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [opComm, pPlus, chiralHamiltonian]

theorem pMinus_commutes_chiralHamiltonian (hPlus hMinus : A) :
    opComm (pMinus : Op₂ A) (chiralHamiltonian hPlus hMinus) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [opComm, pMinus, chiralHamiltonian]

def symmetricHamiltonian (h₀ h₁ : A) : Op₂ A := !![h₀, h₁; h₁, h₀]
def walshSym : Op₂ A := 1 + sigma
def walshAnti : Op₂ A := 1 - sigma

theorem sigma_commutes_symmetricHamiltonian (h₀ h₁ : A) :
    (sigma : Op₂ A) * symmetricHamiltonian h₀ h₁ =
      symmetricHamiltonian h₀ h₁ * sigma := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma, symmetricHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

theorem walshSym_mul_walshAnti : (walshSym : Op₂ A) * walshAnti = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [walshSym, walshAnti, sigma, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem walshAnti_mul_walshSym : (walshAnti : Op₂ A) * walshSym = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [walshSym, walshAnti, sigma, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem walshSym_fusion : (walshSym : Op₂ A) * walshSym = walshSym + walshSym := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [walshSym, sigma, Matrix.mul_apply, Fin.sum_univ_two]

theorem walshAnti_fusion : (walshAnti : Op₂ A) * walshAnti = walshAnti + walshAnti := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [walshAnti, sigma, Matrix.mul_apply, Fin.sum_univ_two]

theorem walshSym_commutes_symmetricHamiltonian (h₀ h₁ : A) :
    opComm (walshSym : Op₂ A) (symmetricHamiltonian h₀ h₁) = 0 := by
  dsimp [opComm, walshSym]
  rw [add_mul, mul_add, one_mul, mul_one,
    sigma_commutes_symmetricHamiltonian]
  abel

theorem walshAnti_commutes_symmetricHamiltonian (h₀ h₁ : A) :
    opComm (walshAnti : Op₂ A) (symmetricHamiltonian h₀ h₁) = 0 := by
  dsimp [opComm, walshAnti]
  rw [sub_mul, mul_sub, one_mul, mul_one,
    sigma_commutes_symmetricHamiltonian]
  abel

/-! ## D₅. Peirce cut composition and adjoint channel symmetry
The following are algebraic resolution and self-adjointness statements.  No
positive cone is part of `[StarRing A]`, so no positivity claim is made.
-/

theorem peirce_cut_gluing (Z₁ Z₂ : Op₂ A) :
    Z₁ * pPlus * Z₂ + Z₁ * pMinus * Z₂ = Z₁ * Z₂ := by
  have hsum : (pPlus : Op₂ A) + pMinus = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pPlus, pMinus]
  calc
    Z₁ * pPlus * Z₂ + Z₁ * pMinus * Z₂ =
        Z₁ * (pPlus + pMinus) * Z₂ := by noncomm_ring
    _ = Z₁ * Z₂ := by rw [hsum]; simp

def reflectionChannelPlus [StarRing A] (Z : Op₂ A) : Op₂ A := Z * pPlus * Zᴴ
def reflectionChannelMinus [StarRing A] (Z : Op₂ A) : Op₂ A := Z * pMinus * Zᴴ

theorem pPlus_selfAdjoint [StarRing A] : (pPlus : Op₂ A)ᴴ = pPlus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pPlus]

theorem pMinus_selfAdjoint [StarRing A] : (pMinus : Op₂ A)ᴴ = pMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pMinus]

theorem reflectionChannelPlus_selfAdjoint [StarRing A] (Z : Op₂ A) :
    (reflectionChannelPlus Z)ᴴ = reflectionChannelPlus Z := by
  dsimp [reflectionChannelPlus]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    pPlus_selfAdjoint, mul_assoc]

theorem reflectionChannelMinus_selfAdjoint [StarRing A] (Z : Op₂ A) :
    (reflectionChannelMinus Z)ᴴ = reflectionChannelMinus Z := by
  dsimp [reflectionChannelMinus]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    pMinus_selfAdjoint, mul_assoc]

theorem reflectionDouble_peirce_resolution [StarRing A] (Z : Op₂ A) :
    reflectionChannelPlus Z + reflectionChannelMinus Z = Z * Zᴴ := by
  simpa [reflectionChannelPlus, reflectionChannelMinus] using peirce_cut_gluing Z Zᴴ

end InfoGeometry.OperatorAlgebra.GeometricIndexAndDefects
