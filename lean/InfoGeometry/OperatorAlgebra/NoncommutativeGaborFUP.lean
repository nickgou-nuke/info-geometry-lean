/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra
import InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce
import InfoGeometry.Core.PeirceCompressionDefect

/-!
# Finite operator identities for localization and Gabor systems

All operators below live in matrix rings over an arbitrary (possibly
noncommutative) star ring. These algebraic identities do not assert analytic
fractal uncertainty estimates or positivity in an ordered operator algebra.
-/
namespace InfoGeometry.OperatorAlgebra.NoncommutativeGaborFUP

open Matrix

abbrev Op (B : Type*) := Matrix (Fin 2) (Fin 2) B

section Localization

variable {B : Type*} [Ring B] [StarRing B]

/-- Separate time and frequency localization on an operator module. -/
def localization (pFrequency unitary pTime : Op B) : Op B :=
  pFrequency * unitary * pTime

/-- The exact complementary-channel identity for self-adjoint projections. -/
theorem localization_pore_conservation
    (q u p : Op B)
    (hu : uᴴ * u = 1) (hp : p * p = p) (hps : pᴴ = p)
    (hq : q * q = q) (hqs : qᴴ = q) :
    (localization q u p)ᴴ * localization q u p +
      (localization (1 - q) u p)ᴴ * localization (1 - q) u p = p := by
  dsimp [localization]
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hps, hqs]
  have hsplit : q * q + (1 - q) * (1 - q) = 1 := by
    have hc : (1 - q) * (1 - q) = 1 - q := by noncomm_ring [hq]
    rw [hq, hc]
    noncomm_ring
  calc
    _ = p * (uᴴ * (q * q + (1 - q) * (1 - q)) * u) * p := by
      noncomm_ring
    _ = p * (uᴴ * 1 * u) * p := by rw [hsplit]
    _ = p := by
      calc
        p * (uᴴ * 1 * u) * p = p * (uᴴ * u) * p := by noncomm_ring
        _ = p * 1 * p := by rw [hu]
        _ = p := by noncomm_ring [hp]

/-- Star-square form of the compression defect for self-adjoint projections. -/
theorem compression_variance_star_matrix
    (p q : Op B) (hp : p * p = p) (hps : pᴴ = p) (hqs : qᴴ = q) :
    p * (q * q) * p - (p * q * p) * (p * q * p) =
      ((1 - p) * q * p)ᴴ * ((1 - p) * q * p) := by
  rw [InfoGeometry.Core.PeirceCompressionDefect.compression_square_defect p q hp]
  have hcomp : ((1 - p) * q * p)ᴴ * ((1 - p) * q * p) =
      p * q * (1 - p) * (1 - p) * q * p := by
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hps, hqs]
    noncomm_ring
  rw [hcomp]
  noncomm_ring

end Localization

section IsometricTransform

variable {B : Type*} [Ring B] [StarRing B]

def fockProjection (v : Op B) : Op B := v * vᴴ
def localizationSymbol (v s : Op B) : Op B := vᴴ * s * v
def toeplitzSymbol (v s : Op B) : Op B := fockProjection v * s * fockProjection v

theorem fockProjection_idempotent (v : Op B) (hv : vᴴ * v = 1) :
    fockProjection v * fockProjection v = fockProjection v := by
  dsimp [fockProjection]
  calc
    (v * vᴴ) * (v * vᴴ) = v * (vᴴ * v) * vᴴ := by noncomm_ring
    _ = v * 1 * vᴴ := by rw [hv]
    _ = v * vᴴ := by noncomm_ring

theorem fockProjection_selfAdjoint (v : Op B) :
    (fockProjection v)ᴴ = fockProjection v := by
  simp [fockProjection]

theorem localization_toeplitz_intertwining (v s : Op B) (hv : vᴴ * v = 1) :
    v * localizationSymbol v s = toeplitzSymbol v s * v ∧
    v * localizationSymbol v s * vᴴ = toeplitzSymbol v s ∧
    vᴴ * toeplitzSymbol v s * v = localizationSymbol v s := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [localizationSymbol, toeplitzSymbol, fockProjection]
    calc
      v * (vᴴ * s * v) = v * vᴴ * s * v := by noncomm_ring
      _ = (v * vᴴ) * s * (v * vᴴ) * v := by noncomm_ring [hv]
  · dsimp [localizationSymbol, toeplitzSymbol, fockProjection]
    noncomm_ring
  · dsimp [localizationSymbol, toeplitzSymbol, fockProjection]
    calc
      vᴴ * ((v * vᴴ) * s * (v * vᴴ)) * v =
          (vᴴ * v) * vᴴ * s * v * (vᴴ * v) := by noncomm_ring
      _ = (1 : Op B) * vᴴ * s * v * 1 := by rw [hv]
      _ = vᴴ * s * v := by noncomm_ring

theorem localization_symbol_complement (v s : Op B) (hv : vᴴ * v = 1) :
    localizationSymbol v s + localizationSymbol v (1 - s) = 1 := by
  dsimp [localizationSymbol]
  calc
    vᴴ * s * v + vᴴ * (1 - s) * v = vᴴ * v := by noncomm_ring
    _ = 1 := hv

end IsometricTransform

section MatrixGaborSpecialization

variable {B : Type*} [Ring B] [StarRing B] {m : ℕ}

open InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce

/-- The grading matrix is self-adjoint over any star ring. -/
theorem gamma_selfAdjoint : (gamma : Op B)ᴴ = gamma := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma]

/-- The exchange matrix is self-adjoint over any star ring. -/
theorem sigma_selfAdjoint : (sigma : Op B)ᴴ = sigma := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma]

/-- The symplectic matrix is skew-adjoint, reusing the existing Peirce owner. -/
theorem omega_skewAdjoint : (omega : Op B)ᴴ = -omega :=
  InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce.omega_skew_adjoint

theorem pPlus_selfAdjoint : (pPlus : Op B)ᴴ = pPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pPlus]

/-- The existing finite frame construction specialized to matrix-valued atoms. -/
abbrev matrixFrameOperator (φ : Fin m → Op B) : Op B :=
  KnutsenGaborOperatorAlgebra.gaborFrameOperator φ

/-- The existing finite multiplier construction specialized to matrix-valued atoms. -/
abbrev matrixGaborMultiplier (φ b : Fin m → Op B) : Op B :=
  KnutsenGaborOperatorAlgebra.gaborMultiplier φ b

/-- The Gram matrix of matrix-valued atoms, with entries in the same operator ring. -/
abbrev matrixGaborGram (φ : Fin m → Op B) :
    Matrix (Fin m) (Fin m) (Op B) :=
  KnutsenGaborOperatorAlgebra.gaborGram φ

theorem matrixGaborMultiplier_adjoint (φ b : Fin m → Op B) :
    star (matrixGaborMultiplier φ b) =
      matrixGaborMultiplier φ (fun i => star (b i)) :=
  KnutsenGaborOperatorAlgebra.gaborMultiplier_adjoint φ b

theorem matrixGaborGram_sq_apply (φ : Fin m → Op B) (i j : Fin m) :
    (matrixGaborGram φ * matrixGaborGram φ) i j =
      star (φ i) * matrixFrameOperator φ * φ j :=
  KnutsenGaborOperatorAlgebra.gaborGram_sq_apply φ i j

theorem matrixGaborGram_idempotent_of_parseval (φ : Fin m → Op B)
    (hframe : matrixFrameOperator φ = 1) :
    matrixGaborGram φ * matrixGaborGram φ = matrixGaborGram φ :=
  KnutsenGaborOperatorAlgebra.gaborGram_idempotent_of_parseval hframe

/-! ### Four-point Weyl–Heisenberg frame on the full operator matrix space

These identities instantiate the frame construction on `M₂(B)`, using the
existing noncommuting Clifford generators. They retain all four entries of
the input operator. -/

/-- Average an operator over the four Weyl–Heisenberg conjugations generated
by the identity, grading, exchange, and symplectic matrix operators. -/
def fourPointWeylAverage (M : Op B) : Op B :=
  M + gamma * M * gammaᴴ + sigma * M * sigmaᴴ + omega * M * omegaᴴ

/-- The four-point Weyl–Heisenberg average removes both off-diagonal
operator entries and returns twice the embedded sum of the diagonal entries. -/
theorem fourPointWeylAverage_eq_traceFiber (M : Op B) :
    fourPointWeylAverage M =
      2 * fiberEmbed (M 0 0 + M 1 1) := by
  unfold fourPointWeylAverage
  rw [gamma_selfAdjoint, sigma_selfAdjoint, omega_skewAdjoint]
  rw [two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, sigma, omega, fiberEmbed, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] <;>
    abel

/-- Frame operator of the four Clifford translates of a window. -/
def fourPointFrameOperator (w : Op B) : Op B :=
  w * wᴴ + (gamma * w) * (gamma * w)ᴴ +
    (sigma * w) * (sigma * w)ᴴ + (omega * w) * (omega * w)ᴴ

/-- The Peirce window gives a tight four-point frame with bound `2·1` in the
full noncommutative operator matrix ring. -/
theorem peirceWindow_fourPointFrame :
    fourPointFrameOperator (pPlus : Op B) = (1 : Op B) + 1 := by
  unfold fourPointFrameOperator
  simp only [conjTranspose_mul, gamma_selfAdjoint, sigma_selfAdjoint,
    omega_skewAdjoint, pPlus_selfAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, sigma, omega, pPlus]

/-- Restricting the Peirce window to the identity and exchange translates
gives the exact two-channel frame operator `1`. -/
theorem peirceWindow_twoPointFrame :
    (pPlus : Op B) * pPlusᴴ + (sigma * pPlus) * (sigma * pPlus)ᴴ = (1 : Op B) := by
  simp only [conjTranspose_mul, sigma_selfAdjoint, pPlus_selfAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma, pPlus]

/-- The identity translate alone has frame operator equal to the positive
Peirce projection. -/
theorem peirceWindow_singleBranchFrame :
    (pPlus : Op B) * pPlusᴴ = pPlus := by
  rw [pPlus_selfAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pPlus]

end MatrixGaborSpecialization

section MatrixWitness

/-- Matrix multiplication on `Op B` is genuinely noncommutative over every
nontrivial coefficient ring. -/
theorem op_noncommute {B : Type*} [Ring B] [Nontrivial B] :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) B,
      matI * matJ ≠ matJ * matI := by
  refine ⟨(Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : B) : Matrix (Fin 2) (Fin 2) B),
    (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : B) : Matrix (Fin 2) (Fin 2) B), ?_⟩
  intro h
  have h₁ : (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : B) : Matrix (Fin 2) (Fin 2) B) *
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : B) =
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : B) := by
    simp [Matrix.single_mul_single_same]
  have h₂ : (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : B) : Matrix (Fin 2) (Fin 2) B) *
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : B) =
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : B) := by
    simp [Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [Matrix.single_apply] at h00

end MatrixWitness

end InfoGeometry.OperatorAlgebra.NoncommutativeGaborFUP
