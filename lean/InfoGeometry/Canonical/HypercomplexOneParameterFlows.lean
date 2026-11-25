/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Hypercomplex One-Parameter Unit Flows

This module formalizes the exact 1-parameter evolution flow into the unit group $A^\times$:

$$\Phi : (\mathbb{R}, +) \to A^\times$$

realized as a group homomorphism `Multiplicative ℝ →* Units A`.

Because $(\mathbb{R}, +)$ is an additive group, any homomorphism satisfying $\Phi(s+t) = \Phi(s)\Phi(t)$
automatically lands in the invertible elements with $\Phi(-t) = \Phi(t)^{-1}$.

## Key Constructions:

1. **`RealOneParameterFlow (A : Type*) [Monoid A]`**:
   Structure packaging `flowHom : Multiplicative ℝ →* Units A`.

2. **Elliptic Rotation Flow ($J^2 = -1$):**
   - Generator $J$ satisfying $J^2 = -1$.
   - Flow element: $R_J(t) = \cos(t) \cdot 1 + \sin(t) J \in A^\times$.
   - Group law: $R_J(s+t) = R_J(s) R_J(t)$ via trigonometric addition formulas.
   - Inverse: $R_J(t)^{-1} = R_J(-t) = \cos(t) \cdot 1 - \sin(t) J$.

3. **Hyperbolic Boost Flow ($H^2 = 1$):**
   - Generator $H$ satisfying $H^2 = 1$.
   - Flow element: $B_H(t) = \cosh(t) \cdot 1 + \sinh(t) H \in A^\times$.
   - Group law: $B_H(s+t) = B_H(s) B_H(t)$ via hyperbolic addition formulas.
   - Inverse: $B_H(t)^{-1} = B_H(-t) = \cosh(t) \cdot 1 - \sinh(t) H$.

4. **Parabolic Shear Flow ($N^2 = 0$):**
   - Generator $N$ satisfying $N^2 = 0$.
   - Flow element: $U_N(t) = 1 + t N \in A^\times$.
   - Group law: $U_N(s+t) = U_N(s) U_N(t)$ via $(1+sN)(1+tN) = 1 + (s+t)N + stN^2 = 1 + (s+t)N$.
   - Inverse: $U_N(t)^{-1} = U_N(-t) = 1 - t N$.

5. **Mode classification on eigenmodes:** for each square-law generator above,
   every eigenvector has an eigenvalue forced by the square law:

   - $H^2 = 1 \Rightarrow \mu \in \{+1,-1\}$: the hyperbolic flow acts by
     $e^{t}$ (growth) and $e^{-t}$ (decay) on the two real modes;
   - $J^2 = -1 \Rightarrow \mu \in \{+i,-i\}$: the elliptic flow acts by
     $e^{\pm it}$, a rotation with unit modulus;
   - $N^2 = 0 \Rightarrow \mu = 0$: the parabolic flow is the identity on the
     kernel and affine-linear $w + t v$ along a Jordan chain $Nw = v$.

This is the honest scope available with the pinned mathlib: there is a spectral
theorem for symmetric operators and a semisimplicity API, but no general real
Jordan form and no `NormedSpace.exp` eigenvector-action lemma.  The theorems
below therefore classify the three realized square-law carriers, not an
arbitrary diagonalizable generator.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.HypercomplexOneParameterFlows

open Matrix
open scoped ComplexConjugate
open Multiplicative

/-! ## 1. Categorical Structure for Real One-Parameter Flows -/

/-- An exact 1-parameter continuous/algebraic group flow into the unit group $A^\times$. -/
structure RealOneParameterFlow (A : Type*) [Monoid A] where
  /-- Group homomorphism from $(\mathbb{R}, +)$ to $A^\times$. -/
  flowHom : Multiplicative ℝ →* Units A

/-- Evaluates the flow homomorphism at time $t \in \mathbb{R}$ returning a unit in $A^\times$. -/
def RealOneParameterFlow.evalUnit {A : Type*} [Monoid A]
    (F : RealOneParameterFlow A) (t : ℝ) : Units A :=
  F.flowHom (ofAdd t)

/-- Evaluates the flow homomorphism at time $t \in \mathbb{R}$ coerced into the algebra $A$. -/
def RealOneParameterFlow.eval {A : Type*} [Monoid A]
    (F : RealOneParameterFlow A) (t : ℝ) : A :=
  (F.evalUnit t : A)

@[simp]
theorem RealOneParameterFlow.eval_zero {A : Type*} [Monoid A]
    (F : RealOneParameterFlow A) :
    F.eval 0 = 1 := by
  dsimp [RealOneParameterFlow.eval, RealOneParameterFlow.evalUnit]
  rw [map_one]
  rfl

theorem RealOneParameterFlow.eval_add {A : Type*} [Monoid A]
    (F : RealOneParameterFlow A) (s t : ℝ) :
    F.eval (s + t) = F.eval s * F.eval t := by
  dsimp [RealOneParameterFlow.eval, RealOneParameterFlow.evalUnit]
  rw [map_mul, Units.val_mul]

/-! ## 2. Parabolic Flow ($N^2 = 0$) -/

/-- Parabolic matrix element $1 + t N$. -/
def parabolicMat (N : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + (t : ℂ) • N

theorem parabolicMat_zero (N : Matrix (Fin 2) (Fin 2) ℂ) :
    parabolicMat N 0 = 1 := by
  simp [parabolicMat]

theorem parabolicMat_mul (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) (s t : ℝ) :
    parabolicMat N s * parabolicMat N t = parabolicMat N (s + t) := by
  ext i j
  simp only [parabolicMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply, smul_eq_mul]
  have hNij : ∀ a b, (N * N) a b = (0 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hN]; intros; rfl
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := hNij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : N 0 0 * N 0 1 + N 0 1 * N 1 1 = 0 := by
    have := hNij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : N 1 0 * N 0 0 + N 1 1 * N 1 0 = 0 := by
    have := hNij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
    have := hNij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [Fin.isValue]
    calc (1 + ↑s * N 0 0) * (1 + ↑t * N 0 0) + (0 + ↑s * N 0 1) * (0 + ↑t * N 1 0)
      _ = 1 + ↑s * N 0 0 + ↑t * N 0 0 + ↑s * ↑t * (N 0 0 * N 0 0 + N 0 1 * N 1 0) := by ring
      _ = 1 + ↑s * N 0 0 + ↑t * N 0 0 + ↑s * ↑t * 0 := by rw [h00]
      _ = 1 + ↑(s + t) * N 0 0 := by push_cast; ring
  · simp only [Fin.isValue]
    calc (1 + ↑s * N 0 0) * (0 + ↑t * N 0 1) + (0 + ↑s * N 0 1) * (1 + ↑t * N 1 1)
      _ = ↑s * N 0 1 + ↑t * N 0 1 + ↑s * ↑t * (N 0 0 * N 0 1 + N 0 1 * N 1 1) := by ring
      _ = ↑s * N 0 1 + ↑t * N 0 1 + ↑s * ↑t * 0 := by rw [h01]
      _ = 0 + ↑(s + t) * N 0 1 := by push_cast; ring
  · simp only [Fin.isValue]
    calc (0 + ↑s * N 1 0) * (1 + ↑t * N 0 0) + (1 + ↑s * N 1 1) * (0 + ↑t * N 1 0)
      _ = ↑s * N 1 0 + ↑t * N 1 0 + ↑s * ↑t * (N 1 0 * N 0 0 + N 1 1 * N 1 0) := by ring
      _ = ↑s * N 1 0 + ↑t * N 1 0 + ↑s * ↑t * 0 := by rw [h10]
      _ = 0 + ↑(s + t) * N 1 0 := by push_cast; ring
  · simp only [Fin.isValue]
    calc (0 + ↑s * N 1 0) * (0 + ↑t * N 0 1) + (1 + ↑s * N 1 1) * (1 + ↑t * N 1 1)
      _ = 1 + ↑s * N 1 1 + ↑t * N 1 1 + ↑s * ↑t * (N 1 0 * N 0 1 + N 1 1 * N 1 1) := by ring
      _ = 1 + ↑s * N 1 1 + ↑t * N 1 1 + ↑s * ↑t * 0 := by rw [h11]
      _ = 1 + ↑(s + t) * N 1 1 := by push_cast; ring

/-- Unit carrier for parabolic element $1 + t N$ when $N^2 = 0$. -/
def parabolicUnit (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) (t : ℝ) :
    Units (Matrix (Fin 2) (Fin 2) ℂ) where
  val := parabolicMat N t
  inv := parabolicMat N (-t)
  val_inv := by
    have h := parabolicMat_mul N hN t (-t)
    rw [add_neg_cancel, parabolicMat_zero] at h
    exact h
  inv_val := by
    have h := parabolicMat_mul N hN (-t) t
    rw [neg_add_cancel, parabolicMat_zero] at h
    exact h

/-- Parabolic group homomorphism into units. -/
def parabolicHom (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) :
    Multiplicative ℝ →* Units (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun t := parabolicUnit N hN (toAdd t)
  map_one' := by
    apply Units.ext
    simp [parabolicUnit, parabolicMat]
  map_mul' s t := by
    apply Units.ext
    simp only [Units.val_mul, parabolicUnit]
    have h := parabolicMat_mul N hN (toAdd s) (toAdd t)
    exact h.symm

/-- 🏆 THEOREM: Canonical parabolic 1-parameter flow into units. -/
def parabolicFlow_of_sq_eq_zero (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) :
    RealOneParameterFlow (Matrix (Fin 2) (Fin 2) ℂ) where
  flowHom := parabolicHom N hN

/-! ## 3. Hyperbolic Flow ($H^2 = 1$) -/

/-- Hyperbolic boost matrix element $\cosh(t) \cdot 1 + \sinh(t) H$. -/
def hyperbolicMat (H : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cosh t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Real.sinh t : ℂ) • H

theorem hyperbolicMat_zero (H : Matrix (Fin 2) (Fin 2) ℂ) :
    hyperbolicMat H 0 = 1 := by
  simp [hyperbolicMat, Real.cosh_zero, Real.sinh_zero]

theorem hyperbolicMat_mul (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) (s t : ℝ) :
    hyperbolicMat H s * hyperbolicMat H t = hyperbolicMat H (s + t) := by
  have hcosh : Real.cosh (s + t) = Real.cosh s * Real.cosh t + Real.sinh s * Real.sinh t :=
    Real.cosh_add s t
  have hsinh : Real.sinh (s + t) = Real.sinh s * Real.cosh t + Real.cosh s * Real.sinh t :=
    Real.sinh_add s t
  ext i j
  simp only [hyperbolicMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    smul_eq_mul]
  have hHij : ∀ a b, (H * H) a b = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hH]; intros; rfl
  have h00 : H 0 0 * H 0 0 + H 0 1 * H 1 0 = 1 := by
    have := hHij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : H 0 0 * H 0 1 + H 0 1 * H 1 1 = 0 := by
    have := hHij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : H 1 0 * H 0 0 + H 1 1 * H 1 0 = 0 := by
    have := hHij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : H 1 0 * H 0 1 + H 1 1 * H 1 1 = 1 := by
    have := hHij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcosh, hsinh]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    calc (↑(Real.cosh s) * 1 + ↑(Real.sinh s) * H 0 0) * (↑(Real.cosh t) * 1 + ↑(Real.sinh t) * H 0 0) +
          (↑(Real.cosh s) * 0 + ↑(Real.sinh s) * H 0 1) * (↑(Real.cosh t) * 0 + ↑(Real.sinh t) * H 1 0)
      _ = ↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t) * (H 0 0 * H 0 0 + H 0 1 * H 1 0) +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 0 0 := by ring
      _ = ↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t) * 1 +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 0 0 := by rw [h00]
      _ = (↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t)) * 1 +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 0 0 := by ring
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcosh, hsinh]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    calc (↑(Real.cosh s) * 1 + ↑(Real.sinh s) * H 0 0) * (↑(Real.cosh t) * 0 + ↑(Real.sinh t) * H 0 1) +
          (↑(Real.cosh s) * 0 + ↑(Real.sinh s) * H 0 1) * (↑(Real.cosh t) * 1 + ↑(Real.sinh t) * H 1 1)
      _ = (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 0 1 +
          ↑(Real.sinh s) * ↑(Real.sinh t) * (H 0 0 * H 0 1 + H 0 1 * H 1 1) := by ring
      _ = (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 0 1 +
          ↑(Real.sinh s) * ↑(Real.sinh t) * 0 := by rw [h01]
      _ = (↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t)) * 0 +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 0 1 := by ring
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcosh, hsinh]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    calc (↑(Real.cosh s) * 0 + ↑(Real.sinh s) * H 1 0) * (↑(Real.cosh t) * 1 + ↑(Real.sinh t) * H 0 0) +
          (↑(Real.cosh s) * 1 + ↑(Real.sinh s) * H 1 1) * (↑(Real.cosh t) * 0 + ↑(Real.sinh t) * H 1 0)
      _ = (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 1 0 +
          ↑(Real.sinh s) * ↑(Real.sinh t) * (H 1 0 * H 0 0 + H 1 1 * H 1 0) := by ring
      _ = (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 1 0 +
          ↑(Real.sinh s) * ↑(Real.sinh t) * 0 := by rw [h10]
      _ = (↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t)) * 0 +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 1 0 := by ring
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcosh, hsinh]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    calc (↑(Real.cosh s) * 0 + ↑(Real.sinh s) * H 1 0) * (↑(Real.cosh t) * 0 + ↑(Real.sinh t) * H 0 1) +
          (↑(Real.cosh s) * 1 + ↑(Real.sinh s) * H 1 1) * (↑(Real.cosh t) * 1 + ↑(Real.sinh t) * H 1 1)
      _ = ↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t) * (H 1 0 * H 0 1 + H 1 1 * H 1 1) +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 1 1 := by ring
      _ = ↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t) * 1 +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 1 1 := by rw [h11]
      _ = (↑(Real.cosh s) * ↑(Real.cosh t) + ↑(Real.sinh s) * ↑(Real.sinh t)) * 1 +
          (↑(Real.sinh s) * ↑(Real.cosh t) + ↑(Real.cosh s) * ↑(Real.sinh t)) * H 1 1 := by ring

/-- Unit carrier for hyperbolic boost element. -/
def hyperbolicUnit (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) (t : ℝ) :
    Units (Matrix (Fin 2) (Fin 2) ℂ) where
  val := hyperbolicMat H t
  inv := hyperbolicMat H (-t)
  val_inv := by
    have h := hyperbolicMat_mul H hH t (-t)
    rw [add_neg_cancel, hyperbolicMat_zero] at h
    exact h
  inv_val := by
    have h := hyperbolicMat_mul H hH (-t) t
    rw [neg_add_cancel, hyperbolicMat_zero] at h
    exact h

/-- Hyperbolic group homomorphism into units. -/
def hyperbolicHom (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    Multiplicative ℝ →* Units (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun t := hyperbolicUnit H hH (toAdd t)
  map_one' := by
    apply Units.ext
    simp [hyperbolicUnit, hyperbolicMat, Real.cosh_zero, Real.sinh_zero]
  map_mul' s t := by
    apply Units.ext
    simp only [Units.val_mul, hyperbolicUnit]
    have h := hyperbolicMat_mul H hH (toAdd s) (toAdd t)
    exact h.symm

/-- 🏆 THEOREM: Canonical hyperbolic 1-parameter boost flow into units. -/
def hyperbolicFlow_of_sq_eq_one (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) :
    RealOneParameterFlow (Matrix (Fin 2) (Fin 2) ℂ) where
  flowHom := hyperbolicHom H hH

/-! ## 4. Elliptic Flow ($J^2 = -1$) -/

/-- Elliptic rotation matrix element $\cos(t) \cdot 1 + \sin(t) J$. -/
def ellipticMat (J : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Real.sin t : ℂ) • J

theorem ellipticMat_zero (J : Matrix (Fin 2) (Fin 2) ℂ) :
    ellipticMat J 0 = 1 := by
  simp [ellipticMat, Real.cos_zero, Real.sin_zero]

theorem ellipticMat_mul (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1) (s t : ℝ) :
    ellipticMat J s * ellipticMat J t = ellipticMat J (s + t) := by
  have hcos : Real.cos (s + t) = Real.cos s * Real.cos t - Real.sin s * Real.sin t :=
    Real.cos_add s t
  have hsin : Real.sin (s + t) = Real.sin s * Real.cos t + Real.cos s * Real.sin t :=
    Real.sin_add s t
  ext i j
  simp only [ellipticMat, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    smul_eq_mul]
  have hJij : ∀ a b, (J * J) a b = (-1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hJ]; intros; rfl
  have h00 : J 0 0 * J 0 0 + J 0 1 * J 1 0 = -1 := by
    have := hJij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : J 0 0 * J 0 1 + J 0 1 * J 1 1 = 0 := by
    have := hJij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : J 1 0 * J 0 0 + J 1 1 * J 1 0 = 0 := by
    have := hJij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : J 1 0 * J 0 1 + J 1 1 * J 1 1 = -1 := by
    have := hJij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcos, hsin]
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    calc (↑(Real.cos s) * 1 + ↑(Real.sin s) * J 0 0) * (↑(Real.cos t) * 1 + ↑(Real.sin t) * J 0 0) +
          (↑(Real.cos s) * 0 + ↑(Real.sin s) * J 0 1) * (↑(Real.cos t) * 0 + ↑(Real.sin t) * J 1 0)
      _ = ↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t) * (-(J 0 0 * J 0 0 + J 0 1 * J 1 0)) +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 0 0 := by ring
      _ = ↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t) * (-(-1)) +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 0 0 := by rw [h00]
      _ = (↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t)) * 1 +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 0 0 := by ring
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcos, hsin]
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    calc (↑(Real.cos s) * 1 + ↑(Real.sin s) * J 0 0) * (↑(Real.cos t) * 0 + ↑(Real.sin t) * J 0 1) +
          (↑(Real.cos s) * 0 + ↑(Real.sin s) * J 0 1) * (↑(Real.cos t) * 1 + ↑(Real.sin t) * J 1 1)
      _ = (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 0 1 +
          ↑(Real.sin s) * ↑(Real.sin t) * (J 0 0 * J 0 1 + J 0 1 * J 1 1) := by ring
      _ = (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 0 1 +
          ↑(Real.sin s) * ↑(Real.sin t) * 0 := by rw [h01]
      _ = (↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t)) * 0 +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 0 1 := by ring
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcos, hsin]
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    calc (↑(Real.cos s) * 0 + ↑(Real.sin s) * J 1 0) * (↑(Real.cos t) * 1 + ↑(Real.sin t) * J 0 0) +
          (↑(Real.cos s) * 1 + ↑(Real.sin s) * J 1 1) * (↑(Real.cos t) * 0 + ↑(Real.sin t) * J 1 0)
      _ = (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 1 0 +
          ↑(Real.sin s) * ↑(Real.sin t) * (J 1 0 * J 0 0 + J 1 1 * J 1 0) := by ring
      _ = (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 1 0 +
          ↑(Real.sin s) * ↑(Real.sin t) * 0 := by rw [h10]
      _ = (↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t)) * 0 +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 1 0 := by ring
  · simp only [Matrix.one_apply, Fin.isValue]
    rw [hcos, hsin]
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    calc (↑(Real.cos s) * 0 + ↑(Real.sin s) * J 1 0) * (↑(Real.cos t) * 0 + ↑(Real.sin t) * J 0 1) +
          (↑(Real.cos s) * 1 + ↑(Real.sin s) * J 1 1) * (↑(Real.cos t) * 1 + ↑(Real.sin t) * J 1 1)
      _ = ↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t) * (-(J 1 0 * J 0 1 + J 1 1 * J 1 1)) +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 1 1 := by ring
      _ = ↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t) * (-(-1)) +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 1 1 := by rw [h11]
      _ = (↑(Real.cos s) * ↑(Real.cos t) - ↑(Real.sin s) * ↑(Real.sin t)) * 1 +
          (↑(Real.sin s) * ↑(Real.cos t) + ↑(Real.cos s) * ↑(Real.sin t)) * J 1 1 := by ring

/-- Unit carrier for elliptic rotation element. -/
def ellipticUnit (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1) (t : ℝ) :
    Units (Matrix (Fin 2) (Fin 2) ℂ) where
  val := ellipticMat J t
  inv := ellipticMat J (-t)
  val_inv := by
    have h := ellipticMat_mul J hJ t (-t)
    rw [add_neg_cancel, ellipticMat_zero] at h
    exact h
  inv_val := by
    have h := ellipticMat_mul J hJ (-t) t
    rw [neg_add_cancel, ellipticMat_zero] at h
    exact h

/-- Elliptic group homomorphism into units. -/
def ellipticHom (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1) :
    Multiplicative ℝ →* Units (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun t := ellipticUnit J hJ (toAdd t)
  map_one' := by
    apply Units.ext
    simp [ellipticUnit, ellipticMat, Real.cos_zero, Real.sin_zero]
  map_mul' s t := by
    apply Units.ext
    simp only [Units.val_mul, ellipticUnit]
    have h := ellipticMat_mul J hJ (toAdd s) (toAdd t)
    exact h.symm

/-- 🏆 THEOREM: Canonical elliptic 1-parameter rotation flow into units. -/
def ellipticFlow_of_sq_eq_neg_one (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1) :
    RealOneParameterFlow (Matrix (Fin 2) (Fin 2) ℂ) where
  flowHom := ellipticHom J hJ

/-! ## 5. Square-law eigenmode classification

The three flows above are generated by matrices with $H^2 = 1$, $J^2 = -1$,
$N^2 = 0$.  Their eigenvalues are forced by these square laws, and the flows
act on each eigenmode by the scalar dictated by that eigenvalue: exponential
growth/decay for the real modes, a unit-modulus complex rotation for the
complex modes, and an affine-linear shear along a nontrivial Jordan chain.
-/

private abbrev PositionalEnd2 := Module.End ℂ (Fin 2 → ℂ)

private lemma mulVecLin_sq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (A.mulVecLin : PositionalEnd2) ^ 2 = (A * A).mulVecLin := by
  ext v i
  simp [pow_two]

/-- A square-law generator has eigenvalues whose square is the law's scalar.
For `H * H = 1` this gives `μ² = 1`; for `J * J = -1` it gives `μ² = -1`;
for `N * N = 0` it gives `μ² = 0`. -/
theorem eigenvalue_sq_of_sq_eq_smul (A : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (hA : A * A = c • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (A.mulVecLin : PositionalEnd2) μ) :
    μ ^ 2 = c := by
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  have hpow := hv.pow_apply 2
  have hsq : (A.mulVecLin : PositionalEnd2) ^ 2 =
      c • (LinearMap.id : PositionalEnd2) := by
    rw [mulVecLin_sq, hA]
    ext w i
    simp
  rw [hsq] at hpow
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hpow
  have hvne : v ≠ 0 := hv.2
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hvne
    funext j
    exact h j
  have hcoord := congrFun hpow i
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  exact mul_right_cancel₀ hi hcoord.symm

/-- A hyperbolic generator (`H² = 1`) has only real eigenvalues `+1` and `-1`.
These are the growth and decay modes. -/
theorem hyperbolic_eigenvalue_eq_one_or_neg_one
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (H.mulVecLin : PositionalEnd2) μ) :
    μ = 1 ∨ μ = -1 := by
  have hc : H * H = (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simpa using hH
  have hsq := eigenvalue_sq_of_sq_eq_smul H 1 hc hμ
  exact sq_eq_one_iff.mp (by simpa using hsq)

/-- A parabolic generator (`N² = 0`) has only the zero eigenvalue. -/
theorem parabolic_eigenvalue_eq_zero
    (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (N.mulVecLin : PositionalEnd2) μ) :
    μ = 0 := by
  have hc : N * N = (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simpa using hN
  have hsq := eigenvalue_sq_of_sq_eq_smul N 0 hc hμ
  exact sq_eq_zero_iff.mp hsq

/-- An elliptic generator (`J² = -1`) has only the complex conjugate pair
`+i`, `-i`.  These are the rotation modes. -/
theorem elliptic_eigenvalue_eq_I_or_neg_I
    (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (J.mulVecLin : PositionalEnd2) μ) :
    μ = Complex.I ∨ μ = -Complex.I := by
  have hc : J * J = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simpa using hJ
  have hsq := eigenvalue_sq_of_sq_eq_smul J (-1) hc hμ
  have hfac : (μ - Complex.I) * (μ + Complex.I) = 0 := by
    calc
      (μ - Complex.I) * (μ + Complex.I) = μ ^ 2 + 1 := by
        rw [sub_mul, mul_add, mul_add, Complex.I_mul_I]
        ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    exact eq_neg_of_add_eq_zero_left h

/-- The hyperbolic flow acts diagonally on an eigenvector of `H`, with scalar
`cosh t + μ sinh t`. -/
theorem hyperbolicMat_mulVec_eigen (H : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (μ : ℂ) (hv : H *ᵥ v = μ • v) (t : ℝ) :
    hyperbolicMat H t *ᵥ v = ((Real.cosh t : ℂ) + μ * (Real.sinh t : ℂ)) • v := by
  rw [hyperbolicMat, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hv, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Growth mode: the `+1` eigenvector of a hyperbolic generator is scaled by
`exp t` at time `t`. -/
theorem hyperbolicMat_growth (H : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (hv : H *ᵥ v = v) (t : ℝ) :
    hyperbolicMat H t *ᵥ v = (Real.exp t : ℂ) • v := by
  rw [hyperbolicMat_mulVec_eigen H v 1 (by simpa using hv) t]
  norm_num

/-- Decay mode: the `-1` eigenvector of a hyperbolic generator is scaled by
`exp (-t)` at time `t`. -/
theorem hyperbolicMat_decay (H : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (hv : H *ᵥ v = -v) (t : ℝ) :
    hyperbolicMat H t *ᵥ v = (Real.exp (-t) : ℂ) • v := by
  rw [hyperbolicMat_mulVec_eigen H v (-1) (by simpa using hv) t]
  norm_num
  congr 1
  have h : Real.cosh t - Real.sinh t = Real.exp (-t) := by
    calc
      Real.cosh t - Real.sinh t = Real.cosh (-t) + Real.sinh (-t) := by
        rw [Real.cosh_neg, Real.sinh_neg]
        ring
      _ = Real.exp (-t) := Real.cosh_add_sinh (-t)
  exact_mod_cast h

/-- The elliptic flow acts diagonally on an eigenvector of `J`, with scalar
`cos t + μ sin t`. -/
theorem ellipticMat_mulVec_eigen (J : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (μ : ℂ) (hv : J *ᵥ v = μ • v) (t : ℝ) :
    ellipticMat J t *ᵥ v = ((Real.cos t : ℂ) + μ * (Real.sin t : ℂ)) • v := by
  rw [ellipticMat, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hv, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Counter-rotating complex mode: the `+i` eigenvector is scaled by `exp(i t)`. -/
theorem ellipticMat_rotation_pos (J : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (hv : J *ᵥ v = Complex.I • v) (t : ℝ) :
    ellipticMat J t *ᵥ v = (Complex.exp ((t : ℂ) * Complex.I)) • v := by
  rw [ellipticMat_mulVec_eigen J v Complex.I hv t]
  congr 1
  rw [Complex.exp_ofReal_mul_I]
  ring_nf

/-- Co-rotating complex mode: the `-i` eigenvector is scaled by `exp(-i t)`. -/
theorem ellipticMat_rotation_neg (J : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (hv : J *ᵥ v = (-Complex.I) • v) (t : ℝ) :
    ellipticMat J t *ᵥ v = (Complex.exp (-(t : ℂ) * Complex.I)) • v := by
  rw [ellipticMat_mulVec_eigen J v (-Complex.I) hv t]
  congr 1
  rw [show -(t : ℂ) * Complex.I = ((-t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring_nf]
  rw [Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring_nf

/-- The complex rotation scalar is unitary: it preserves norm at all times. -/
theorem ellipticMat_rotation_norm (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

/-- Zero mode: the parabolic flow fixes the kernel of `N` pointwise. -/
theorem parabolicMat_mulVec_zero (N : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℂ) (hv : N *ᵥ v = 0) (t : ℝ) :
    parabolicMat N t *ᵥ v = v := by
  rw [parabolicMat, add_mulVec, smul_mulVec, one_mulVec, hv]
  simp

/-- Jordan mode: along a chain `N w = v`, `N v = 0` the parabolic flow is the
affine-linear (polynomial in `t`) shear `w ↦ w + t • v`, and the shear image
remains in the same affine chain. -/
theorem parabolicMat_mulVec_jordan (N : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℂ) (hv : N *ᵥ w = v) (hw : N *ᵥ v = 0) (t : ℝ) :
    parabolicMat N t *ᵥ w = w + (t : ℂ) • v ∧
      N *ᵥ (parabolicMat N t *ᵥ w) = v := by
  constructor
  · rw [parabolicMat, add_mulVec, smul_mulVec, one_mulVec, hv]
  · rw [parabolicMat, add_mulVec, smul_mulVec, one_mulVec, hv]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hw]
    simp [hv]

end InfoGeometry.Canonical.HypercomplexOneParameterFlows
