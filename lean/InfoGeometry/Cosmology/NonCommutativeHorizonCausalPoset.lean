/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Basic

/-!
# The Causal Poset of Non-Commutative Horizons

This module formalizes the causal synthesis of non-commutative horizons across
Algebraic Quantum Field Theory (AQFT), Tomita–Takesaki modular theory, Krein spaces,
and Bogoliubov–Rindler flows. The archetypes are ordered into a strict causal poset:

## Causal Poset Archetypes
1. `Archetype_I_StateFunctional`: Evaluation of the fundamental state $\phi(x)$.
2. `Archetype_II_GNS_Radical`: The null space forming a strict Left Ideal (Ket space).
3. `Archetype_III_Tracial_Modular`: Right Ideal completion iff the state is tracial (Tomita–Takesaki origin).
4. `Archetype_IV_Krein_Metric`: Indefinite $(1, -1)$ geometry of the doubled Nambu–Gor'kov space.
5. `Archetype_V_Bogoliubov_Rindler`: Invariant hyperbolic flow preserving the Krein null cone.
-/

-- ==============================================================================
-- Archetype I & II : State Functional and the GNS Radical Left Ideal
-- ==============================================================================
namespace Archetype_II_GNS_Radical

variable {R : Type*} [CommRing R] [StarRing R]
variable {A : Type*} [Ring A] [StarRing A] [Algebra R A] [StarModule R A]
variable (φ : A →ₗ[R] R)

/-- The Gelfand-Naimark-Segal (GNS) null radical.
    Mathematically represents the zero-norm ghosts `N_φ = { x | ∀ y, φ(y* x) = 0 }`. -/
def gnsRadical : Submodule R A where
  carrier := { x | ∀ y, φ (star y * x) = 0 }
  add_mem' hx hy y := by
    simp only [mul_add, LinearMap.map_add, hx y, hy y, add_zero]
  zero_mem' y := by
    simp only [mul_zero, LinearMap.map_zero]
  smul_mem' c x hx y := by
    rw [mul_smul_comm]
    rw [LinearMap.map_smul]
    rw [hx y]
    exact smul_zero c

/-- The GNS Radical forms a strict Left Ideal.
    This proves that the quotient naturally forms a module of Kets `|ψ⟩`. -/
theorem gnsRadical_is_left_ideal (a : A) (x : A) (hx : x ∈ gnsRadical φ) :
    a * x ∈ gnsRadical φ := by
  intro y
  have h_assoc : star y * (a * x) = star (star a * y) * x := by
    simp only [star_mul, star_star, mul_assoc]
  rw [h_assoc]
  exact hx (star a * y)

end Archetype_II_GNS_Radical

-- ==============================================================================
-- Archetype III : Traciality and the Arrow of Time
-- ==============================================================================
namespace Archetype_III_Tracial_Modular

variable {R : Type*} [CommRing R] [StarRing R]
variable {A : Type*} [Ring A] [StarRing A] [Algebra R A] [StarModule R A]
variable (φ : A →ₗ[R] R)

/-- A state functional is tracial if it is invariant under cyclic permutation.
    If the state is non-tracial, Tomita-Takesaki modular time flows non-trivially. -/
def IsTracial : Prop := ∀ u v : A, φ (u * v) = φ (v * u)

/-- Under traciality of the fundamental state, the GNS Radical is also a Right Ideal,
    completing it to a two-sided ideal (forming an Algebra rather than merely a Left Module). -/
theorem gnsRadical_is_right_ideal_of_tracial
    (hTr : IsTracial φ) (a : A) (x : A) (hx : x ∈ Archetype_II_GNS_Radical.gnsRadical φ) :
    x * a ∈ Archetype_II_GNS_Radical.gnsRadical φ := by
  intro y
  have h1 : star y * (x * a) = (star y * x) * a := by rw [mul_assoc]
  rw [h1, hTr, ← mul_assoc]
  have h2 : a * star y = star (y * star a) := by simp only [star_mul, star_star]
  rw [h2]
  exact hx (y * star a)

end Archetype_III_Tracial_Modular

-- ==============================================================================
-- Archetype IV : Krein Space and Indefinite Metric Geometry
-- ==============================================================================
namespace Archetype_IV_Krein_Metric

open Matrix
open scoped Matrix

/-- The fundamental split Krein metric η = diag(1, -1) representing 
    the particle-hole doubling of the Nambu-Gor'kov space. -/
def kreinMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- The Krein/Dirac adjoint operator K^‡ = η Kᵀ η. -/
def kreinAdjoint (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinMetric * Mᵀ * kreinMetric

/-- The indefinite quadratic form defining the Krein null cone. -/
def kreinQuadForm (v : Fin 2 → ℝ) : ℝ :=
  (v 0)^2 - (v 1)^2

/-- A state resides on the causal boundary if its Krein norm vanishes. -/
def IsKreinNull (v : Fin 2 → ℝ) : Prop :=
  kreinQuadForm v = 0

end Archetype_IV_Krein_Metric

-- ==============================================================================
-- Archetype V : Bogoliubov-Rindler Hyperbolic Flow
-- ==============================================================================
namespace Archetype_V_Bogoliubov_Rindler

open Matrix
open scoped Matrix
open Archetype_IV_Krein_Metric

/-- The Bogoliubov transformation (Lorentz boost / Rindler thermal time evolution). -/
noncomputable def bogoliubovTransform (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh θ, Real.sinh θ; Real.sinh θ, Real.cosh θ]

/-- Explicitly compute the Krein adjoint of the Bogoliubov flow. -/
lemma kreinAdjoint_bogoliubovTransform (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) = !![Real.cosh θ, -Real.sinh θ; -Real.sinh θ, Real.cosh θ] := by
  ext i j
  dsimp [kreinAdjoint, kreinMetric, bogoliubovTransform]
  simp only [Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The Bogoliubov flow is an exact isometry of the Krein metric space: B^‡ B = 1. -/
theorem bogoliubov_is_krein_isometry (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) * bogoliubovTransform θ = 1 := by
  rw [kreinAdjoint_bogoliubovTransform]
  ext i j
  dsimp [bogoliubovTransform]
  simp only [Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp
  · have h := Real.cosh_sq_sub_sinh_sq θ
    calc Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ
      _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
      _ = 1 := h
  · ring
  · ring
  · have h := Real.cosh_sq_sub_sinh_sq θ
    calc -(Real.sinh θ * Real.sinh θ) + Real.cosh θ * Real.cosh θ
      _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
      _ = 1 := h

/-- The causal horizon is invariant: The Bogoliubov flow preserves the Krein null cone. -/
theorem bogoliubov_preserves_null_cone (θ : ℝ) (v : Fin 2 → ℝ) (hv : IsKreinNull v) :
    IsKreinNull (bogoliubovTransform θ *ᵥ v) := by
  dsimp [IsKreinNull, kreinQuadForm, bogoliubovTransform, Matrix.mulVec, dotProduct] at *
  simp only [Fin.sum_univ_two, Fin.isValue]
  have hc := Real.cosh_sq_sub_sinh_sq θ
  calc
    (Real.cosh θ * v 0 + Real.sinh θ * v 1) ^ 2 - (Real.sinh θ * v 0 + Real.cosh θ * v 1) ^ 2
      = (Real.cosh θ ^ 2 - Real.sinh θ ^ 2) * (v 0 ^ 2 - v 1 ^ 2) := by ring
    _ = 1 * (v 0 ^ 2 - v 1 ^ 2) := by rw [hc]
    _ = 1 * 0 := by rw [hv]
    _ = 0 := mul_zero 1

end Archetype_V_Bogoliubov_Rindler
