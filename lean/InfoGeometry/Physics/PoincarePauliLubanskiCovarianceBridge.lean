/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

set_option linter.unusedSimpArgs false

/-!
# Covariant operator vectors and generator-relative quadratic invariants

The coefficient algebra is an arbitrary associative real algebra. The results
derive quadratic invariance from a supplied Lorentz covariance law, without
assuming that vector components commute. The historical `PoincareRepresentation`
name denotes a conditional interface: its fields do not construct a full Lie
or group representation and do not define `W` from `P` and `M`.

1. **Generic Lorentz Vector Transformation Law:**
   A 4-vector operator $V : \text{Fin } 4 \to A$ is a Lorentz vector if:
   $$[M_{\mu\nu}, V_\rho] = \eta_{\nu\rho} V_\mu - \eta_{\mu\rho} V_\nu$$

2. **Universal Lorentz Scalar Invariant Theorem (`lorentz_vector_sq_comm_M`):**
   For any operator-valued 4-vector $V$ transforming as a Lorentz vector under $M_{\mu\nu}$,
   its Minkowski squared norm $V^2 = V_0^2 - V_1^2 - V_2^2 - V_3^2$ strictly commutes
   with all Lorentz generators: $[M_{\mu\nu}, V^2] = 0$.

3. **First quadratic invariant relative to the supplied generators:**
   - $[C_1, P_\mu] = 0$ for all translation generators $P_\mu$.
   - $[C_1, M_{\mu\nu}] = 0$ for all Lorentz rotation/boost generators $M_{\mu\nu}$.

4. **Second quadratic invariant relative to the supplied generators:**
   - $[C_2, P_\mu] = 0$ for all translation generators $P_\mu$.
   - $[C_2, M_{\mu\nu}] = 0$ for all Lorentz rotation/boost generators $M_{\mu\nu}$.
-/

noncomputable section

namespace InfoGeometry.Physics.PoincarePauliLubanskiCovarianceBridge

/-- Commutator of two elements in an associative ring. -/
def bracket {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

/-- Minkowski metric sign function: +1 for 0, -1 for 1,2,3. -/
def etaSign (μ : Fin 4) : ℝ :=
  match μ with
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1

/-- Minkowski metric tensor $\eta_{\mu\nu}$. -/
def eta (μ ν : Fin 4) : ℝ :=
  if μ = ν then etaSign μ else 0

/-- Minkowski squared norm of a 4-vector: $V^2 = V_0^2 - V_1^2 - V_2^2 - V_3^2$. -/
def minkowskiSq {A : Type*} [Ring A] (V : Fin 4 → A) : A :=
  V 0 ^ 2 - V 1 ^ 2 - V 2 ^ 2 - V 3 ^ 2

/-- A 4-vector $V$ in $A$ is a Lorentz vector if its commutator with $M_{\mu\nu}$
    follows the standard vector transformation law. -/
def IsLorentzVector {A : Type*} [Ring A] [Algebra ℝ A]
    (M : Fin 4 → Fin 4 → A) (V : Fin 4 → A) : Prop :=
  ∀ μ ν ρ, bracket (M μ ν) (V ρ) = (eta ν ρ • V μ) - (eta μ ρ • V ν)

/-- Leibniz rule for commutator with square. -/
theorem bracket_sq {A : Type*} [Ring A] (x y : A) :
    bracket x (y ^ 2) = bracket x y * y + y * bracket x y := by
  dsimp [bracket]
  rw [pow_two]
  noncomm_ring

theorem v_comm_eq {A : Type*} [Ring A] (V : Fin 4 → A)
    (hV : ∀ μ ν, bracket (V μ) (V ν) = 0) (μ ν : Fin 4) :
    V μ * V ν = V ν * V μ := by
  have hp := hV μ ν
  dsimp [bracket] at hp
  calc
    V μ * V ν = (V μ * V ν - V ν * V μ) + V ν * V μ := by abel
    _ = 0 + V ν * V μ := by rw [hp]
    _ = V ν * V μ := by abel

/-- Explicit expansion of bracket of M with V^2. -/
theorem bracket_M_V_sq {A : Type*} [Ring A] [Algebra ℝ A]
    (M : Fin 4 → Fin 4 → A) (V : Fin 4 → A) (hLor : IsLorentzVector M V) (μ ν i : Fin 4) :
    bracket (M μ ν) (V i ^ 2) =
      ((eta ν i • V μ) - (eta μ i • V ν)) * V i +
      V i * ((eta ν i • V μ) - (eta μ i • V ν)) := by
  rw [bracket_sq, hLor μ ν i]

/-- Quadratic invariance from Lorentz covariance alone:
    For any operator-valued 4-vector $V$ transforming as a Lorentz vector under $M_{\mu\nu}$,
    its Minkowski norm $V^2$ commutes with all Lorentz generators: $[M_{\mu\nu}, V^2] = 0$. -/
theorem lorentz_vector_sq_comm_M {A : Type*} [Ring A] [Algebra ℝ A]
    (M : Fin 4 → Fin 4 → A) (V : Fin 4 → A)
    (hLor : IsLorentzVector M V)
    (μ ν : Fin 4) :
    bracket (minkowskiSq V) (M μ ν) = 0 := by
  have h_anti : bracket (minkowskiSq V) (M μ ν) = - bracket (M μ ν) (minkowskiSq V) := by
    dsimp [bracket]; abel
  rw [h_anti]
  have h_cas : bracket (M μ ν) (minkowskiSq V) =
      bracket (M μ ν) (V 0 ^ 2) -
      bracket (M μ ν) (V 1 ^ 2) -
      bracket (M μ ν) (V 2 ^ 2) -
      bracket (M μ ν) (V 3 ^ 2) := by
    dsimp [minkowskiSq, bracket]
    simp only [mul_sub, sub_mul]
    abel
  rw [h_cas]
  simp only [bracket_M_V_sq M V hLor]
  fin_cases μ <;> fin_cases ν <;>
    norm_num [eta, etaSign] <;> noncomm_ring

/-- Conditional covariance and translation-commutation interface.
This does not supply the full Lorentz bracket laws or define `W` from `P` and `M`. -/
structure PoincareRepresentation (A : Type*) [Ring A] [Algebra ℝ A] where
  P : Fin 4 → A
  M : Fin 4 → Fin 4 → A
  W : Fin 4 → A
  P_comm : ∀ μ ν, bracket (P μ) (P ν) = 0
  PW_comm : ∀ μ ν, bracket (P μ) (W ν) = 0
  P_lorentz : IsLorentzVector M P
  W_lorentz : IsLorentzVector M W

/-- The first quadratic invariant commutes with the supplied translations. -/
theorem poincare_casimir1_central_translations {A : Type*} [Ring A] [Algebra ℝ A]
    (poinc : PoincareRepresentation A) (μ : Fin 4) :
    bracket (minkowskiSq poinc.P) (poinc.P μ) = 0 := by
  dsimp [minkowskiSq, bracket]
  have hcomm (i : Fin 4) : (poinc.P i ^ 2) * poinc.P μ = poinc.P μ * (poinc.P i ^ 2) := by
    have hp := poinc.P_comm i μ
    dsimp [bracket] at hp
    have hp' : poinc.P i * poinc.P μ = poinc.P μ * poinc.P i := by
      calc
        poinc.P i * poinc.P μ = poinc.P i * poinc.P μ - poinc.P μ * poinc.P i + poinc.P μ * poinc.P i := by abel
        _ = 0 + poinc.P μ * poinc.P i := by rw [hp]
        _ = poinc.P μ * poinc.P i := by abel
    calc
      (poinc.P i ^ 2) * poinc.P μ = poinc.P i * (poinc.P i * poinc.P μ) := by rw [pow_two, mul_assoc]
      _ = poinc.P i * (poinc.P μ * poinc.P i) := by rw [hp']
      _ = (poinc.P i * poinc.P μ) * poinc.P i := by rw [mul_assoc]
      _ = (poinc.P μ * poinc.P i) * poinc.P i := by rw [hp']
      _ = poinc.P μ * (poinc.P i ^ 2) := by rw [pow_two, mul_assoc]
  simp only [sub_mul, mul_sub, hcomm]
  abel

theorem poincare_casimir1_central_lorentz {A : Type*} [Ring A] [Algebra ℝ A]
    (poinc : PoincareRepresentation A) (μ ν : Fin 4) :
    bracket (minkowskiSq poinc.P) (poinc.M μ ν) = 0 :=
  lorentz_vector_sq_comm_M poinc.M poinc.P poinc.P_lorentz μ ν

/-- The second quadratic invariant commutes with the supplied translations. -/
theorem poincare_casimir2_central_translations {A : Type*} [Ring A] [Algebra ℝ A]
    (poinc : PoincareRepresentation A) (μ : Fin 4) :
    bracket (minkowskiSq poinc.W) (poinc.P μ) = 0 := by
  dsimp [minkowskiSq, bracket]
  have hcomm (i : Fin 4) : (poinc.W i ^ 2) * poinc.P μ = poinc.P μ * (poinc.W i ^ 2) := by
    have hp := poinc.PW_comm μ i
    dsimp [bracket] at hp
    have hp' : poinc.W i * poinc.P μ = poinc.P μ * poinc.W i := by
      calc
        poinc.W i * poinc.P μ = -(poinc.P μ * poinc.W i - poinc.W i * poinc.P μ) + poinc.P μ * poinc.W i := by abel
        _ = -0 + poinc.P μ * poinc.W i := by rw [hp]
        _ = poinc.P μ * poinc.W i := by abel
    calc
      (poinc.W i ^ 2) * poinc.P μ = poinc.W i * (poinc.W i * poinc.P μ) := by rw [pow_two, mul_assoc]
      _ = poinc.W i * (poinc.P μ * poinc.W i) := by rw [hp']
      _ = (poinc.W i * poinc.P μ) * poinc.W i := by rw [mul_assoc]
      _ = (poinc.P μ * poinc.W i) * poinc.W i := by rw [hp']
      _ = poinc.P μ * (poinc.W i ^ 2) := by rw [pow_two, mul_assoc]
  simp only [sub_mul, mul_sub, hcomm]
  abel

theorem poincare_casimir2_central_lorentz {A : Type*} [Ring A] [Algebra ℝ A]
    (poinc : PoincareRepresentation A) (μ ν : Fin 4) :
    bracket (minkowskiSq poinc.W) (poinc.M μ ν) = 0 :=
  lorentz_vector_sq_comm_M poinc.M poinc.W poinc.W_lorentz μ ν

end InfoGeometry.Physics.PoincarePauliLubanskiCovarianceBridge
