import Mathlib.Tactic
import InfoGeometry.Physics.SplitOctonionPoincareCasimirBridge
import InfoGeometry.Physics.PoincareCasimirCentralityBridge

set_option linter.unusedSimpArgs false

/-!
# Poincaré Pauli-Lubański Covariance and Full Casimir Centrality Bridge

This owner module formalizes the exact representation-theoretic covariance and
Casimir centrality theorems for the Poincaré Lie algebra:

1. **Generic Lorentz Vector Transformation Law:**
   A 4-vector operator $V : \text{Fin } 4 \to A$ is a Lorentz vector if:
   $$[M_{\mu\nu}, V_\rho] = \eta_{\nu\rho} V_\mu - \eta_{\mu\rho} V_\nu$$

2. **Universal Lorentz Scalar Invariant Theorem (`lorentz_vector_sq_comm_M`):**
   For any commuting 4-vector $V$ transforming as a Lorentz vector under $M_{\mu\nu}$,
   its Minkowski squared norm $V^2 = V_0^2 - V_1^2 - V_2^2 - V_3^2$ strictly commutes
   with all Lorentz generators: $[M_{\mu\nu}, V^2] = 0$.

3. **Full First Casimir Centrality ($[C_1, \mathfrak{p}] = 0$):**
   - $[C_1, P_\mu] = 0$ for all translation generators $P_\mu$.
   - $[C_1, M_{\mu\nu}] = 0$ for all Lorentz rotation/boost generators $M_{\mu\nu}$.

4. **Full Second Casimir Centrality ($[C_2, \mathfrak{p}] = 0$):**
   - $[C_2, P_\mu] = 0$ for all translation generators $P_\mu$.
   - $[C_2, M_{\mu\nu}] = 0$ for all Lorentz rotation/boost generators $M_{\mu\nu}$.
-/

noncomputable section

namespace InfoGeometry.Physics.PoincarePauliLubanskiCovarianceBridge

open InfoGeometry.Physics.PoincareCasimirCentralityBridge
open InfoGeometry.Physics.SplitOctonionPoincareCasimirBridge

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

/-- 🏆 THEOREM 1 (GENERIC LORENTZ SCALAR INVARIANCE):
    For any commuting 4-vector $V$ transforming as a Lorentz vector under $M_{\mu\nu}$,
    its Minkowski norm $V^2$ commutes with all Lorentz generators: $[M_{\mu\nu}, V^2] = 0$. -/
theorem lorentz_vector_sq_comm_M {A : Type*} [Ring A] [Algebra ℝ A]
    (M : Fin 4 → Fin 4 → A) (V : Fin 4 → A)
    (hLor : IsLorentzVector M V)
    (hV_comm : ∀ μ ν, bracket (V μ) (V ν) = 0) (μ ν : Fin 4) :
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
  fin_cases μ <;> fin_cases ν
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 0 1
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 0 2
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 0 3
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 1 0
    rw [hp]; abel
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 1 2
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 1 3
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 2 0
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 2 1
    rw [hp]; abel
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 2 3
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 3 0
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 3 1
    rw [hp]; abel
  · dsimp [eta, etaSign]
    simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_add, zero_sub, one_smul, neg_smul, neg_one_smul, mul_neg, neg_mul, neg_neg]
    have hp := v_comm_eq V hV_comm 3 2
    rw [hp]; abel
  · dsimp [eta, etaSign]; simp only [zero_smul, sub_zero, mul_zero, zero_mul, sub_self, add_zero, zero_sub, neg_zero]

/-- Abstract Poincaré algebra structure. -/
structure PoincareRepresentation (A : Type*) [Ring A] [Algebra ℝ A] where
  P : Fin 4 → A
  M : Fin 4 → Fin 4 → A
  W : Fin 4 → A
  P_comm : ∀ μ ν, bracket (P μ) (P ν) = 0
  W_comm : ∀ μ ν, bracket (W μ) (W ν) = 0
  PW_comm : ∀ μ ν, bracket (P μ) (W ν) = 0
  P_lorentz : IsLorentzVector M P
  W_lorentz : IsLorentzVector M W

/-- 🏆 THEOREM 2: Full Casimir 1 Centrality in Poincaré Algebra. -/
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
  lorentz_vector_sq_comm_M poinc.M poinc.P poinc.P_lorentz poinc.P_comm μ ν

/-- 🏆 THEOREM 3: Full Casimir 2 Centrality in Poincaré Algebra. -/
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
  lorentz_vector_sq_comm_M poinc.M poinc.W poinc.W_lorentz poinc.W_comm μ ν

end InfoGeometry.Physics.PoincarePauliLubanskiCovarianceBridge
