import Mathlib

noncomputable section

open ContinuousLinearMap Complex

namespace InfoGeometry.EndToEnd

/-!
=============================================================================
LAYER 1: The Lie Algebra of Spacetime and Modular Flows
=============================================================================
-/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Bundled ℂ-linear derivation on a complex algebra A. -/
structure Derivation (A : Type*) [Ring A] [Algebra ℂ A] where
  toFun : A →ₗ[ℂ] A
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace Derivation

instance : CoeFun (Derivation A) (fun _ => A → A) where
  coe D := D.toFun

variable (D : Derivation A)

-- LinearMap inheritance gives us algebraic mapping rules for free.
@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := LinearMap.map_add D.toFun x y
@[simp] theorem map_zero : D 0 = 0 := LinearMap.map_zero D.toFun
@[simp] theorem map_sub (x y : A) : D (x - y) = D x - D y := LinearMap.map_sub D.toFun x y
@[simp] theorem map_neg (x : A) : D (-x) = - D x := LinearMap.map_neg D.toFun x
@[simp] theorem map_smul (c : ℂ) (x : A) : D (c • x) = c • D x := LinearMap.map_smul D.toFun c x
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

/-- THEOREM 1: Every derivation strictly annihilates the identity. -/
@[simp]
theorem map_one : D 1 = 0 := by
  have h := D.leibniz 1 1
  rw [mul_one, one_mul] at h
  have h_eq : D 1 = D 1 + D 1 := h.symm
  exact self_eq_add_self.mp h_eq.symm

end Derivation

/-- Inner Modular Generator: ad_K(X) = [K, X]. -/
def adK (K X : A) : A :=
  K * X - X * K

/-- 
  THEOREM 2 (Master Commutator):
  [D, ad_K](X) = ad_{D(K)}(X)
-/
theorem master_dual_flow_commutator (D : Derivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X := by
  dsimp [adK]
  rw [D.map_sub, D.leibniz, D.leibniz]
  abel

/-- 
  THEOREM 3 (Thermal Time Invariance):
  ad_K = 0 ↔ K ∈ Z(A)
-/
theorem thermal_time_kernel (K : A) :
    (∀ X, adK K X = 0) ↔ (∀ X, K * X = X * K) := by
  constructor
  · intro h X
    have hX := h X
    dsimp [adK] at hX
    linear_combination hX
  · intro h X
    dsimp [adK]
    rw [h X, sub_self]

/-!
=============================================================================
LAYER 2: Quantum Geometric Tensor (QGT) and Uncertainty Geometry
=============================================================================
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- Quantum Geometric Tensor (QGT). -/
def QGT (ψ : H) (X Y : EndH) : ℂ :=
  inner (X ψ) (Y ψ) - inner (X ψ) ψ * inner ψ (Y ψ)

/-- Quantum Fisher Information / Fubini-Study Metric. -/
def fisherMetric (ψ : H) (X Y : EndH) : ℝ :=
  (QGT ψ X Y).re

/-- Berry Curvature 2-Form. -/
def berryCurvature (ψ : H) (X Y : EndH) : ℝ :=
  -2 * (QGT ψ X Y).im

/-- Operator Lie Commutator. -/
def opCommutator (X Y : EndH) : EndH :=
  X.comp Y - Y.comp X

@[simp]
theorem opCommutator_apply (X Y : EndH) (v : H) :
    opCommutator X Y v = X (Y v) - Y (X v) := rfl

/-- 
  THEOREM 4 (QGT Modulus Pythagorean Identity):
  |Q_ψ(X, Y)|² = g_ψ(X, Y)² + (1/4) * Ω_ψ(X, Y)²
-/
theorem QGT_normSq_decomposition (ψ : H) (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) =
      (fisherMetric ψ X Y) ^ 2 + (1 / 4) * (berryCurvature ψ X Y) ^ 2 := by
  dsimp [fisherMetric, berryCurvature]
  rw [Complex.normSq_apply]
  have h_sq : (-2 * (QGT ψ X Y).im) ^ 2 = 4 * (QGT ψ X Y).im ^ 2 := by ring
  rw [h_sq]
  ring

/-- 
  THEOREM 5 (Geometric Curvature Bound):
  |Q_ψ(X, Y)|² ≥ (1/4) * Ω_ψ(X, Y)²
-/
theorem QGT_normSq_ge_curvature (ψ : H) (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) ≥ (1 / 4) * (berryCurvature ψ X Y) ^ 2 := by
  rw [QGT_normSq_decomposition]
  have h_sq_nonneg : (fisherMetric ψ X Y) ^ 2 ≥ 0 := sq_nonneg _
  linarith

/-- 
  THEOREM 6 (The Robertson–Schrödinger Uncertainty Bound from QGT)
-/
theorem robertson_schrodinger_qgt_bound
    (ψ : H) (X Y : EndH)
    (h_cauchy : (fisherMetric ψ X X) * (fisherMetric ψ Y Y) ≥ Complex.normSq (QGT ψ X Y)) :
    (fisherMetric ψ X X) * (fisherMetric ψ Y Y) ≥ (1 / 4) * (berryCurvature ψ X Y) ^ 2 := by
  have h_curv := QGT_normSq_ge_curvature ψ X Y
  exact le_trans h_curv h_cauchy

/-- 
  THEOREM 7 (Commutator Uncertainty Principle)
-/
theorem geometric_commutator_uncertainty_bound
    (ψ : H) (X Y : EndH)
    (h_cauchy : (fisherMetric ψ X X) * (fisherMetric ψ Y Y) ≥ Complex.normSq (QGT ψ X Y))
    (h_comm_curv : (berryCurvature ψ X Y : ℂ) * I = inner ψ (opCommutator X Y ψ)) :
    (fisherMetric ψ X X) * (fisherMetric ψ Y Y) ≥ (1 / 4) * Complex.normSq (inner ψ (opCommutator X Y ψ)) := by
  have h_bound := robertson_schrodinger_qgt_bound ψ X Y h_cauchy
  have h_normSq_comm :
    Complex.normSq (inner ψ (opCommutator X Y ψ)) = (berryCurvature ψ X Y) ^ 2 := by
    rw [← h_comm_curv]
    rw [Complex.normSq_mul, Complex.normSq_I, mul_one]
    exact Complex.normSq_ofReal (berryCurvature ψ X Y)
  rw [h_normSq_comm]
  exact h_bound

/-!
=============================================================================
LAYER 3: Thermal Equilibrium & KMS States
=============================================================================
-/

/-- A quantum state generalized as a normalized ℂ-linear functional. -/
structure QuantumState (A : Type*) [Ring A] [Algebra ℂ A] where
  toFun : A →ₗ[ℂ] ℂ
  normalized : toFun 1 = 1

namespace QuantumState

instance : CoeFun (QuantumState A) (fun _ => A → ℂ) where
  coe ω := ω.toFun

variable (ω : QuantumState A)

@[simp] theorem map_sub (x y : A) : ω (x - y) = ω x - ω y := LinearMap.map_sub ω.toFun x y
@[simp] theorem map_add (x y : A) : ω (x + y) = ω x + ω y := LinearMap.map_add ω.toFun x y
@[simp] theorem map_zero : ω 0 = 0 := LinearMap.map_zero ω.toFun

end QuantumState

/-- The Infinitesimal Kubo-Martin-Schwinger (KMS) Condition. -/
def IsInfinitesimalKMS (ω : QuantumState A) (D : Derivation A) (β : ℝ) : Prop :=
  ∀ X Y : A, I * (β : ℂ) * ω (X * D Y) = ω (Y * X) - ω (X * Y)

/-- 
  THEOREM 8 (The Tracial Limit):
  At infinite temperature (β → 0), a KMS state rigorously reduces to a tracial state.
-/
theorem kms_zero_beta_is_trace (ω : QuantumState A) (D : Derivation A)
    (h_kms : IsInfinitesimalKMS ω D 0) : ∀ X Y : A, ω (X * Y) = ω (Y * X) := by
  intro X Y
  have h := h_kms X Y
  have h_zero_beta : I * (0 : ℂ) * ω (X * D Y) = 0 := by ring
  rw [h_zero_beta] at h
  exact sub_eq_zero.mp h.symm

/-- 
  THEOREM 9 (Thermal Stationarity):
  Any state satisfying the KMS condition is invariant under the time evolution.
-/
theorem kms_state_invariant (ω : QuantumState A) (D : Derivation A) (β : ℝ)
    (h_kms : IsInfinitesimalKMS ω D β) (h_beta_nz : (β : ℂ) ≠ 0) :
    ∀ X : A, ω (D X) = 0 := by
  intro X
  have h := h_kms 1 X
  simp only [one_mul, mul_one] at h
  have h_comm : ω X - ω X = 0 := sub_self (ω X)
  rw [h_comm] at h
  have h_mul : I * (β : ℂ) * ω (D X) = 0 := h
  simp only [mul_eq_zero, I_ne_zero, false_or] at h_mul
  exact h_mul.resolve_left h_beta_nz

end InfoGeometry.EndToEnd
