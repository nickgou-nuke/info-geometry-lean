import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Noncommutative Connections, Gauge Transformations, and Maurer-Cartan Geometry

This module formalizes:
1. Noncommutative covariant derivatives `∇_D(X) = D(X) + [A_conn, X]`.
2. Proof that `∇_D` satisfies the exact Leibniz product rule on associative algebras.
3. Unitary/Invertible gauge transformations on connections: `A_conn' = u A_conn u⁻¹ + u D(u⁻¹)`.
4. Derivation of unit inverses: `D(u⁻¹) = - u⁻¹ D(u) u⁻¹`.
5. Noncommutative Maurer-Cartan 1-forms `θ = u D(u⁻¹)` and the quadratic identity `θ² = - D(u) D(u⁻¹)`.
6. Noncommutative Maurer-Cartan Flatness Theorem: `D(u) D(u⁻¹) + θ² = 0`.
7. Noncommutative Gauge Equivariance: `∇_{Aᵘ}(Xᵘ) = (∇_A(X))ᵘ` decomposed into explicit helper lemmas.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-- An R-algebra derivation D : A → A satisfying the Leibniz rule:
    D(x * y) = D(x) * y + x * D(y) -/
structure AlgebraDerivation (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  toLinearMap : A →ₗ[R] A
  leibniz' : ∀ x y, toLinearMap (x * y) = toLinearMap x * y + x * toLinearMap y

namespace AlgebraDerivation

variable (D : AlgebraDerivation R A)

instance : CoeFun (AlgebraDerivation R A) (fun _ => A → A) where
  coe D := D.toLinearMap

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.toLinearMap.map_add x y
@[simp] theorem map_smul (r : R) (x : A) : D (r • x) = r • D x := D.toLinearMap.map_smul r x
@[simp] theorem map_sub (x y : A) : D (x - y) = D x - D y := D.toLinearMap.map_sub x y
@[simp] theorem map_neg (x : A) : D (-x) = - D x := D.toLinearMap.map_neg x
@[simp] theorem map_zero : D 0 = 0 := D.toLinearMap.map_zero
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

/-- Derivation annihilates 1 in any ring -/
@[simp]
theorem map_one : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by
    calc
      D 1 = D (1 * 1) := by rw [mul_one]
      _ = D 1 * 1 + 1 * D 1 := D.leibniz 1 1
      _ = D 1 + D 1 := by rw [mul_one, one_mul]
  have h2 : (D 1 + D 1) - D 1 = D 1 - D 1 := congrArg (fun x => x - D 1) h.symm
  simpa using h2

/-- Noncommutative connection covariant derivative associated to derivation D and connection 1-form A_conn:
    ∇_D(X) = D(X) + [A_conn, X] -/
def covariantDerivative (A_conn : A) (X : A) : A :=
  D X + (A_conn * X - X * A_conn)

/-- 🏆 THEOREM 1: The Covariant Derivative satisfies the Noncommutative Leibniz Rule:
    ∇_D(X * Y) = ∇_D(X) * Y + X * ∇_D(Y) -/
theorem covariantDerivative_leibniz (A_conn : A) (X Y : A) :
    covariantDerivative D A_conn (X * Y) =
      covariantDerivative D A_conn X * Y + X * covariantDerivative D A_conn Y := by
  dsimp [covariantDerivative]
  rw [D.leibniz]
  calc
    (D X * Y + X * D Y) + (A_conn * (X * Y) - (X * Y) * A_conn)
      = (D X * Y + (A_conn * X - X * A_conn) * Y) +
        (X * D Y + X * (A_conn * Y - Y * A_conn)) := by
          simp only [mul_assoc, sub_mul, mul_sub]
          abel
    _ = (D X + (A_conn * X - X * A_conn)) * Y +
        X * (D Y + (A_conn * Y - Y * A_conn)) := by
          simp only [add_mul, mul_add]

/-- 🏆 THEOREM 2: Derivation of the Inverse Unit:
    D(u⁻¹) = - u⁻¹ * D(u) * u⁻¹ -/
theorem derivation_inv_unit (u : Aˣ) :
    D (u⁻¹ : Aˣ).val = - ((u⁻¹ : Aˣ).val * D (u : A) * (u⁻¹ : Aˣ).val) := by
  have h : D ((u : A) * (u⁻¹ : Aˣ).val) = 0 := by
    rw [Units.mul_inv, map_one]
  rw [D.leibniz] at h
  have h_shift : (u : A) * D (u⁻¹ : Aˣ).val = - (D (u : A) * (u⁻¹ : Aˣ).val) :=
    eq_neg_of_add_eq_zero_right h
  calc
    D (u⁻¹ : Aˣ).val = (u⁻¹ : Aˣ).val * ((u : A) * D (u⁻¹ : Aˣ).val) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (u⁻¹ : Aˣ).val * (- (D (u : A) * (u⁻¹ : Aˣ).val)) := by rw [h_shift]
    _ = - ((u⁻¹ : Aˣ).val * D (u : A) * (u⁻¹ : Aˣ).val) := by
      simp only [mul_neg, mul_assoc]

/-- The Pure Gauge Maurer-Cartan 1-Form:
    θ = u * D(u⁻¹) -/
def pureGaugeForm (u : Aˣ) : A :=
  (u : A) * D (u⁻¹ : Aˣ).val

/-- Equivalence to negative right-derivative:
    θ = - D(u) * u⁻¹ -/
theorem pureGaugeForm_eq_neg (u : Aˣ) :
    pureGaugeForm D u = - (D (u : A) * (u⁻¹ : Aˣ).val) := by
  unfold pureGaugeForm
  rw [D.derivation_inv_unit, mul_neg]
  congr 1
  calc
    (u : A) * ((u⁻¹ : Aˣ).val * D (u : A) * (u⁻¹ : Aˣ).val) =
        ((u : A) * (u⁻¹ : Aˣ).val) * D (u : A) * (u⁻¹ : Aˣ).val := by
          simp only [mul_assoc]
    _ = D (u : A) * (u⁻¹ : Aˣ).val := by
          have hu : (u : A) * (u⁻¹ : Aˣ).val = 1 := Units.mul_inv u
          rw [hu, one_mul]

/-- Conjugation of an observable by an invertible element. -/
def gaugeTransform (u : Aˣ) (X : A) : A :=
  (u : A) * X * (u⁻¹ : Aˣ).val

/-- Gauge transformation of a connection one-form. -/
def gaugeTransformConnection (u : Aˣ) (A_conn : A) : A :=
  (u : A) * A_conn * (u⁻¹ : Aˣ).val + pureGaugeForm D u

/-!
=============================================================================
Focused Helper Lemmas for Gauge Equivariance
=============================================================================
-/

/-- Helper 1: Derivation of conjugated observable -/
theorem gauge_derivation_conjugated (u : Aˣ) (X : A) :
    D (gaugeTransform u X) =
      D (u : A) * X * (u⁻¹ : Aˣ).val +
      (u : A) * D X * (u⁻¹ : Aˣ).val +
      (u : A) * X * D (u⁻¹ : Aˣ).val := by
  dsimp [gaugeTransform]
  calc
    D ((u : A) * X * (u⁻¹ : Aˣ).val)
      = D ((u : A) * X) * (u⁻¹ : Aˣ).val + (u : A) * X * D (u⁻¹ : Aˣ).val := D.leibniz ((u : A) * X) _
    _ = (D (u : A) * X + (u : A) * D X) * (u⁻¹ : Aˣ).val + (u : A) * X * D (u⁻¹ : Aˣ).val := by rw [D.leibniz]
    _ = D (u : A) * X * (u⁻¹ : Aˣ).val + (u : A) * D X * (u⁻¹ : Aˣ).val + (u : A) * X * D (u⁻¹ : Aˣ).val := by
      simp only [add_mul, add_assoc]

/-- Helper 2: Action of gauge-transformed connection on the left -/
theorem gauge_left_connection_prod (u : Aˣ) (A_conn X : A) :
    (gaugeTransformConnection D u A_conn) * (gaugeTransform u X) =
      (u : A) * A_conn * X * (u⁻¹ : Aˣ).val - D (u : A) * X * (u⁻¹ : Aˣ).val := by
  dsimp [gaugeTransformConnection, gaugeTransform, pureGaugeForm]
  have hu_inv : (u⁻¹ : Aˣ).val * (u : A) = 1 := Units.inv_mul u
  have h_prod1 : ((u : A) * A_conn * (u⁻¹ : Aˣ).val) * ((u : A) * X * (u⁻¹ : Aˣ).val) =
      (u : A) * A_conn * X * (u⁻¹ : Aˣ).val := by
    calc
      ((u : A) * A_conn * (u⁻¹ : Aˣ).val) * ((u : A) * X * (u⁻¹ : Aˣ).val)
        = (u : A) * A_conn * ((u⁻¹ : Aˣ).val * (u : A)) * X * (u⁻¹ : Aˣ).val := by simp only [mul_assoc]
      _ = (u : A) * A_conn * 1 * X * (u⁻¹ : Aˣ).val := by rw [hu_inv]
      _ = (u : A) * A_conn * X * (u⁻¹ : Aˣ).val := by simp only [mul_one, mul_assoc]
  have h_prod2 : ((u : A) * D (u⁻¹ : Aˣ).val) * ((u : A) * X * (u⁻¹ : Aˣ).val) =
      - (D (u : A) * X * (u⁻¹ : Aˣ).val) := by
    calc
      ((u : A) * D (u⁻¹ : Aˣ).val) * ((u : A) * X * (u⁻¹ : Aˣ).val)
        = (pureGaugeForm D u) * ((u : A) * X * (u⁻¹ : Aˣ).val) := rfl
      _ = (- (D (u : A) * (u⁻¹ : Aˣ).val)) * ((u : A) * X * (u⁻¹ : Aˣ).val) := by rw [pureGaugeForm_eq_neg]
      _ = - ((D (u : A) * (u⁻¹ : Aˣ).val) * ((u : A) * X * (u⁻¹ : Aˣ).val)) := by rw [neg_mul]
      _ = - (D (u : A) * ((u⁻¹ : Aˣ).val * (u : A)) * X * (u⁻¹ : Aˣ).val) := by simp only [mul_assoc]
      _ = - (D (u : A) * 1 * X * (u⁻¹ : Aˣ).val) := by rw [hu_inv]
      _ = - (D (u : A) * X * (u⁻¹ : Aˣ).val) := by simp only [mul_one, mul_assoc]
  rw [add_mul, h_prod1, h_prod2, sub_eq_add_neg]

/-- Helper 3: Action of gauge-transformed connection on the right -/
theorem gauge_right_connection_prod (u : Aˣ) (A_conn X : A) :
    (gaugeTransform u X) * (gaugeTransformConnection D u A_conn) =
      (u : A) * X * A_conn * (u⁻¹ : Aˣ).val + (u : A) * X * D (u⁻¹ : Aˣ).val := by
  dsimp [gaugeTransformConnection, gaugeTransform, pureGaugeForm]
  have hu_inv : (u⁻¹ : Aˣ).val * (u : A) = 1 := Units.inv_mul u
  have h_prod3 : ((u : A) * X * (u⁻¹ : Aˣ).val) * ((u : A) * A_conn * (u⁻¹ : Aˣ).val) =
      (u : A) * X * A_conn * (u⁻¹ : Aˣ).val := by
    calc
      ((u : A) * X * (u⁻¹ : Aˣ).val) * ((u : A) * A_conn * (u⁻¹ : Aˣ).val)
        = (u : A) * X * ((u⁻¹ : Aˣ).val * (u : A)) * A_conn * (u⁻¹ : Aˣ).val := by simp only [mul_assoc]
      _ = (u : A) * X * 1 * A_conn * (u⁻¹ : Aˣ).val := by rw [hu_inv]
      _ = (u : A) * X * A_conn * (u⁻¹ : Aˣ).val := by simp only [mul_one, mul_assoc]
  have h_prod4 : ((u : A) * X * (u⁻¹ : Aˣ).val) * ((u : A) * D (u⁻¹ : Aˣ).val) =
      (u : A) * X * D (u⁻¹ : Aˣ).val := by
    calc
      ((u : A) * X * (u⁻¹ : Aˣ).val) * ((u : A) * D (u⁻¹ : Aˣ).val)
        = (u : A) * X * ((u⁻¹ : Aˣ).val * (u : A)) * D (u⁻¹ : Aˣ).val := by simp only [mul_assoc]
      _ = (u : A) * X * 1 * D (u⁻¹ : Aˣ).val := by rw [hu_inv]
      _ = (u : A) * X * D (u⁻¹ : Aˣ).val := by simp only [mul_one, mul_assoc]
  rw [mul_add, h_prod3, h_prod4]

/-- 🏆 THEOREM 3: Covariant derivatives are equivariant under simultaneous gauge
    transformation of the connection and observable. -/
theorem covariantDerivative_gauge_equivariant (u : Aˣ) (A_conn X : A) :
    covariantDerivative D (gaugeTransformConnection D u A_conn)
        (gaugeTransform u X) =
      gaugeTransform u (covariantDerivative D A_conn X) := by
  dsimp [covariantDerivative]
  have h_D := gauge_derivation_conjugated D u X
  have h_left := gauge_left_connection_prod D u A_conn X
  have h_right := gauge_right_connection_prod D u A_conn X
  have h_sum :
      D (gaugeTransform u X) +
          ((gaugeTransformConnection D u A_conn) * (gaugeTransform u X) -
           (gaugeTransform u X) * (gaugeTransformConnection D u A_conn)) =
        (u : A) * D X * (u⁻¹ : Aˣ).val +
        (u : A) * A_conn * X * (u⁻¹ : Aˣ).val -
        (u : A) * X * A_conn * (u⁻¹ : Aˣ).val := by
    rw [h_D, h_left, h_right]
    abel
  have h_target :
      gaugeTransform u (covariantDerivative D A_conn X) =
        (u : A) * D X * (u⁻¹ : Aˣ).val +
        (u : A) * A_conn * X * (u⁻¹ : Aˣ).val -
        (u : A) * X * A_conn * (u⁻¹ : Aˣ).val := by
    dsimp [gaugeTransform, covariantDerivative]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
    abel
  exact h_sum.trans h_target.symm

/-- 🏆 THEOREM 4: The Maurer-Cartan Quadratic Identity:
    θ² = - D(u) * D(u⁻¹) -/
theorem pureGaugeForm_sq (u : Aˣ) :
    pureGaugeForm D u * pureGaugeForm D u = - (D (u : A) * D (u⁻¹ : Aˣ).val) := by
  dsimp [pureGaugeForm]
  have h_inv : D (u⁻¹ : Aˣ).val * (u : A) = - ((u⁻¹ : Aˣ).val * D (u : A)) := by
    have h : D ((u⁻¹ : Aˣ).val * (u : A)) = 0 := by
      rw [Units.inv_mul, map_one]
    rw [D.leibniz] at h
    exact eq_neg_of_add_eq_zero_left h
  calc
    (u : A) * D (u⁻¹ : Aˣ).val * ((u : A) * D (u⁻¹ : Aˣ).val)
      = (u : A) * (D (u⁻¹ : Aˣ).val * (u : A)) * D (u⁻¹ : Aˣ).val := by
        simp only [mul_assoc]
    _ = (u : A) * (- ((u⁻¹ : Aˣ).val * D (u : A))) * D (u⁻¹ : Aˣ).val := by rw [h_inv]
    _ = - ((u : A) * (u⁻¹ : Aˣ).val * D (u : A) * D (u⁻¹ : Aˣ).val) := by
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = - (1 * D (u : A) * D (u⁻¹ : Aˣ).val) := by
      congr 1
      calc
        (u : A) * (u⁻¹ : Aˣ).val * D (u : A) * D (u⁻¹ : Aˣ).val =
            ((u : A) * (u⁻¹ : Aˣ).val) * D (u : A) * D (u⁻¹ : Aˣ).val := by
              simp only [mul_assoc]
        _ = 1 * D (u : A) * D (u⁻¹ : Aˣ).val := by
          have hu : (u : A) * (u⁻¹ : Aˣ).val = 1 := Units.mul_inv u
          rw [hu]
    _ = - (D (u : A) * D (u⁻¹ : Aˣ).val) := by rw [one_mul]

/-- 🏆 THEOREM 4: Noncommutative Maurer-Cartan Flatness:
    D(u) * D(u⁻¹) + θ² = 0 -/
theorem maurer_cartan_flatness (u : Aˣ) :
    D (u : A) * D (u⁻¹ : Aˣ).val + pureGaugeForm D u * pureGaugeForm D u = 0 := by
  rw [pureGaugeForm_sq, add_neg_cancel]

/-- Conjugation of an observable by an invertible element. -/
def gaugeTransform (u : Aˣ) (X : A) : A :=
  (u : A) * X * (u⁻¹ : Aˣ).val

/-- Gauge transformation of a connection one-form:
    A_conn' = u A_conn u⁻¹ + u D(u⁻¹) -/
def gaugeTransformConnection (u : Aˣ) (A_conn : A) : A :=
  (u : A) * A_conn * (u⁻¹ : Aˣ).val + pureGaugeForm D u

/-- 🏆 THEOREM 5: The covariant derivative is gauge equivariant:
    ∇_D(A_conn')(u X u⁻¹) = u ∇_D(A_conn)(X) u⁻¹
    where A_conn' = u A_conn u⁻¹ + u D(u⁻¹) -/
theorem covariantDerivative_gauge_equivariant (u : Aˣ) (A_conn X : A) :
    covariantDerivative D (gaugeTransformConnection D u A_conn) (gaugeTransform u X) =
      gaugeTransform u (covariantDerivative D A_conn X) := by
  dsimp [covariantDerivative, gaugeTransformConnection, gaugeTransform, pureGaugeForm]
  -- Expand D(u * X * u⁻¹) using Leibniz rule
  rw [D.leibniz]
  -- Expand all products explicitly
  simp only [mul_assoc, add_mul, mul_add, sub_mul, mul_sub]
  -- Use D(u⁻¹) = -u⁻¹ D(u) u⁻¹
  have h_inv : D (u⁻¹ : Aˣ).val = -((u⁻¹ : Aˣ).val * D (u : A) * (u⁻¹ : Aˣ).val) := D.derivation_inv_unit u
  rw [h_inv]
  -- Simplify signs and unit identities
  simp only [mul_neg, neg_mul, mul_assoc, Units.mul_inv, one_mul]
  -- Cancel matching terms: D(u)X u⁻¹ - D(u)X u⁻¹ = 0
  -- and -u X u⁻¹ D(u) u⁻¹ + u X u⁻¹ D(u) u⁻¹ = 0
  abel

end AlgebraDerivation

end InfoGeometry.NCG

end noncomputable section
