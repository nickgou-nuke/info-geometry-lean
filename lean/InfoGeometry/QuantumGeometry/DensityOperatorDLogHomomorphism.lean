import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.QuantumGeometry.DensityDLog

variable {R : Type*} [CommRing R]

/-- An additive derivation on a commutative ring R. -/
structure CommRingDerivation (R : Type*) [CommRing R] where
  toFun : R → R
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace CommRingDerivation

variable (D : CommRingDerivation R)

instance : CoeFun (CommRingDerivation R) (fun _ => R → R) where
  coe D := D.toFun

@[simp] theorem map_add (x y : R) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : R) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by
    rw [add_zero, ← D.map_add, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_neg (x : R) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : R) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

@[simp]
theorem map_one : D 1 = 0 := by
  have h : D 1 + D 1 = D 1 := by
    calc
      D 1 + D 1 = D (1 * 1) := by rw [D.leibniz, mul_one, one_mul]
      _ = D 1 := by rw [mul_one]
  have h2 : (D 1 + D 1) - D 1 = D 1 - D 1 := congrArg (fun x => x - D 1) h
  simpa using h2

end CommRingDerivation

/-- The Logarithmic Derivative of an invertible density operator / unit:
    dlog_D(u) = u⁻¹ * D(u) -/
def dlog (D : CommRingDerivation R) (u : Rˣ) : R :=
  (u⁻¹ : Rˣ).val * D (u.val)

@[simp]
theorem dlog_one (D : CommRingDerivation R) :
    dlog D 1 = 0 := by
  dsimp [dlog]
  rw [D.map_one, mul_zero]

theorem dlog_mul (D : CommRingDerivation R) (u v : Rˣ) :
    dlog D (u * v) = dlog D u + dlog D v := by
  have hu : (u⁻¹ : Rˣ).val * u.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hv : (v⁻¹ : Rˣ).val * v.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  dsimp [dlog]
  rw [D.leibniz, mul_inv_rev, Units.val_mul]
  calc
    ((v⁻¹ : Rˣ).val * (u⁻¹ : Rˣ).val) * (D (u.val) * v.val + u.val * D (v.val))
      = ((u⁻¹ : Rˣ).val * D (u.val)) * ((v⁻¹ : Rˣ).val * v.val) +
        ((v⁻¹ : Rˣ).val * D (v.val)) * ((u⁻¹ : Rˣ).val * u.val) := by ring
    _ = ((u⁻¹ : Rˣ).val * D (u.val)) * 1 + ((v⁻¹ : Rˣ).val * D (v.val)) * 1 := by
      rw [hu, hv]
    _ = (u⁻¹ : Rˣ).val * D (u.val) + (v⁻¹ : Rˣ).val * D (v.val) := by
      rw [mul_one, mul_one]

theorem dlog_inv (D : CommRingDerivation R) (u : Rˣ) :
    dlog D (u⁻¹) = - dlog D u := by
  have h : dlog D (u * u⁻¹) = dlog D u + dlog D (u⁻¹) := dlog_mul D u (u⁻¹)
  rw [mul_inv_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Bundled Group Homomorphism: dlogHom : Rˣ →* Multiplicative R -/
def dlogHom (D : CommRingDerivation R) : Rˣ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd (dlog D u)
  map_one' := by
    change Multiplicative.ofAdd (dlog D 1) = Multiplicative.ofAdd 0
    rw [dlog_one]
  map_mul' u v := by
    change Multiplicative.ofAdd (dlog D (u * v)) = Multiplicative.ofAdd (dlog D u) * Multiplicative.ofAdd (dlog D v)
    rw [dlog_mul]
    rfl

/-- Scalar Density Operator in a commutative von Neumann center -/
def scalarDensityOperator (u : Rˣ) : R := u.val

/-- Radon-Nikodym derivative unit between two density states: Δ_{u, v} = u * v⁻¹ -/
def rnDerivativeUnit (u v : Rˣ) : Rˣ := u * v⁻¹

/-- Connes-Radon-Nikodym chain rule: Δ_{u, w} = Δ_{u, v} * Δ_{v, w} -/
theorem rnDerivative_chain_rule (u v w : Rˣ) :
    rnDerivativeUnit u w = rnDerivativeUnit u v * rnDerivativeUnit v w := by
  dsimp [rnDerivativeUnit]
  group

/-- The modular logarithmic derivative of the Radon-Nikodym unit:
    dlog_D(Δ_{u, v}) = dlog_D(u) - dlog_D(v) -/
theorem dlog_rnDerivative (D : CommRingDerivation R) (u v : Rˣ) :
    dlog D (rnDerivativeUnit u v) = dlog D u - dlog D v := by
  dsimp [rnDerivativeUnit]
  rw [dlog_mul, dlog_inv, sub_eq_add_neg]

/-- Relative modular operator factorization: Δ_{u, v} = u * v⁻¹ -/
theorem modularOperator_eq_scalarDensityOperator_rnDerivativeUnit (u v : Rˣ) :
    (rnDerivativeUnit u v).val = scalarDensityOperator u * (v⁻¹ : Rˣ).val := rfl

end InfoGeometry.QuantumGeometry.DensityDLog
