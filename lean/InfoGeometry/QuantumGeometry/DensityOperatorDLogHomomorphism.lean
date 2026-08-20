import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.QuantumGeometry.DensityDLog

/-!
=============================================================================
SECTION 1: Ring Derivations
=============================================================================
-/

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

/-!
=============================================================================
SECTION 2: The Density Operator Logarithmic Derivative Group Homomorphism
=============================================================================
-/

/-- The Logarithmic Derivative of an invertible density operator / unit:
    dlog_D(u) = u⁻¹ * D(u) -/
def dlog (D : CommRingDerivation R) (u : Rˣ) : R :=
  (u⁻¹ : Rˣ).val * D (u.val)

/-- 🏆 THEOREM 1: The logarithmic derivative annihilates the identity state:
    dlog_D(1) = 0 -/
@[simp]
theorem dlog_one (D : CommRingDerivation R) :
    dlog D 1 = 0 := by
  dsimp [dlog]
  rw [D.map_one, mul_zero]

/-- 🏆 THEOREM 2: Logarithmic Derivative Group Homomorphism:
    dlog_D(u * v) = dlog_D(u) + dlog_D(v)
    The logarithmic derivation is a strict group homomorphism from the multiplicative
    group of density units Rˣ to the additive group of observables (R, +). -/
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

/-- 🏆 THEOREM 3: Logarithmic Derivative Inversion (Time-Reversal):
    dlog_D(u⁻¹) = - dlog_D(u) -/
theorem dlog_inv (D : CommRingDerivation R) (u : Rˣ) :
    dlog D (u⁻¹) = - dlog D u := by
  have h : dlog D (u * u⁻¹) = dlog D u + dlog D (u⁻¹) := dlog_mul D u (u⁻¹)
  rw [mul_inv_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- 🏆 THEOREM 4: Bundled Group Homomorphism:
    dlogHom : Rˣ →* Multiplicative R -/
def dlogHom (D : CommRingDerivation R) : Rˣ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd (dlog D u)
  map_one' := by
    change Multiplicative.ofAdd (dlog D 1) = Multiplicative.ofAdd 0
    rw [dlog_one]
  map_mul' u v := by
    change Multiplicative.ofAdd (dlog D (u * v)) = Multiplicative.ofAdd (dlog D u) * Multiplicative.ofAdd (dlog D v)
    rw [dlog_mul]
    rfl

/-- 🏆 THEOREM 5: Power Scaling:
    dlog_D(uⁿ) = n * dlog_D(u) for all n ∈ ℕ -/
theorem dlog_pow (D : CommRingDerivation R) (u : Rˣ) (n : ℕ) :
    dlog D (u ^ n) = (n : R) * dlog D u := by
  induction n with
  | zero =>
    rw [pow_zero, dlog_one, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, dlog_mul, ih, Nat.cast_succ]
    ring

/-- 🏆 THEOREM 6: Integer Power Scaling:
    dlog_D(uᶻ) = z • dlog_D(u) for all z ∈ ℤ -/
theorem dlog_zpow (D : CommRingDerivation R) (u : Rˣ) (z : ℤ) :
    dlog D (u ^ z) = z • dlog D u := by
  have h := (dlogHom D).map_zpow u z
  change Multiplicative.ofAdd (dlog D (u ^ z)) = (Multiplicative.ofAdd (dlog D u)) ^ z at h
  rw [← ofAdd_zsmul] at h
  exact Multiplicative.ofAdd.injective h

end InfoGeometry.QuantumGeometry.DensityDLog

end noncomputable section
