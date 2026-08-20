import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Noncommutative Radon–Nikodym Logarithmic Derivations

This module establishes the exact non-commutative formalization of:
1. Arbitrary (non-commutative) ring derivations `D : A → A`.
2. Left and Right logarithmic derivatives for non-commuting units:
   `dlog_L(u) = u⁻¹ * D(u)`
   `dlog_R(u) = D(u) * u⁻¹`
3. The exact Noncommutative Maurer-Cartan / Connes Gauge Cocycle product rule:
   `dlog_L(u * v) = v⁻¹ * dlog_L(u) * v + dlog_L(v)`
   `dlog_R(u * v) = dlog_R(u) + u * dlog_R(v) * u⁻¹`
4. The Noncommutative Inversion Duality:
   `dlog_L(u⁻¹) = - dlog_R(u)`
5. The relative Noncommutative Radon–Nikodym unit `Δ_{u, v} = u * v⁻¹` and chain rule.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.Noncommutative

variable {A : Type*} [Ring A]

/-- A Leibniz derivation on an arbitrary (noncommutative) ring A. -/
structure NoncommutativeDerivation (A : Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace NoncommutativeDerivation

variable (D : NoncommutativeDerivation A)

instance : CoeFun (NoncommutativeDerivation A) (fun _ => A → A) where
  coe D := D.toFun

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by
    rw [add_zero, ← D.map_add, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_neg (x : A) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

@[simp]
theorem map_one : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by
    calc
      D 1 = D (1 * 1) := by rw [mul_one]
      _ = D 1 * 1 + 1 * D 1 := D.leibniz 1 1
      _ = D 1 + D 1 := by rw [mul_one, one_mul]
  have h2 : (D 1 + D 1) - D 1 = D 1 - D 1 := congrArg (fun x => x - D 1) h.symm
  simpa using h2

end NoncommutativeDerivation

open NoncommutativeDerivation

/-- Noncommutative Left Logarithmic Derivative:
    dlog_L(u) = u⁻¹ * D(u) -/
def dlogL (D : NoncommutativeDerivation A) (u : Aˣ) : A :=
  (u⁻¹ : Aˣ).val * D (u.val)

/-- Noncommutative Right Logarithmic Derivative:
    dlog_R(u) = D(u) * u⁻¹ -/
def dlogR (D : NoncommutativeDerivation A) (u : Aˣ) : A :=
  D (u.val) * (u⁻¹ : Aˣ).val

/-- The right logarithmic derivative detects stationary units exactly. -/
theorem dlogR_eq_zero_iff (D : NoncommutativeDerivation A) (u : Aˣ) :
    dlogR D u = 0 ↔ D u.val = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun x : A => x * u.val) h
    simpa [dlogR, mul_assoc, u.inv_val] using h'
  · intro h
    simp [dlogR, h]

@[simp]
theorem dlogL_one (D : NoncommutativeDerivation A) :
    dlogL D 1 = 0 := by
  dsimp [dlogL]
  rw [D.map_one, mul_zero]

@[simp]
theorem dlogR_one (D : NoncommutativeDerivation A) :
    dlogR D 1 = 0 := by
  dsimp [dlogR]
  rw [D.map_one, zero_mul]

/-- 🏆 THEOREM 1: Noncommutative Logarithmic Product Rule (Connes Gauge Cocycle).
    dlog_L(u * v) = v⁻¹ * dlog_L(u) * v + dlog_L(v)
    This is the fundamental Noncommutative Maurer-Cartan / Gauge Cocycle transformation. -/
theorem dlogL_mul_noncommutative (D : NoncommutativeDerivation A) (u v : Aˣ) :
    dlogL D (u * v) = (v⁻¹ : Aˣ).val * dlogL D u * (v : Aˣ).val + dlogL D v := by
  dsimp [dlogL]
  rw [D.leibniz]
  have h_inv : ((u * v)⁻¹ : Aˣ).val = (v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val := by
    rw [mul_inv_rev, Units.val_mul]
  rw [h_inv]
  calc
    ((v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val) * (D (u.val) * (v.val) + (u.val) * D (v.val))
      = ((v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val) * (D (u.val) * (v.val)) +
        ((v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val) * ((u.val) * D (v.val)) := by rw [mul_add]
    _ = (v⁻¹ : Aˣ).val * ((u⁻¹ : Aˣ).val * D (u.val)) * (v.val) +
        (v⁻¹ : Aˣ).val * (((u⁻¹ : Aˣ).val * (u.val)) * D (v.val)) := by
          simp only [mul_assoc]
    _ = (v⁻¹ : Aˣ).val * ((u⁻¹ : Aˣ).val * D (u.val)) * (v.val) +
        (v⁻¹ : Aˣ).val * (1 * D (v.val)) := by
          have hu : (u⁻¹ : Aˣ).val * (u.val) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          rw [hu]
    _ = (v⁻¹ : Aˣ).val * ((u⁻¹ : Aˣ).val * D (u.val)) * (v.val) +
        (v⁻¹ : Aˣ).val * D (v.val) := by rw [one_mul]

/-- 🏆 THEOREM 2: Noncommutative Right Logarithmic Product Rule.
    dlog_R(u * v) = dlog_R(u) + u * dlog_R(v) * u⁻¹ -/
theorem dlogR_mul_noncommutative (D : NoncommutativeDerivation A) (u v : Aˣ) :
    dlogR D (u * v) = dlogR D u + (u : Aˣ).val * dlogR D v * (u⁻¹ : Aˣ).val := by
  dsimp [dlogR]
  rw [D.leibniz]
  have h_inv : ((u * v)⁻¹ : Aˣ).val = (v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val := by
    rw [mul_inv_rev, Units.val_mul]
  rw [h_inv]
  calc
    (D (u.val) * (v.val) + (u.val) * D (v.val)) * ((v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val)
      = (D (u.val) * (v.val)) * ((v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val) +
        ((u.val) * D (v.val)) * ((v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val) := by rw [add_mul]
    _ = D (u.val) * ((v.val * (v⁻¹ : Aˣ).val) * (u⁻¹ : Aˣ).val) +
        (u.val * (D (v.val) * (v⁻¹ : Aˣ).val)) * (u⁻¹ : Aˣ).val := by
          simp only [mul_assoc]
    _ = D (u.val) * (1 * (u⁻¹ : Aˣ).val) +
        (u.val * (D (v.val) * (v⁻¹ : Aˣ).val)) * (u⁻¹ : Aˣ).val := by
          have hv : (v.val * (v⁻¹ : Aˣ).val) = 1 := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          rw [hv]
    _ = D (u.val) * (u⁻¹ : Aˣ).val +
        (u.val * (D (v.val) * (v⁻¹ : Aˣ).val)) * (u⁻¹ : Aˣ).val := by rw [one_mul]

/-- Under the precise commutation hypothesis that kills the conjugation term,
the right noncommutative logarithmic derivative becomes additive. -/
theorem dlogR_mul_of_commute (D : NoncommutativeDerivation A) (u v : Aˣ)
    (h_comm : Commute (u : Aˣ).val (dlogR D v)) :
    dlogR D (u * v) = dlogR D u + dlogR D v := by
  rw [dlogR_mul_noncommutative]
  have hu : (u : Aˣ).val * (u⁻¹ : Aˣ).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc
    dlogR D u + (u : Aˣ).val * dlogR D v * (u⁻¹ : Aˣ).val
        = dlogR D u + ((u : Aˣ).val * dlogR D v) * (u⁻¹ : Aˣ).val := by
          simp only [mul_assoc]
    _ = dlogR D u + ((dlogR D v) * (u : Aˣ).val) * (u⁻¹ : Aˣ).val := by
          rw [h_comm.eq]
    _ = dlogR D u + dlogR D v * ((u : Aˣ).val * (u⁻¹ : Aˣ).val) := by
          simp only [mul_assoc]
    _ = dlogR D u + dlogR D v := by rw [hu, mul_one]

/- A central left factor removes the conjugation term in the right cocycle. -/
theorem dlogR_mul_of_central (D : NoncommutativeDerivation A) (c u : Aˣ)
    (h_central : ∀ x, (c : Aˣ).val * x = x * (c : Aˣ).val) :
    dlogR D (c * u) = dlogR D c + dlogR D u := by
  apply dlogR_mul_of_commute
  exact h_central (dlogR D u)

/-- 🏆 THEOREM 3: Noncommutative Inversion Duality:
    dlog_L(u⁻¹) = - dlog_R(u) -/
theorem dlogL_inv_eq_neg_dlogR (D : NoncommutativeDerivation A) (u : Aˣ) :
    dlogL D (u⁻¹) = - dlogR D u := by
  have h_prod : D (u.val * (u⁻¹ : Aˣ).val) = 0 := by
    have hu : u.val * (u⁻¹ : Aˣ).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hu, D.map_one]
  rw [D.leibniz] at h_prod
  -- h_prod : D u * u⁻¹ + u * D(u⁻¹) = 0
  have h_shift : u.val * D (u⁻¹ : Aˣ).val = - (D (u.val) * (u⁻¹ : Aˣ).val) := by
    exact eq_neg_of_add_eq_zero_right h_prod
  dsimp [dlogL, dlogR]
  have h_inv_inv : ((u⁻¹ : Aˣ)⁻¹ : Aˣ).val = u.val := rfl
  rw [h_inv_inv, h_shift]

theorem dlogR_inv_eq_neg_dlogL (D : NoncommutativeDerivation A) (u : Aˣ) :
    dlogR D (u⁻¹) = - dlogL D u := by
  have h := dlogL_inv_eq_neg_dlogR D (u⁻¹)
  rw [inv_inv] at h
  rw [h, neg_neg]

/-- 🏆 THEOREM 4: Noncommutative Commuting Homomorphism:
    If v commutes with dlog_L(u), then dlog_L(u * v) = dlog_L(u) + dlog_L(v). -/
theorem dlogL_mul_of_commute (D : NoncommutativeDerivation A) (u v : Aˣ)
    (h_comm : dlogL D u * (v : Aˣ).val = (v : Aˣ).val * dlogL D u) :
    dlogL D (u * v) = dlogL D u + dlogL D v := by
  rw [dlogL_mul_noncommutative]
  have hv : (v⁻¹ : Aˣ).val * (v : Aˣ).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc
    (v⁻¹ : Aˣ).val * dlogL D u * (v : Aˣ).val + dlogL D v
      = (v⁻¹ : Aˣ).val * (dlogL D u * (v : Aˣ).val) + dlogL D v := by simp only [mul_assoc]
    _ = (v⁻¹ : Aˣ).val * ((v : Aˣ).val * dlogL D u) + dlogL D v := by rw [h_comm]
    _ = ((v⁻¹ : Aˣ).val * (v : Aˣ).val) * dlogL D u + dlogL D v := by simp only [mul_assoc]
    _ = 1 * dlogL D u + dlogL D v := by rw [hv]
    _ = dlogL D u + dlogL D v := by rw [one_mul]

/-- 🏆 THEOREM 5: Noncommutative Central Cocycle Homomorphism:
    For any central unit c ∈ Z(Aˣ), dlog_L(u * c) = dlog_L(u) + dlog_L(c). -/
theorem dlogL_mul_of_central (D : NoncommutativeDerivation A) (u c : Aˣ)
    (h_central : ∀ x, x * (c : Aˣ).val = (c : Aˣ).val * x) :
    dlogL D (u * c) = dlogL D u + dlogL D c := by
  apply dlogL_mul_of_commute
  exact h_central (dlogL D u)

/-- Relative Noncommutative Modular Radon–Nikodym unit: Δ_{u, v} = u * v⁻¹ -/
def rnUnit (u v : Aˣ) : Aˣ := u * v⁻¹

/-- Connes Noncommutative Chain Rule: Δ_{u, w} = Δ_{u, v} * Δ_{v, w} -/
theorem rnUnit_chain_rule (u v w : Aˣ) :
    rnUnit u w = rnUnit u v * rnUnit v w := by
  dsimp [rnUnit]
  group

/-- Right logarithmic cocycle of a relative Radon--Nikodym unit. -/
theorem dlogR_rnUnit (D : NoncommutativeDerivation A) (u v : Aˣ) :
    dlogR D (rnUnit u v) =
      dlogR D u - (u : Aˣ).val * dlogL D v * (u⁻¹ : Aˣ).val := by
  dsimp [rnUnit]
  rw [dlogR_mul_noncommutative, dlogR_inv_eq_neg_dlogL]
  simp only [mul_neg, neg_mul, sub_eq_add_neg]

/-- Noncommutative Logarithmic Cocycle of relative Radon-Nikodym unit:
    dlog_L(Δ_{u, v}) = v * dlog_L(u) * v⁻¹ - dlog_R(v) -/
theorem dlogL_rnUnit (D : NoncommutativeDerivation A) (u v : Aˣ) :
    dlogL D (rnUnit u v) =
      (v : Aˣ).val * dlogL D u * (v⁻¹ : Aˣ).val - dlogR D v := by
  dsimp [rnUnit]
  rw [dlogL_mul_noncommutative, dlogL_inv_eq_neg_dlogR]
  have h_inv_inv : ((v⁻¹ : Aˣ)⁻¹ : Aˣ).val = (v : Aˣ).val := rfl
  rw [h_inv_inv, sub_eq_add_neg]

end InfoGeometry.Modular.Noncommutative
