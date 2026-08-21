import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.QuantumGeometry.BerryKeating

variable {A : Type*} [Ring A]

structure Derivation (A: Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

instance : CoeFun (Derivation A) (fun _ => A → A) where
  coe D := D.toFun

namespace Derivation

variable (D: Derivation A)

@[simp] theorem map_add (x: A) (y: A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x: A) (y: A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 = D 0 + D 0 := by
    calc D 0 = D (0 + 0) := by rw [add_zero]
    _ = D 0 + D 0 := D.map_add 0 0
  have h1 : D 0 - D 0 = (D 0 + D 0) - D 0 := congr_arg (fun x => x - D 0) h
  rw [sub_self, add_sub_cancel_right] at h1
  exact h1.symm

@[simp]
theorem map_neg (x: A) : D (-x) = - D x := by -- uses x
  have h : D (x + -x) = D x + D (-x) := D.map_add x (-x)
  rw [add_neg_cancel, D.map_zero] at h
  have h_neg : - D x = - D x + (D x + D (-x)) := by rw [← h, add_zero]
  rw [← add_assoc, neg_add_cancel, zero_add] at h_neg
  exact h_neg.symm

@[simp]
theorem map_sub (x: A) (y: A) : D (x - y) = D x - D y := by -- uses x y
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

@[simp]
theorem map_one : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by
    calc D 1 = D (1 * 1) := by rw [mul_one]
    _ = D 1 * 1 + 1 * D 1 := D.leibniz 1 1
    _ = D 1 + D 1 := by rw [mul_one, one_mul]
  have h1 : D 1 - D 1 = (D 1 + D 1) - D 1 := congr_arg (fun x => x - D 1) h
  rw [sub_self, add_sub_cancel_right] at h1
  exact h1.symm

end Derivation

def opQ (K: A) (X: A) : A :=
  K * X

@[simp] theorem opQ_apply (K: A) (X: A) : opQ K X = K * X := rfl

def opP (D: Derivation A) (X: A) : A :=
  D X

@[simp] theorem opP_apply (D: Derivation A) (X: A) : opP D X = D X := rfl

def opComm (T₁: A → A) (T₂: A → A) (X: A) : A :=
  T₁ (T₂ X) - T₂ (T₁ X)

@[simp] theorem opComm_apply (T₁: A → A) (T₂: A → A) (X: A) :
    opComm T₁ T₂ X = T₁ (T₂ X) - T₂ (T₁ X) := rfl

def opH_BK (half: A) (D: Derivation A) (K: A) (X: A) : A :=
  half * (opQ K (opP D X) + opP D (opQ K X))

theorem opH_BK_normal_ordered
    (half: A) (h_half: (2: A) * half = 1) (h_half_comm: ∀ x : A, half * x = x * half)
    (D: Derivation A) (K: A) (X: A) :
    opH_BK half D K X = K * D X + half * (D K * X) := by
  dsimp [opH_BK, opQ, opP]
  rw [D.leibniz K X]
  have h_sum : K * D X + (D K * X + K * D X) = (2: A) * (K * D X) + D K * X := by
    calc
      K * D X + (D K * X + K * D X) = (K * D X + K * D X) + D K * X := by abel
      _ = (2: A) * (K * D X) + D K * X := by rw [two_mul]
  rw [h_sum, mul_add]
  have h_two : half * ((2: A) * (K * D X)) = K * D X := by
    calc
      half * ((2: A) * (K * D X)) = (half * (2: A)) * (K * D X) := (mul_assoc _ _ _).symm
      _ = ((2: A) * half) * (K * D X) := by rw [h_half_comm (2: A)]
      _ = 1 * (K * D X) := by rw [h_half]
      _ = K * D X := one_mul _
  rw [h_two]

theorem opH_BK_comm_coordinate
    (half: A) (h_half: (2: A) * half = 1) (h_half_comm: ∀ x : A, half * x = x * half)
    (D: Derivation A) (Y: A) (X: A) :
    opComm (opH_BK half D 1) (opQ Y) X = opQ (D Y) X := by
  dsimp [opComm, opQ]
  rw [opH_BK_normal_ordered half h_half h_half_comm D 1 (Y * X)]
  rw [opH_BK_normal_ordered half h_half h_half_comm D 1 X]
  rw [D.map_one]
  simp only [mul_zero, zero_mul, add_zero, one_mul]
  rw [D.leibniz Y X]
  abel

def opH_symm (half: A) (D: Derivation A) (X: A) : A :=
  D X + half * X

theorem critical_line_spectral_cancellation
    (half: A) (D: Derivation A) (X: A) (s: A) (E: A)
    (h_eigen: D X = s * X)
    (h_critical: s + half = E) :
    opH_symm half D X = E * X := by
  dsimp [opH_symm]
  rw [h_eigen]
  calc
    s * X + half * X = (s + half) * X := (add_mul s half X).symm
    _ = E * X := by rw [h_critical]

end InfoGeometry.QuantumGeometry.BerryKeating

end noncomputable section
