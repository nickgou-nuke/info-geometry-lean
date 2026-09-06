import Mathlib

/-!
# Symmetric/skew geometry of a doubled chiral carrier

For `E = V × V*` the evaluation pairing has a canonical symmetric and
antisymmetric decomposition.  The two summands are isotropic for both forms,
and the para-complex involution records the sign relating them.  This is a
purely algebraic `V ⊕ V*` statement; it does not assert a manifold or an
analytic completion.
-/

namespace InfoGeometry.Canonical.DoubledChiralPairing

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V]

abbrev Dual (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  Module.Dual R V
abbrev Doubled (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  V × Dual R V

def evaluation (X Y : Doubled R V) : R := X.2 Y.1

def eta (X Y : Doubled R V) : R :=
  evaluation X Y + evaluation Y X

def omega (X Y : Doubled R V) : R :=
  evaluation X Y - evaluation Y X

/-! The parent evaluation pairing is recovered by the two components without
    assuming that `2` is invertible. -/

theorem two_mul_evaluation_eq_eta_add_omega (X Y : Doubled R V) :
    2 * evaluation X Y = eta X Y + omega X Y := by
  unfold eta omega
  ring

theorem two_mul_evaluation_swap_eq_eta_sub_omega (X Y : Doubled R V) :
    2 * evaluation Y X = eta X Y - omega X Y := by
  unfold eta omega
  ring

def para (X : Doubled R V) : Doubled R V :=
  (X.1, -X.2)

theorem eta_add_omega_eq_two_evaluation (X Y : Doubled R V) :
    eta X Y + omega X Y = (2 : R) * evaluation X Y := by
  unfold eta omega
  ring

theorem eta_sub_omega_eq_two_evaluation_swap (X Y : Doubled R V) :
    eta X Y - omega X Y = (2 : R) * evaluation Y X := by
  unfold eta omega
  ring

@[simp] theorem eta_swap (X Y : Doubled R V) :
    eta X Y = eta Y X := by
  simp [eta, add_comm]

@[simp] theorem omega_swap (X Y : Doubled R V) :
    omega Y X = -omega X Y := by
  simp [omega, sub_eq_add_neg, add_comm]

@[simp] theorem para_involutive (X : Doubled R V) :
    para (para X) = X := by
  cases X with
  | mk v α => simp [para]

theorem para_primal (v : V) :
    para (R := R) (v, 0) = (v, 0) := by
  simp [para]

theorem para_dual (α : Dual R V) :
    para (R := R) (0, α) = (0, -α) := by
  simp [para]

theorem omega_eq_eta_para_right (X Y : Doubled R V) :
    omega X Y = eta X (para Y) := by
  cases X with
  | mk v α =>
    cases Y with
    | mk w β =>
      simp only [omega, eta, para, evaluation]
      rw [sub_eq_add_neg]
      simp

theorem eta_restrict_left_zero (v w : V) :
    eta (R := R) (v, 0) (w, 0) = 0 := by
  simp [eta, evaluation]

theorem eta_restrict_right_zero (α β : Dual R V) :
    eta (R := R) (0, α) (0, β) = 0 := by
  simp [eta, evaluation]

theorem omega_restrict_left_zero (v w : V) :
    omega (R := R) (v, 0) (w, 0) = 0 := by
  simp [omega, evaluation]

theorem omega_restrict_right_zero (α β : Dual R V) :
    omega (R := R) (0, α) (0, β) = 0 := by
  simp [omega, evaluation]

section NeutralPairing

/-- The normalized neutral pairing on the primal/dual doubled carrier. -/
def neutralKreinPairing (X Y : Doubled R V) : R :=
  (2 : R)⁻¹ * eta X Y

theorem neutralKreinPairing_symm (X Y : Doubled R V) :
    neutralKreinPairing X Y = neutralKreinPairing Y X := by
  simp [neutralKreinPairing, eta, add_comm]

theorem neutralKreinPairing_left_isotropic (v w : V) :
    neutralKreinPairing (R := R) (v, 0) (w, 0) = 0 := by
  change (2 : R)⁻¹ * ((0 : R) + 0) = 0
  exact Eq.trans
    (congrArg (fun x : R => (2 : R)⁻¹ * x) (add_zero (0 : R)))
    (mul_zero _)

theorem neutralKreinPairing_right_isotropic (α β : Dual R V) :
    neutralKreinPairing (R := R) (0, α) (0, β) = 0 := by
  simp [neutralKreinPairing, eta, evaluation]

def legendreGraphLift
    (L : V → Dual R V) (v : V) : Doubled R V :=
  (v, L v)

theorem neutralKreinPairing_graph
    (L : V → Dual R V) (u v : V) :
    neutralKreinPairing
        (legendreGraphLift L u) (legendreGraphLift L v) =
      (2 : R)⁻¹ * ((L u) v + (L v) u) := by
  simp [neutralKreinPairing, eta, evaluation, legendreGraphLift]

theorem omega_graph_eq_zero_of_symmetric
    (L : V → Dual R V)
    (hL : ∀ u v : V, (L u) v = (L v) u)
    (u v : V) :
    omega
        (legendreGraphLift L u)
        (legendreGraphLift L v) = 0 := by
  simp [omega, evaluation, legendreGraphLift, hL u v]

end NeutralPairing

end InfoGeometry.Canonical.DoubledChiralPairing
