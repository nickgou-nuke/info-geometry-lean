import Mathlib

/-!
# Operator-valued super-Poincare charges

Central charges are elements of the operator algebra, not scalars. This file
proves only algebraic operator lemmas in a noncommutative ring.
-/

namespace InfoGeometry.Physics.SuperPoincareOperatorCharges

/-- Operator commutator. -/
def comm {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

/-- Operator anticommutator. -/
def anti {A : Type*} [Ring A] (x y : A) : A := x * y + y * x

@[simp] theorem comm_eq_zero_of_commutes {A : Type*} [Ring A] {z x : A}
    (h : z * x = x * z) : comm z x = 0 := by
  simp [comm, h]

@[simp] theorem comm_self {A : Type*} [Ring A] (x : A) : comm x x = 0 := by
  simp [comm]

@[simp] theorem anti_comm {A : Type*} [Ring A] (x y : A) : anti x y = anti y x := by
  simp [anti, add_comm]

/-- If the operator-valued central charge `Z` commutes with every operator, its
commutator with any momentum operator vanishes. -/
theorem central_charge_commutes_with_momentum {A : Type*} [Ring A]
    {Z : A} (hZ : ∀ x : A, Z * x = x * Z) (Pμ : A) :
    comm Z Pμ = 0 := by
  exact comm_eq_zero_of_commutes (hZ Pμ)

/-- If the operator-valued central charge `Z` commutes with every operator, its
commutator with any Lorentz generator vanishes. -/
theorem central_charge_commutes_with_lorentz {A : Type*} [Ring A]
    {Z : A} (hZ : ∀ x : A, Z * x = x * Z) (Mμν : A) :
    comm Z Mμν = 0 := by
  exact comm_eq_zero_of_commutes (hZ Mμν)

/-- If the operator-valued central charge `Z` commutes with every operator, its
commutator with any supercharge vanishes. -/
theorem central_charge_commutes_with_supercharge {A : Type*} [Ring A]
    {Z : A} (hZ : ∀ x : A, Z * x = x * Z) (Q : A) :
    comm Z Q = 0 := by
  exact comm_eq_zero_of_commutes (hZ Q)

/-- The chiral Dirac operator `Dχ = Q₊ + Q₋` squares to the mixed
anticommutator when both chiral supercharges are nilpotent. -/
theorem chiral_dirac_square_eq_momentum_operator {A : Type*} [Ring A]
    {Qplus Qminus : A}
    (hplus : Qplus * Qplus = 0)
    (hminus : Qminus * Qminus = 0) :
    (Qplus + Qminus) * (Qplus + Qminus) = anti Qplus Qminus := by
  simp [anti, left_distrib, right_distrib, hplus, hminus]
  abel

/-- If the mixed anticommutator is the momentum operator, then `Dχ²=P`. -/
theorem chiral_dirac_square_eq_given_momentum {A : Type*} [Ring A]
    {Qplus Qminus P : A}
    (hplus : Qplus * Qplus = 0)
    (hminus : Qminus * Qminus = 0)
    (hP : anti Qplus Qminus = P) :
    (Qplus + Qminus) * (Qplus + Qminus) = P := by
  rw [chiral_dirac_square_eq_momentum_operator hplus hminus, hP]

/-- Operator-valued extended SUSY central charge relation. If `{Qᵢ,Qⱼ}=Zᵢⱼ`
and `Zᵢⱼ` is central as an operator, then its commutator with every observable
vanishes. -/
theorem operator_central_charge_from_anticommutator {A : Type*} [Ring A]
    {Qi Qj Zij : A}
    (hAnti : anti Qi Qj = Zij)
    (hZ : ∀ x : A, Zij * x = x * Zij) (X : A) :
    anti Qi Qj = Zij ∧ comm Zij X = 0 := by
  exact ⟨hAnti, comm_eq_zero_of_commutes (hZ X)⟩

/-- The operator-valued central charge commutes with the anticommutator that defines it. -/
theorem central_charge_commutes_with_defining_anticommutator {A : Type*} [Ring A]
    {Qi Qj Zij : A}
    (hAnti : anti Qi Qj = Zij)
    (hZ : ∀ x : A, Zij * x = x * Zij) :
    comm Zij (anti Qi Qj) = 0 := by
  rw [hAnti]
  exact comm_eq_zero_of_commutes (hZ Zij)

end InfoGeometry.Physics.SuperPoincareOperatorCharges
