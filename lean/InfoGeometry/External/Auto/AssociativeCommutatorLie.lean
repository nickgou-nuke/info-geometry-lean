import Mathlib.Tactic

noncomputable section

namespace AssociativeCommutatorLie

/-- Commutator in an associative ring. -/
def comm {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

/-- Anticommutator in an associative ring. -/
def anti {A : Type*} [Ring A] (x y : A) : A := x * y + y * x

@[simp] theorem comm_self {A : Type*} [Ring A] (x : A) : comm x x = 0 := by
  simp [comm]

@[simp] theorem comm_swap {A : Type*} [Ring A] (x y : A) :
    comm x y = - comm y x := by
  simp [comm]

/-- The associative commutator satisfies the Jacobi identity. -/
theorem comm_jacobi {A : Type*} [Ring A] (x y z : A) :
    comm x (comm y z) + comm y (comm z x) + comm z (comm x y) = 0 := by
  simp [comm]
  noncomm_ring

/-- The commutator is a derivation in the right argument. -/
theorem comm_mul_right {A : Type*} [Ring A] (x y z : A) :
    comm x (y * z) = comm x y * z + y * comm x z := by
  simp [comm]
  noncomm_ring

/-- The commutator is a derivation in the left argument. -/
theorem comm_mul_left {A : Type*} [Ring A] (x y z : A) :
    comm (x * y) z = x * comm y z + comm x z * y := by
  simp [comm]
  noncomm_ring

/-- If an operator commutes with all elements, its commutator with every element vanishes. -/
theorem comm_eq_zero_of_forall_commutes {A : Type*} [Ring A] {Z : A}
    (hZ : ∀ x : A, Z * x = x * Z) (x : A) :
    comm Z x = 0 := by
  simp [comm, hZ x]

/-- If `Z` is central, commutation is preserved after multiplying by `Z` on the left. -/
theorem central_mul_comm {A : Type*} [Ring A] {Z : A}
    (hZ : ∀ x : A, Z * x = x * Z) (x y : A) :
    comm (Z * x) y = Z * comm x y := by
  simp [comm]
  have hy : y * (Z * x) = Z * (y * x) := by
    rw [← mul_assoc, ← hZ y, mul_assoc]
  rw [hy]
  noncomm_ring

/-- If `Z` is central, commutation is preserved after multiplying by `Z` on the right. -/
theorem mul_central_comm {A : Type*} [Ring A] {Z : A}
    (hZ : ∀ x : A, Z * x = x * Z) (x y : A) :
    comm (x * Z) y = Z * comm x y := by
  rw [← hZ x]
  exact central_mul_comm hZ x y

/-- Mixed nilpotent supercharges: the square of `Q₊+Q₋` is their anticommutator. -/
theorem square_add_of_square_zero {A : Type*} [Ring A] {Qplus Qminus : A}
    (hplus : Qplus * Qplus = 0) (hminus : Qminus * Qminus = 0) :
    (Qplus + Qminus) * (Qplus + Qminus) = anti Qplus Qminus := by
  simp [anti, left_distrib, right_distrib, hplus, hminus]
  abel

#check comm_jacobi
#check comm_mul_right
#check comm_mul_left
#check central_mul_comm
#check mul_central_comm
#check square_add_of_square_zero

end AssociativeCommutatorLie
