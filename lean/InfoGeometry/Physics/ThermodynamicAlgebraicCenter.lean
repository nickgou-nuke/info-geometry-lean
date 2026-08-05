import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Basic

namespace InfoGeometry.Physics

variable (A : Type*) [Ring A]

/-- The algebraic center of a ring, defined as the elements commuting with every
element of the ambient ring. -/
def ThermodynamicCenter : Set A :=
  {z : A | ∀ x : A, z * x = x * z}

/-- The commutant of a set of ring elements. -/
def Commutant (S : Set A) : Set A :=
  {y : A | ∀ s ∈ S, y * s = s * y}

theorem center_contains_vacuum_background :
    (1 : A) ∈ ThermodynamicCenter A := by
  dsimp [ThermodynamicCenter]
  intro x
  rw [one_mul, mul_one]

theorem center_closed_under_multiplication (z1 z2 : A)
    (hz1 : z1 ∈ ThermodynamicCenter A)
    (hz2 : z2 ∈ ThermodynamicCenter A) :
    z1 * z2 ∈ ThermodynamicCenter A := by
  dsimp [ThermodynamicCenter] at *
  intro x
  rw [mul_assoc, hz2 x, ← mul_assoc, hz1 x, mul_assoc]

theorem double_commutant_emergence (S : Set A) :
    S ⊆ Commutant A (Commutant A S) := by
  intro s hs
  dsimp [Commutant]
  intro y hy
  exact (hy s hs).symm

theorem center_is_global_commutant :
    ThermodynamicCenter A = Commutant A (Set.univ : Set A) := by
  ext z
  dsimp [ThermodynamicCenter, Commutant]
  constructor
  · intro h s _
    exact h s
  · intro h x
    exact h x (Set.mem_univ x)

theorem thermodynamic_center_synthesis (z1 z2 : A)
    (hz1 : z1 ∈ ThermodynamicCenter A)
    (hz2 : z2 ∈ ThermodynamicCenter A) :
    ((1 : A) ∈ ThermodynamicCenter A) ∧
    (z1 * z2 ∈ ThermodynamicCenter A) ∧
    (∀ S : Set A, S ⊆ Commutant A (Commutant A S)) ∧
    (ThermodynamicCenter A = Commutant A (Set.univ : Set A)) :=
  ⟨center_contains_vacuum_background A,
    center_closed_under_multiplication A z1 z2 hz1 hz2,
    double_commutant_emergence A,
    center_is_global_commutant A⟩

end InfoGeometry.Physics
