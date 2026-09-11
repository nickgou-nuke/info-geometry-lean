import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

namespace InfoGeometry.Physics.ZornTkkAlgebraicClosure


variable {A : Type*} [Ring A]

/-- Jordan triple on an associative ring. -/
def jordanTriple (x y z : A) : A := x * y * z + z * y * x

@[simp] theorem jordanTriple_outer_symm (x y z : A) :
    jordanTriple x y z = jordanTriple z y x := by
  simp [jordanTriple, mul_assoc, add_comm]

/-- Jordan triple identity in an associative ring. -/
theorem jordanTriple_identity (a b x y z : A) :
    jordanTriple a b (jordanTriple x y z)
      - jordanTriple (jordanTriple a b x) y z
      + jordanTriple x (jordanTriple b a y) z
      - jordanTriple x y (jordanTriple a b z) = 0 := by
  unfold jordanTriple
  noncomm_ring

/-- Associative-ring commutator. -/
def commutator (x y : A) : A := x * y - y * x

@[simp] theorem commutator_def (x y : A) : commutator x y = x * y - y * x := rfl

/-- Jacobi identity for the commutator Lie bracket. -/
theorem commutator_jacobi (X Y Z : A) :
    commutator X (commutator Y Z) +
      commutator Y (commutator Z X) +
      commutator Z (commutator X Y) = 0 := by
  simpa [commutator, Ring.lie_def] using (lie_jacobi (x := X) (y := Y) (z := Z))

/-- The mathlib Lie bracket on an associative ring is the commutator. -/
theorem lieBracket_eq_commutator (X Y : A) :
    ⁅X, Y⁆ = commutator X Y := by
  simp [commutator, Ring.lie_def]


/-- Owner-backed associative-ring packet. -/
theorem associativeRing_bridge_packet (a b x y z : A) :
    jordanTriple a b (jordanTriple x y z)
      - jordanTriple (jordanTriple a b x) y z
      + jordanTriple x (jordanTriple b a y) z
      - jordanTriple x y (jordanTriple a b z) = 0 ∧
    ⁅a, ⁅b, x⁆⁆ + ⁅b, ⁅x, a⁆⁆ + ⁅x, ⁅a, b⁆⁆ = 0 := by
  exact ⟨jordanTriple_identity a b x y z, by
    simpa [Ring.lie_def] using (commutator_jacobi a b x)⟩

end InfoGeometry.Physics.ZornTkkAlgebraicClosure
