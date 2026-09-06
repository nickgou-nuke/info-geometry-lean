import proofs.SplitOctonionJordanCore
import proofs.SplitOctonionJordanForm

/-!
# Jordan structure operators of the canonical split-octonion carrier

This file owns the symmetrized product on the complete eight-dimensional
canonical Zorn carrier.  It proves the Jordan identity by coordinates and
defines the left, inner, and quadratic structure operators used by a later
orthogonally constrained TKK construction.

No identification with `so(4,4) ⊕ ℝ` or `so(5,5)` is asserted here: those
claims require a finite-dimensional structure-algebra subspace, its
orthogonality equation, and dimension/isomorphism proofs.
-/

noncomputable section

namespace SplitOctonionJordanStructure

set_option maxHeartbeats 2000000

open SplitOctonionChiralClosure
open SplitOctonionBraidSU3

abbrev Zorn := SplitOctonionChiralClosure.Zorn

/-- The normalized Jordan product on the full split-octonion carrier. -/
def jordan (X Y : Zorn) : Zorn :=
  SplitOctonionJordanCore.jordanMul X Y

/-- Left Jordan multiplication, retained as an explicitly evaluable operator. -/
def leftJordan (X : Zorn) : Zorn → Zorn := fun Y => jordan X Y

/-- The inner structure operator `[L_X,L_Y]`. -/
def innerStructure (X Y : Zorn) : Zorn → Zorn := fun Z =>
  sub (leftJordan X (leftJordan Y Z))
    (leftJordan Y (leftJordan X Z))

/-- Quadratic representation `U_X Y = 2 X∘(X∘Y) - X²∘Y`. -/
def quadraticRepresentation (X : Zorn) : Zorn → Zorn := fun Y =>
  sub (smul 2 (jordan X (jordan X Y))) (jordan (jordan X X) Y)

/-- Standard Jordan triple product expressed through left multiplication. -/
def jordanTriple (X Y Z : Zorn) : Zorn :=
  add (sub (jordan X (jordan Y Z)) (jordan Y (jordan X Z)))
    (jordan Z (jordan Y X))

macro "full_jordan_coords" : tactic =>
  `(tactic| (apply SplitOctonionBraidSU3.zorn_ext <;>
    simp [jordan, leftJordan, innerStructure, quadraticRepresentation,
      jordanTriple, SplitOctonionJordanCore.jordanMul,
      SplitOctonionChiralClosure.mul,
      SplitOctonionChiralClosure.add, SplitOctonionChiralClosure.sub,
      SplitOctonionChiralClosure.smul, SplitOctonionChiralClosure.antiComm,
      SplitOctonionChiralClosure.one, SplitOctonionChiralClosure.zero,
      zornMul, zornAdd, zornSub, zornSmul, dot3, cross3] <;>
    try funext i <;> try fin_cases i <;> simp [cross3, dot3] <;> ring <;> abel))

theorem jordan_comm (X Y : Zorn) : jordan X Y = jordan Y X := by
  full_jordan_coords <;> ring

/-- The unit of the raw Zorn algebra is also the Jordan unit. -/
theorem jordan_one_left (X : Zorn) : jordan one X = X := by
  full_jordan_coords <;> ring

theorem jordan_one_right (X : Zorn) : jordan X one = X := by
  rw [jordan_comm, jordan_one_left]

/-- Full Jordan identity on arbitrary canonical split octonions. -/
theorem jordan_identity (X Y : Zorn) :
    jordan (jordan X X) (jordan X Y) =
      jordan X (jordan (jordan X X) Y) := by
  exact SplitOctonionJordanCore.jordan_identity_from_spin_coordinates X Y

/-- Commutation of `L_X` with `L_{X²}`, the operator form of the identity. -/
theorem leftJordan_square_commutes (X Y : Zorn) :
    innerStructure X (jordan X X) Y = zero := by
  rw [show innerStructure X (jordan X X) Y =
      sub (jordan X (jordan (jordan X X) Y))
        (jordan (jordan X X) (jordan X Y)) from rfl]
  rw [← jordan_identity]
  full_jordan_coords

/-- The Jordan triple is symmetric in its outer variables. -/
theorem jordanTriple_outer_symm (X Y Z : Zorn) :
    jordanTriple X Y Z = jordanTriple Z Y X := by
  have hXZ : jordan X Z = jordan Z X := jordan_comm X Z
  unfold jordanTriple
  rw [hXZ]
  apply SplitOctonionBraidSU3.zorn_ext <;>
    simp [jordanTriple, SplitOctonionChiralClosure.add,
      SplitOctonionChiralClosure.sub, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSub] <;>
    try funext i
  all_goals ring

/-- The concrete real split quadratic carrier reused by the future
orthogonal structure-algebra identification. -/
abbrev RealSplit44 := SplitOctonionJordanForm.RealJordan
abbrev realQuadratic44 := SplitOctonionJordanForm.quadratic44

/-- Arithmetic expected of the eventual constrained TKK decomposition.  This
is only a dimension target, not a dimension theorem for a Lie subalgebra. -/
theorem tkk55_dimension_target : 8 + 29 + 8 = 45 := by norm_num

theorem split_octonion_jordan_structure_synthesis (X Y Z : Zorn) :
    jordan X Y = jordan Y X ∧
    jordan one X = X ∧
    jordan (jordan X X) (jordan X Y) =
      jordan X (jordan (jordan X X) Y) ∧
    innerStructure X (jordan X X) Y = zero ∧
    jordanTriple X Y Z = jordanTriple Z Y X := by
  exact ⟨jordan_comm X Y, jordan_one_left X, jordan_identity X Y,
    leftJordan_square_commutes X Y, jordanTriple_outer_symm X Y Z⟩

end SplitOctonionJordanStructure

end noncomputable section
