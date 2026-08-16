import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Data.Complex.Basic

/-!
# Zero-grade Lie-factor interface

This file records only the native Lie-algebra data available at the zero
grade of a five-graded carrier.  It deliberately does not identify arbitrary
subalgebras with `su(2)` or `su(3)`: such an identification requires a model
Lie algebra and a proved Lie equivalence.

The commuting-factor theorem below is therefore parameterized by its actual
bracket hypothesis.  Membership in a common ambient grade is not confused
with commutation.
-/

namespace TKK_StandardModel

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- The five zero-grade-carrier slots used by this compatibility interface. -/
structure TKKGrading where
  g_minus_2 : LieSubalgebra ℂ L
  g_minus_1 : LieSubalgebra ℂ L
  g_0 : LieSubalgebra ℂ L
  g_1 : LieSubalgebra ℂ L
  g_2 : LieSubalgebra ℂ L

variable (tkk : TKKGrading (L := L))

/-- A Lie subalgebra chosen inside the zero-grade carrier. -/
abbrev ZeroGradeLieSubalgebra
    (tkk : TKKGrading (L := L)) := LieSubalgebra ℂ tkk.g_0

/-- A chosen zero-grade element, without a representation-theoretic label. -/
structure ChosenZeroGradeElement where
  carrier : ZeroGradeLieSubalgebra tkk

/-- Two zero-grade factors commute in the ambient Lie algebra. -/
def ZeroGradeFactorsCommute
    (a b : ZeroGradeLieSubalgebra tkk) : Prop :=
  ∀ x : a, ∀ y : b, ⁅(x : L), (y : L)⁆ = 0

/-- The commutation predicate is symmetric by Lie anti-commutativity. -/
theorem zeroGradeFactorsCommute_symm
    {a b : ZeroGradeLieSubalgebra tkk}
    (h : ZeroGradeFactorsCommute tkk a b) :
    ZeroGradeFactorsCommute tkk b a := by
  intro y x
  calc
    ⁅(y : L), (x : L)⁆ = -⁅(x : L), (y : L)⁆ := (lie_skew _ _).symm
    _ = 0 := by rw [h x y, neg_zero]

/-- A factor packet with its actual zero-grade commutation evidence. -/
structure ZeroGradeFactorPacket where
  isospinFactor : ZeroGradeLieSubalgebra tkk
  colorFactor : ZeroGradeLieSubalgebra tkk
  commute : ZeroGradeFactorsCommute tkk isospinFactor colorFactor

/-- The packet commutation theorem in the ambient TKK carrier. -/
theorem zeroGradeFactorPacket_bracket_eq_zero
    (P : ZeroGradeFactorPacket tkk)
    (x : P.colorFactor) (y : P.isospinFactor) :
    ⁅(x : L), (y : L)⁆ = 0 := by
  exact zeroGradeFactorsCommute_symm tkk P.commute x y

/-- A selected Cartan element is only a chosen element at this layer. -/
structure ChosenZeroGradeCartan where
  factor : ZeroGradeLieSubalgebra tkk
  element : factor

/-- The grade-zero carrier is closed under its native Lie bracket. -/
theorem zeroGrade_lie_closed
    (tkk : TKKGrading (L := L))
    {x y : tkk.g_0} :
    ⁅(x : L), (y : L)⁆ ∈ tkk.g_0 := by
  exact tkk.g_0.lie_mem x.property y.property

end TKK_StandardModel
