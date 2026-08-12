import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Data.Complex.Basic

/-!
# Finite TKK grading data

This owner records only the native finite algebraic data that is actually
available here: five Lie-subalgebra slots and selected elements of the
degree-zero slot.  It does not identify arbitrary subalgebras with physical
SU(2)/SU(3) factors, and it does not claim a Cartan involution or a
commutation relation without the corresponding hypotheses and constructions.
Those representation-theoretic bridges belong in separate owners.
-/

namespace TKK_StandardModel

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- The five Lie-subalgebra slots of a finite TKK grading. -/
structure TKKGrading where
  g_minus_2 : LieSubalgebra ℂ L
  g_minus_1 : LieSubalgebra ℂ L
  g_0       : LieSubalgebra ℂ L
  g_1       : LieSubalgebra ℂ L
  g_2       : LieSubalgebra ℂ L

variable (tkk : TKKGrading (L := L))

/-- A chosen degree-zero element, with its membership proof retained. -/
structure DegreeZeroElement (tkk : TKKGrading (L := L)) where
  value : tkk.g_0

/-- A chosen degree-zero subalgebra and one of its elements. -/
structure DegreeZeroSubalgebraElement (tkk : TKKGrading (L := L)) where
  carrier : LieSubalgebra ℂ tkk.g_0
  value : carrier

end TKK_StandardModel
