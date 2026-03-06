import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

abbrev DoubledSpace (E : Type) := E × E

noncomputable section

example : IsTopologicalRing (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  inferInstance
