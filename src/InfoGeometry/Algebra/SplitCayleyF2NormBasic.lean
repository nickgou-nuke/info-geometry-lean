import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Basic norm identities for the split Cayley carrier

These are definition-level identities used by the structural composition
layer.  They are kept separate from the finite verification owner.
-/

namespace InfoGeometry.Algebra.SplitCayleyF2

@[simp] theorem norm_zero_basic : norm (zero : Cayley) = 0 := by
  simp [norm, zero, dot]

@[simp] theorem norm_one_basic : norm (one : Cayley) = 1 := by
  simp [norm, one, dot]

end InfoGeometry.Algebra.SplitCayleyF2
