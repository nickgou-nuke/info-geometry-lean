import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

noncomputable section
variable {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
abbrev CuntzAlg (R ι : Type*) [CommSemiring R] := TensorAlgebra R (ι →₀ R)
def T₀ (i : ι) : CuntzAlg R ι := TensorAlgebra.ι R (Finsupp.single i 1)
def T (i : ι) : CuntzAlg R ι := T₀ i

#check T (R := R)
