import InfoGeometry.Algebra.Zorn.G2GroupOrderReduction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity

/-!
# Internal finite-cardinality boundary for `G₂(2)`

The automorphism carrier is reduced by the existing seven-image equivalence to
the exact admissible-basis subtype.  The remaining theorem is intentionally
kept in this small owner so that its computational cost and kernel boundary
are visible to downstream users.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismInternalCardinality

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn

noncomputable section

def Nilpotent := {x : SplitOctF2 // mul x x = zero}

noncomputable instance nilpotentFintype : Fintype Nilpotent := by
  exact Fintype.subtype (Finset.univ.filter (fun x => mul x x = zero)) (by
    intro x
    simp)

abbrev GeneratorTuple := Nilpotent × Nilpotent × Nilpotent × Nilpotent

def tupleBasis (q : GeneratorTuple) : Fin 7 → SplitOctF2 :=
  let a := q.1.1
  let c := q.2.1.1
  let b := q.2.2.1.1
  let d := q.2.2.2.1
  ![mul a c, a, b, mul c d, c, d, mul a b]

def admissibleGeneratorTuple (q : GeneratorTuple) : Prop :=
  admissibleBasis7 (tupleBasis q)

/-! This is intentionally only a reduction interface.  We do not install a
noncomputable subtype enumeration here: that would recreate the memory-heavy
full search this owner is designed to avoid. -/

end
end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismInternalCardinality
