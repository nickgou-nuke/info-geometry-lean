import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Structural idempotent lemmas for the finite split-Zorn carrier

This file proves the coordinate characterization of trace-one idempotents.
It does not identify their orbit with `SplitOctF2Aut` and does not make a
cardinality claim about that automorphism group.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def zornTrace (X : SplitOctF2) : Bool :=
  add2 X.a X.b

def zornVectorPairing (X : SplitOctF2) : Bool :=
  dot3 X.x0 X.x1 X.x2 X.y0 X.y1 X.y2

theorem idempotent_implies_zero_vector_pairing (X : SplitOctF2)
    (hX : mul X X = X) :
    zornVectorPairing X = false := by
  have ha := congrArg SplitOctF2.a hX
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
      simp [mul, zornVectorPairing, dot3, mul2, add2] at ha ⊢
      cases a <;> simp at ha ⊢ <;> exact ha

theorem trace_one_idempotent_iff_zero_vector_pairing (X : SplitOctF2)
    (htrace : zornTrace X = true) :
    mul X X = X ↔ zornVectorPairing X = false := by
  constructor
  · intro hX
    exact idempotent_implies_zero_vector_pairing X hX
  · cases X with
    | mk a b x0 x1 x2 y0 y1 y2 =>
        cases a <;> cases b <;>
          simp [zornTrace, zornVectorPairing, mul, dot3, mul2, add2,
            cross0, cross1, cross2, Bool.xor_comm] at htrace ⊢ <;>
          intro hdot <;> simp [Bool.and_comm, hdot]

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
