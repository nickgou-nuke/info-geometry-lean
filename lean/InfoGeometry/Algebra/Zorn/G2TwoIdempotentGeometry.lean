import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import Mathlib.Tactic

/-!
# Structural idempotent lemmas for the finite split-Zorn carrier

This file proves the coordinate characterization and exact counting of trace-one idempotents.
It proves that there are exactly 72 trace-one idempotents in the split octonions over 𝔽₂,
partitioned into two diagonal sectors of 36 elements each.
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
            cross0, cross1, cross2, Bool.xor_assoc,
            Bool.xor_comm] at htrace ⊢ <;>
          intro hdot <;> simp [Bool.and_comm, hdot]

instance : DecidablePred (fun X : SplitOctF2 => mul X X = X ∧ zornTrace X = true) :=
  fun _ => inferInstance

instance : DecidablePred (fun X : SplitOctF2 => mul X X = X ∧ X.a = true ∧ X.b = false) :=
  fun _ => inferInstance

instance : DecidablePred (fun X : SplitOctF2 => mul X X = X ∧ X.a = false ∧ X.b = true) :=
  fun _ => inferInstance

/-- 🏆 THEOREM 1: Exactly 36 primitive idempotents with diagonal (1, 0). -/
theorem idempotents_one_zero_card_eq_36 :
    Fintype.card {X : SplitOctF2 // mul X X = X ∧ X.a = true ∧ X.b = false} = 36 := by
  decide

/-- 🏆 THEOREM 2: Exactly 36 primitive idempotents with diagonal (0, 1). -/
theorem idempotents_zero_one_card_eq_36 :
    Fintype.card {X : SplitOctF2 // mul X X = X ∧ X.a = false ∧ X.b = true} = 36 := by
  decide

/-- 🏆 THEOREM 3: Total 72 trace-one idempotents in the split octonions over 𝔽₂. -/
theorem trace_one_idempotents_card_eq_72 :
    Fintype.card {X : SplitOctF2 // mul X X = X ∧ zornTrace X = true} = 72 := by
  decide

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
