import InfoGeometry.OperatorAlgebra.TKKClosure
import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.Physics.ZornTkkAnomalyCancellation

/-!
# InfoGeometry.Physics.ZornTkkHypothesisDistillation

This file distills the overclaimed Zorn/TKK narrative into theorem-honest
mathematical packets already supported by the repository.

The concrete owner-supported content is:

* the raw split-octonion commutator is not Lie on the full carrier;
* selected cleared Jordan-triple readbacks close on named concrete sectors;
* the concrete `e⁺/e⁻` commutator packet remains exactly zero.

The abstract TKK route is recorded only as an explicit property packet over a
Jordan triple system and its Lie closure boundary.
-/

noncomputable section

namespace InfoGeometry.Physics.ZornTkkHypothesisDistillation

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation
open InfoGeometry.Physics.ZornTkkAnomalyCancellation

/-- The full raw split-octonion commutator is not a Lie bracket on the owner
carrier: the concrete Jacobiator on `(up₀, up₁, down₀)` is nonzero. -/
theorem raw_commutator_not_lie :
    jacobiatorZ up0 up1 down0 ≠ zeroZ :=
  jacobiator_up0_up1_down0_ne_zero

/-- Concrete cleared Jordan-triple readbacks that survive as theorem-honest
finite packets on named Zorn basis vectors. -/
theorem concrete_doubleJordan_packet :
    doubleJordanTriple up0 down0 up0 = ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ ∧
      doubleJordanTriple up0 down0 up1 = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ ∧
      doubleJordanTriple up1 down1 up2 = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · exact doubleJordan_up0_down0_up0_eq
  · exact doubleJordan_up0_down0_up1_eq
  · exact doubleJordan_up1_down1_up2_eq

/-- Honest concrete `e⁺/e⁻` packet: exact cancellation, pure-bosonic readback,
and vanishing trace/determinant. -/
theorem concrete_ePlus_eMinus_packet :
    lieBracket ePlus eMinus = zeroZ ∧
      IsPureBosonic (lieBracket ePlus eMinus) ∧
      trZ (lieBracket ePlus eMinus) = 0 ∧
      detZ (lieBracket ePlus eMinus) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lieBracket_ePlus_eMinus
  · exact tkk_e_plus_minus_anomaly_cancellation
  · exact tkk_commutator_trace_evaluation
  · exact tkk_commutator_det_evaluation

/-- Finite concrete boundary packet: the raw full commutator is not Lie, while
the surviving theorem-honest Zorn data are the named doubled-Jordan readbacks
and the exact `e⁺/e⁻` cancellation packet. -/
theorem concrete_boundary_packet :
    jacobiatorZ up0 up1 down0 ≠ zeroZ ∧
      (doubleJordanTriple up0 down0 up0 = ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ ∧
        doubleJordanTriple up0 down0 up1 = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ ∧
        doubleJordanTriple up1 down1 up2 = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩) ∧
      (lieBracket ePlus eMinus = zeroZ ∧
        IsPureBosonic (lieBracket ePlus eMinus) ∧
        trZ (lieBracket ePlus eMinus) = 0 ∧
        detZ (lieBracket ePlus eMinus) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact raw_commutator_not_lie
  · exact concrete_doubleJordan_packet
  · exact concrete_ePlus_eMinus_packet

/-- The abstract TKK route is legitimate only after supplying a concrete
`TKKLieClosure` property, which already packages the Jordan triple data together
with its 3-graded Lie closure. -/
structure JordanTripleTKKClosureHypotheses
    (J : Type*) [AddCommGroup J] [Module ℝ J] where
  L : Type*
  instAddCommGroup : AddCommGroup L
  instModule : Module ℝ L
  closure : InfoGeometry.OperatorAlgebra.TKKLieClosure J L

attribute [instance] JordanTripleTKKClosureHypotheses.instAddCommGroup
attribute [instance] JordanTripleTKKClosureHypotheses.instModule

namespace JordanTripleTKKClosureHypotheses

variable
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (H : JordanTripleTKKClosureHypotheses J)

/-- Re-export: the negative TKK grade is abelian under the supplied closure
hypotheses. -/
theorem neg_grade_abelian (x y : J) :
    H.closure.lie.bracket (H.closure.neg x) (H.closure.neg y) = 0 :=
  H.closure.bracket_neg_neg x y

/-- Re-export: the positive TKK grade is abelian under the supplied closure
hypotheses. -/
theorem pos_grade_abelian (x y : J) :
    H.closure.lie.bracket (H.closure.pos x) (H.closure.pos y) = 0 :=
  H.closure.bracket_pos_pos x y

/-- Re-export: the cross bracket closes into the grade-zero structure operator
under the supplied closure hypotheses. -/
theorem cross_bracket_closure (x y : J) :
    H.closure.lie.bracket (H.closure.neg x) (H.closure.pos y) =
      H.closure.zero x y :=
  H.closure.bracket_neg_pos x y

/-- Re-export: the opposite cross bracket is the negative of the grade-zero
structure operator under the supplied closure hypotheses. -/
theorem opposite_cross_bracket_closure (x y : J) :
    H.closure.lie.bracket (H.closure.pos y) (H.closure.neg x) =
      -H.closure.zero x y :=
  H.closure.bracket_pos_neg x y

/-- Re-export: grade zero acts on the negative grade by the Jordan triple
product under the supplied closure hypotheses. -/
theorem zero_neg_triple_action (x y z : J) :
    H.closure.lie.bracket (H.closure.zero x y) (H.closure.neg z) =
      H.closure.neg (H.closure.jordan.triple x y z) :=
  H.closure.bracket_zero_neg x y z

/-- Re-export: the opposite negative-grade/structure bracket is the negative of
the induced Jordan triple action under the supplied closure hypotheses. -/
theorem neg_zero_triple_action (x y z : J) :
    H.closure.lie.bracket (H.closure.neg z) (H.closure.zero x y) =
      -H.closure.neg (H.closure.jordan.triple x y z) :=
  H.closure.bracket_neg_zero x y z

/-- Re-export: grade zero acts contragrediently on the positive grade under
the supplied closure hypotheses. -/
theorem zero_pos_triple_action (x y z : J) :
    H.closure.lie.bracket (H.closure.zero x y) (H.closure.pos z) =
      -H.closure.pos (H.closure.jordan.triple y x z) :=
  H.closure.bracket_zero_pos x y z

/-- Re-export: the opposite positive-grade/structure bracket removes the
leading minus sign from the contragredient action under the supplied closure
hypotheses. -/
theorem pos_zero_triple_action (x y z : J) :
    H.closure.lie.bracket (H.closure.pos z) (H.closure.zero x y) =
      H.closure.pos (H.closure.jordan.triple y x z) :=
  H.closure.bracket_pos_zero x y z

/-- Small theorem-safe packet collecting the basic bracket identities carried by
the supplied `TKKLieClosure` property. -/
theorem basic_closure_consequences (x y z : J) :
    H.closure.lie.bracket (H.closure.neg x) (H.closure.neg y) = 0 ∧
      H.closure.lie.bracket (H.closure.pos x) (H.closure.pos y) = 0 ∧
      H.closure.lie.bracket (H.closure.neg x) (H.closure.pos y) = H.closure.zero x y ∧
      H.closure.lie.bracket (H.closure.pos y) (H.closure.neg x) = -H.closure.zero x y ∧
      H.closure.lie.bracket (H.closure.zero x y) (H.closure.neg z) =
        H.closure.neg (H.closure.jordan.triple x y z) ∧
      H.closure.lie.bracket (H.closure.neg z) (H.closure.zero x y) =
        -H.closure.neg (H.closure.jordan.triple x y z) ∧
      H.closure.lie.bracket (H.closure.zero x y) (H.closure.pos z) =
        -H.closure.pos (H.closure.jordan.triple y x z) ∧
      H.closure.lie.bracket (H.closure.pos z) (H.closure.zero x y) =
        H.closure.pos (H.closure.jordan.triple y x z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact H.neg_grade_abelian x y
  · exact H.pos_grade_abelian x y
  · exact H.cross_bracket_closure x y
  · exact H.opposite_cross_bracket_closure x y
  · exact H.zero_neg_triple_action x y z
  · exact H.neg_zero_triple_action x y z
  · exact H.zero_pos_triple_action x y z
  · exact H.pos_zero_triple_action x y z

end JordanTripleTKKClosureHypotheses

end InfoGeometry.Physics.ZornTkkHypothesisDistillation
