import InfoGeometry.Categorical.FibonacciBraidedCategory

noncomputable section

namespace InfoGeometry.Categorical.FibonacciGlobalChannelBasis

open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace

abbrev FibObject := InfoGeometry.Categorical.FibonacciHomSpace.FibCat

/-!
# Explicit τ-output channel indices

These finite sum types record the three fusion-channel summands in the
τ-output of the two parenthesizations.  They are only a basis index layer;
no fusion-tree ordering or associator is chosen here.
-/

abbrev LeftTauChannelIndex (X Y Z : FibObject) : Type :=
  Sum
    (Fin ((X FibSimple.unit * Y FibSimple.unit +
      X FibSimple.tau * Y FibSimple.tau) * Z FibSimple.tau))
    (Sum
      (Fin ((X FibSimple.unit * Y FibSimple.tau +
        X FibSimple.tau * Y FibSimple.unit +
        X FibSimple.tau * Y FibSimple.tau) * Z FibSimple.unit))
      (Fin ((X FibSimple.unit * Y FibSimple.tau +
        X FibSimple.tau * Y FibSimple.unit +
        X FibSimple.tau * Y FibSimple.tau) * Z FibSimple.tau)))

abbrev RightTauChannelIndex (X Y Z : FibObject) : Type :=
  Sum
    (Fin (X FibSimple.unit *
      (Y FibSimple.unit * Z FibSimple.tau +
        Y FibSimple.tau * Z FibSimple.unit +
        Y FibSimple.tau * Z FibSimple.tau)))
    (Sum
      (Fin (X FibSimple.tau *
        (Y FibSimple.unit * Z FibSimple.unit +
          Y FibSimple.tau * Z FibSimple.tau)))
      (Fin (X FibSimple.tau *
        (Y FibSimple.unit * Z FibSimple.tau +
          Y FibSimple.tau * Z FibSimple.unit +
          Y FibSimple.tau * Z FibSimple.tau))))

/-! The fully refined eight-path indices.  In particular, the two final
`Fin (xτ * yτ * zτ)` summands are kept distinct. -/

abbrev LeftTauFusionPathIndex (X Y Z : FibObject) : Type :=
  Sum (Fin (X FibSimple.unit * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.tau))
         (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))))))))

abbrev RightTauFusionPathIndex (X Y Z : FibObject) : Type :=
  Sum (Fin (X FibSimple.unit * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.unit))
         (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))))))))

theorem leftTauFusionPathIndex_card (X Y Z : FibObject) :
    Fintype.card (LeftTauFusionPathIndex X Y Z) =
      (fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau := by
  simp [LeftTauFusionPathIndex, fibTensorObj]
  <;> ring

theorem rightTauFusionPathIndex_card (X Y Z : FibObject) :
    Fintype.card (RightTauFusionPathIndex X Y Z) =
      (fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau := by
  simp [RightTauFusionPathIndex, fibTensorObj]
  <;> ring

theorem leftTauFusionPathIndex_card_eq_right
    (X Y Z : FibObject) :
    Fintype.card (LeftTauFusionPathIndex X Y Z) =
      Fintype.card (RightTauFusionPathIndex X Y Z) := by
  rw [leftTauFusionPathIndex_card, rightTauFusionPathIndex_card]
  simpa [fibTensorObj] using
    congrArg (fun W : FibObject => W FibSimple.tau)
      (fibTensorObj_assoc X Y Z)

noncomputable def leftTauFusionPathEquivRight
    (X Y Z : FibObject) :
    LeftTauFusionPathIndex X Y Z ≃ RightTauFusionPathIndex X Y Z :=
  (Fintype.equivFin (LeftTauFusionPathIndex X Y Z)).trans
    ((Equiv.cast (congrArg Fin
      (leftTauFusionPathIndex_card_eq_right X Y Z))).trans
      (Fintype.equivFin (RightTauFusionPathIndex X Y Z)).symm)

/-! Selectors for the two repeated `τ ⊗ τ ⊗ τ` paths. -/

abbrev TauTripleMultiplicity (X Y Z : FibObject) : ℕ :=
  X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau

def leftTauFInputOne (X Y Z : FibObject) (i : Fin (TauTripleMultiplicity X Y Z)) :
    LeftTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inl i)

def leftTauFInputTwo (X Y Z : FibObject) (i : Fin (TauTripleMultiplicity X Y Z)) :
    LeftTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr i))))))

def rightTauFOutputOne (X Y Z : FibObject) (i : Fin (TauTripleMultiplicity X Y Z)) :
    RightTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))

def rightTauFOutputTwo (X Y Z : FibObject) (i : Fin (TauTripleMultiplicity X Y Z)) :
    RightTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr i))))))

@[simp] theorem leftTauFInputOne_injective
    (X Y Z : FibObject) :
    Function.Injective (leftTauFInputOne X Y Z) := by
  intro i j h
  exact Sum.inl.inj (Sum.inr.inj h)

@[simp] theorem leftTauFInputTwo_injective
    (X Y Z : FibObject) :
    Function.Injective (leftTauFInputTwo X Y Z) := by
  intro i j h
  repeat' first | apply Sum.inr.inj | apply Sum.inl.inj
  exact h

@[simp] theorem rightTauFOutputOne_injective
    (X Y Z : FibObject) :
    Function.Injective (rightTauFOutputOne X Y Z) := by
  intro i j h
  repeat' first | apply Sum.inr.inj | apply Sum.inl.inj
  exact h

@[simp] theorem rightTauFOutputTwo_injective
    (X Y Z : FibObject) :
    Function.Injective (rightTauFOutputTwo X Y Z) := by
  intro i j h
  repeat' first | apply Sum.inr.inj | apply Sum.inl.inj
  exact h

theorem leftTauChannelIndex_card (X Y Z : FibObject) :
    Fintype.card (LeftTauChannelIndex X Y Z) =
      (fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau := by
  simp [LeftTauChannelIndex, fibTensorObj]
  <;> ring

theorem rightTauChannelIndex_card (X Y Z : FibObject) :
    Fintype.card (RightTauChannelIndex X Y Z) =
      (fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau := by
  simp [RightTauChannelIndex, fibTensorObj]
  <;> ring

theorem leftTauChannelIndex_card_eq_right
    (X Y Z : FibObject) :
    Fintype.card (LeftTauChannelIndex X Y Z) =
      Fintype.card (RightTauChannelIndex X Y Z) := by
  rw [leftTauChannelIndex_card, rightTauChannelIndex_card]
  simpa [fibTensorObj] using
    congrArg (fun W : FibCat => W FibSimple.tau)
      (fibTensorObj_assoc X Y Z)

noncomputable def leftTauChannelEquivRightTauChannel
    (X Y Z : FibObject) :
    LeftTauChannelIndex X Y Z ≃ RightTauChannelIndex X Y Z :=
  (Fintype.equivFin (LeftTauChannelIndex X Y Z)).trans
    ((Equiv.cast (congrArg Fin (leftTauChannelIndex_card_eq_right X Y Z))).trans
      (Fintype.equivFin (RightTauChannelIndex X Y Z)).symm)

abbrev LeftTauChannelFunctions (X Y Z : FibObject) : Type :=
  LeftTauChannelIndex X Y Z → ℂ

abbrev RightTauChannelFunctions (X Y Z : FibObject) : Type :=
  RightTauChannelIndex X Y Z → ℂ

/-! The induced linear equivalence on channel-valued functions.  This is the
reindexing layer for a future block-preserving `FibHom`; it does not yet
choose the Fibonacci `F`-matrix on the two distinguished channels. -/
noncomputable def leftTauChannelFunctionsEquivRight
    (X Y Z : FibObject) :
    LeftTauChannelFunctions X Y Z ≃ₗ[ℂ]
      RightTauChannelFunctions X Y Z where
  toFun x j := x ((leftTauChannelEquivRightTauChannel X Y Z).symm j)
  invFun y i := y (leftTauChannelEquivRightTauChannel X Y Z i)
  map_add' x y := by
    ext j
    rfl
  map_smul' c x := by
    ext j
    rfl
  left_inv x := by
    ext i
    simp
  right_inv y := by
    ext j
    simp

@[simp] theorem leftTauChannelFunctionsEquivRight_apply
    (X Y Z : FibObject)
    (x : LeftTauChannelFunctions X Y Z)
    (j : RightTauChannelIndex X Y Z) :
    leftTauChannelFunctionsEquivRight X Y Z x j =
      x ((leftTauChannelEquivRightTauChannel X Y Z).symm j) :=
  rfl

end InfoGeometry.Categorical.FibonacciGlobalChannelBasis
