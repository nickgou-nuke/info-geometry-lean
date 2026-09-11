import InfoGeometry.Categorical.FibonacciBraidedCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Categorical.FibonacciGlobalChannelBasis

open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace

/-!
# Explicit τ-output channel indices

These finite sum types record the three fusion-channel summands in the
τ-output of the two parenthesizations.  They are only a basis index layer;
no fusion-tree ordering or associator is chosen here.
-/

abbrev LeftTauChannelIndex (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
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

abbrev RightTauChannelIndex (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
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

abbrev LeftTauFusionPathIndex (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  Sum (Fin (X FibSimple.unit * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.tau))
         (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))))))))

abbrev RightTauFusionPathIndex (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  Sum (Fin (X FibSimple.unit * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.unit))
         (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau))))))))

theorem leftTauFusionPathIndex_card (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (LeftTauFusionPathIndex X Y Z) =
      (fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau := by
  simp [LeftTauFusionPathIndex, fibTensorObj]
  <;> ring

theorem rightTauFusionPathIndex_card (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (RightTauFusionPathIndex X Y Z) =
      (fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau := by
  simp [RightTauFusionPathIndex, fibTensorObj]
  <;> ring

theorem leftTauFusionPathIndex_card_eq_right
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (LeftTauFusionPathIndex X Y Z) =
      Fintype.card (RightTauFusionPathIndex X Y Z) := by
  rw [leftTauFusionPathIndex_card, rightTauFusionPathIndex_card]
  simpa [fibTensorObj] using
    congrArg (fun W : InfoGeometry.Categorical.FibonacciHomSpace.FibCat => W FibSimple.tau)
      (fibTensorObj_assoc X Y Z)

noncomputable def leftTauFusionPathEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftTauFusionPathIndex X Y Z ≃ RightTauFusionPathIndex X Y Z :=
  (Fintype.equivFin (LeftTauFusionPathIndex X Y Z)).trans
    ((Equiv.cast (congrArg Fin
      (leftTauFusionPathIndex_card_eq_right X Y Z))).trans
      (Fintype.equivFin (RightTauFusionPathIndex X Y Z)).symm)

/-! The cardinality equivalence above is deliberately opaque.  The
    associator needs the semantic fusion-tree correspondence below. -/

def leftTauSemanticPathMap (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftTauFusionPathIndex X Y Z → RightTauFusionPathIndex X Y Z := fun i =>
  match i with
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
  | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) =>
      Sum.inr (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))))

def rightTauSemanticPathMap (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    RightTauFusionPathIndex X Y Z → LeftTauFusionPathIndex X Y Z := fun i =>
  match i with
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inr (Sum.inl i)) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) =>
      Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))))

noncomputable def leftTauSemanticPathEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftTauFusionPathIndex X Y Z ≃ RightTauFusionPathIndex X Y Z :=
  { toFun := leftTauSemanticPathMap X Y Z
    invFun := rightTauSemanticPathMap X Y Z
    left_inv := by
      intro i
      rcases i with i | i
      · rfl
      · rcases i with i | i
        · rfl
        · rcases i with i | i
          · rfl
          · rcases i with i | i
            · rfl
            · rcases i with i | i
              · rfl
              · rcases i with i | i
                · rfl
                · rcases i with i | i
                  · rfl
                  · rfl
    right_inv := by
      intro i
      rcases i with i | i
      · rfl
      · rcases i with i | i
        · rfl
        · rcases i with i | i
          · rfl
          · rcases i with i | i
            · rfl
            · rcases i with i | i
              · rfl
              · rcases i with i | i
                · rfl
                · rcases i with i | i
                  · rfl
                  · rfl }

/-! Selectors for the two repeated `τ ⊗ τ ⊗ τ` paths. -/

abbrev TauTripleMultiplicity (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : ℕ :=
  X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau

def leftTauFInputOne (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    LeftTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inl i)

def leftTauFInputTwo (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    LeftTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr i))))))

def rightTauFOutputOne (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    RightTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))

def rightTauFOutputTwo (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    RightTauFusionPathIndex X Y Z :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr i))))))

@[simp] theorem leftTauFInputOne_injective
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Function.Injective (leftTauFInputOne X Y Z) := by
  intro i j h
  exact Sum.inl.inj (Sum.inr.inj h)

@[simp] theorem leftTauFInputTwo_injective
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Function.Injective (leftTauFInputTwo X Y Z) := by
  intro i j h
  cases h
  rfl

@[simp] theorem leftTauSemanticPathMap_f_input_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    leftTauSemanticPathMap X Y Z (leftTauFInputOne X Y Z i) =
      rightTauFOutputOne X Y Z i := by
  rfl

@[simp] theorem leftTauSemanticPathMap_f_input_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    leftTauSemanticPathMap X Y Z (leftTauFInputTwo X Y Z i) =
      rightTauFOutputTwo X Y Z i := by
  rfl

@[simp] theorem rightTauSemanticPathMap_f_output_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    rightTauSemanticPathMap X Y Z (rightTauFOutputOne X Y Z i) =
      leftTauFInputOne X Y Z i := by
  rfl

@[simp] theorem rightTauSemanticPathMap_f_output_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    rightTauSemanticPathMap X Y Z (rightTauFOutputTwo X Y Z i) =
      leftTauFInputTwo X Y Z i := by
  rfl

theorem leftTauSemanticPathMap_eq_f_output_one_iff
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (i : LeftTauFusionPathIndex X Y Z)
    (k : Fin (TauTripleMultiplicity X Y Z)) :
    leftTauSemanticPathMap X Y Z i = rightTauFOutputOne X Y Z k ↔
      i = leftTauFInputOne X Y Z k := by
  constructor
  · intro h
    calc
      i = rightTauSemanticPathMap X Y Z
          (leftTauSemanticPathMap X Y Z i) := by
            exact (leftTauSemanticPathEquivRight X Y Z).left_inv i |>.symm
      _ = rightTauSemanticPathMap X Y Z
          (rightTauFOutputOne X Y Z k) := congrArg _ h
      _ = leftTauFInputOne X Y Z k := by rfl
  · intro h
    subst h
    rfl

theorem leftTauSemanticPathMap_eq_f_output_two_iff
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (i : LeftTauFusionPathIndex X Y Z)
    (k : Fin (TauTripleMultiplicity X Y Z)) :
    leftTauSemanticPathMap X Y Z i = rightTauFOutputTwo X Y Z k ↔
      i = leftTauFInputTwo X Y Z k := by
  constructor
  · intro h
    calc
      i = rightTauSemanticPathMap X Y Z
          (leftTauSemanticPathMap X Y Z i) := by
            exact (leftTauSemanticPathEquivRight X Y Z).left_inv i |>.symm
      _ = rightTauSemanticPathMap X Y Z
          (rightTauFOutputTwo X Y Z k) := congrArg _ h
      _ = leftTauFInputTwo X Y Z k := by rfl
  · intro h
    subst h
    rfl

theorem leftTauSemanticPathMap_symm_f_output_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (k : Fin (TauTripleMultiplicity X Y Z)) :
    (leftTauSemanticPathEquivRight X Y Z).symm
        (rightTauFOutputOne X Y Z k) =
      leftTauFInputOne X Y Z k := by
  apply (leftTauSemanticPathEquivRight X Y Z).injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem leftTauSemanticPathMap_symm_f_output_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (k : Fin (TauTripleMultiplicity X Y Z)) :
    (leftTauSemanticPathEquivRight X Y Z).symm
        (rightTauFOutputTwo X Y Z k) =
      leftTauFInputTwo X Y Z k := by
  apply (leftTauSemanticPathEquivRight X Y Z).injective
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] theorem rightTauFOutputOne_injective
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Function.Injective (rightTauFOutputOne X Y Z) := by
  intro i j h
  cases h
  rfl

@[simp] theorem rightTauFOutputTwo_injective
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Function.Injective (rightTauFOutputTwo X Y Z) := by
  intro i j h
  cases h
  rfl

theorem leftTauFInputOne_ne_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (i j : Fin (TauTripleMultiplicity X Y Z)) :
    leftTauFInputOne X Y Z i ≠ leftTauFInputTwo X Y Z j := by
  intro h
  cases h

theorem rightTauFOutputOne_ne_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (i j : Fin (TauTripleMultiplicity X Y Z)) :
    rightTauFOutputOne X Y Z i ≠ rightTauFOutputTwo X Y Z j := by
  intro h
  cases h

/-! The rectangular eight-path associator matrix.  The six ordinary paths are
    transported by the semantic path equivalence; only the two repeated
    `τττ → τ` paths carry the Fibonacci `F` block. -/

noncomputable def tauFusionPathEntry
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : LeftTauFusionPathIndex X Y Z)
    (j : RightTauFusionPathIndex X Y Z) : ℂ :=
  by
    classical
    exact match i with
      | Sum.inr (Sum.inl k) =>
          if j = rightTauFOutputOne X Y Z k then τ
          else if j = rightTauFOutputTwo X Y Z k then s else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr k)))))) =>
          if j = rightTauFOutputOne X Y Z k then s
          else if j = rightTauFOutputTwo X Y Z k then -τ else 0
      | i => if j = leftTauSemanticPathMap X Y Z i then 1 else 0

noncomputable def tauFusionPathMatrix
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    Matrix (LeftTauFusionPathIndex X Y Z)
      (RightTauFusionPathIndex X Y Z) ℂ :=
  tauFusionPathEntry X Y Z τ s

theorem tauFusionPathEntry_f_input_one_of_ne
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : Fin (TauTripleMultiplicity X Y Z))
    (j : RightTauFusionPathIndex X Y Z)
    (h₁ : j ≠ rightTauFOutputOne X Y Z i)
    (h₂ : j ≠ rightTauFOutputTwo X Y Z i) :
    tauFusionPathEntry X Y Z τ s
      (leftTauFInputOne X Y Z i) j = 0 := by
  simp [tauFusionPathEntry, leftTauFInputOne, h₁, h₂]

theorem tauFusionPathEntry_f_input_two_of_ne
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : Fin (TauTripleMultiplicity X Y Z))
    (j : RightTauFusionPathIndex X Y Z)
    (h₁ : j ≠ rightTauFOutputOne X Y Z i)
    (h₂ : j ≠ rightTauFOutputTwo X Y Z i) :
    tauFusionPathEntry X Y Z τ s
      (leftTauFInputTwo X Y Z i) j = 0 := by
  simp [tauFusionPathEntry, leftTauFInputTwo, h₁, h₂]

theorem tauFusionPathEntry_ordinary_row_at_f_output_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : LeftTauFusionPathIndex X Y Z)
    (k : Fin (TauTripleMultiplicity X Y Z))
    (h₁ : i ≠ leftTauFInputOne X Y Z k)
    (h₂ : i ≠ leftTauFInputTwo X Y Z k) :
    tauFusionPathEntry X Y Z τ s i
      (rightTauFOutputOne X Y Z k) = 0 := by
  rcases i with i | i
  · simp [tauFusionPathEntry, rightTauFOutputOne,
      leftTauSemanticPathMap, h₁, h₂]
  · rcases i with i | i
    · by_cases h : i = k
      · subst k
        exact (h₁ rfl).elim
      · have hout : rightTauFOutputOne X Y Z i ≠
          rightTauFOutputOne X Y Z k := by
          intro e
          exact h ((rightTauFOutputOne_injective X Y Z) e)
        have hcross : rightTauFOutputOne X Y Z k ≠
            rightTauFOutputTwo X Y Z i :=
          rightTauFOutputOne_ne_two X Y Z k i
        by_cases hcross' : rightTauFOutputOne X Y Z k =
            rightTauFOutputTwo X Y Z i
        · exact (hcross hcross').elim
        · simp [tauFusionPathEntry, rightTauFOutputOne, rightTauFOutputTwo,
            h, Ne.symm h,
            hout, Ne.symm hout, hcross, Ne.symm hcross, hcross']
    · rcases i with i | i
      · simp [tauFusionPathEntry, rightTauFOutputOne,
          leftTauSemanticPathMap, h₁, h₂]
      · rcases i with i | i
        · simp [tauFusionPathEntry, rightTauFOutputOne,
            leftTauSemanticPathMap, h₁, h₂]
        · rcases i with i | i
          · simp [tauFusionPathEntry, rightTauFOutputOne,
              leftTauSemanticPathMap, h₁, h₂]
          · rcases i with i | i
            · simp [tauFusionPathEntry, rightTauFOutputOne,
                leftTauSemanticPathMap, h₁, h₂]
            · rcases i with i | i
              · simp [tauFusionPathEntry, rightTauFOutputOne,
                  leftTauSemanticPathMap, h₁, h₂]
              · by_cases h : i = k
                · subst k
                  exact (h₂ rfl).elim
                · have hout : rightTauFOutputOne X Y Z i ≠
                    rightTauFOutputOne X Y Z k := by
                    intro e
                    exact h ((rightTauFOutputOne_injective X Y Z) e)
                  have hcross : rightTauFOutputOne X Y Z k ≠
                      rightTauFOutputTwo X Y Z i :=
                    rightTauFOutputOne_ne_two X Y Z k i
                  by_cases hcross' : rightTauFOutputOne X Y Z k =
                      rightTauFOutputTwo X Y Z i
                  · exact (hcross hcross').elim
                  · simp [tauFusionPathEntry, rightTauFOutputOne,
                      rightTauFOutputTwo, h,
                      Ne.symm h, hout, Ne.symm hout, hcross, Ne.symm hcross,
                      hcross']

theorem tauFusionPathEntry_ordinary_row_at_f_output_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : LeftTauFusionPathIndex X Y Z)
    (k : Fin (TauTripleMultiplicity X Y Z))
    (h₁ : i ≠ leftTauFInputOne X Y Z k)
    (h₂ : i ≠ leftTauFInputTwo X Y Z k) :
    tauFusionPathEntry X Y Z τ s i
      (rightTauFOutputTwo X Y Z k) = 0 := by
  rcases i with i | i
  · simp [tauFusionPathEntry, rightTauFOutputTwo,
      leftTauSemanticPathMap, h₁, h₂]
  · rcases i with i | i
    · by_cases h : i = k
      · subst k
        exact (h₁ rfl).elim
      · have hout : rightTauFOutputTwo X Y Z i ≠
            rightTauFOutputTwo X Y Z k := by
          intro e
          exact h ((rightTauFOutputTwo_injective X Y Z) e)
        have hcross : rightTauFOutputOne X Y Z i ≠
            rightTauFOutputTwo X Y Z k :=
          rightTauFOutputOne_ne_two X Y Z i k
        by_cases hcross' : rightTauFOutputOne X Y Z i =
            rightTauFOutputTwo X Y Z k
        · exact (hcross hcross').elim
        · simp [tauFusionPathEntry, rightTauFOutputOne,
            rightTauFOutputTwo, h, Ne.symm h, hout, Ne.symm hout,
            hcross, Ne.symm hcross, hcross']
    · rcases i with i | i
      · simp [tauFusionPathEntry, rightTauFOutputTwo,
          leftTauSemanticPathMap, h₁, h₂]
      · rcases i with i | i
        · simp [tauFusionPathEntry, rightTauFOutputTwo,
            leftTauSemanticPathMap, h₁, h₂]
        · rcases i with i | i
          · simp [tauFusionPathEntry, rightTauFOutputTwo,
              leftTauSemanticPathMap, h₁, h₂]
          · rcases i with i | i
            · simp [tauFusionPathEntry, rightTauFOutputTwo,
                leftTauSemanticPathMap, h₁, h₂]
            · rcases i with i | i
              · simp [tauFusionPathEntry, rightTauFOutputTwo,
                  leftTauSemanticPathMap, h₁, h₂]
              · by_cases h : i = k
                · subst k
                  exact (h₂ rfl).elim
                · have hout : rightTauFOutputTwo X Y Z i ≠
                      rightTauFOutputTwo X Y Z k := by
                    intro e
                    exact h ((rightTauFOutputTwo_injective X Y Z) e)
                  have hcross : rightTauFOutputOne X Y Z i ≠
                      rightTauFOutputTwo X Y Z k :=
                    rightTauFOutputOne_ne_two X Y Z i k
                  by_cases hcross' : rightTauFOutputOne X Y Z i =
                      rightTauFOutputTwo X Y Z k
                  · exact (hcross hcross').elim
                  · simp [tauFusionPathEntry, rightTauFOutputOne,
                      rightTauFOutputTwo, h, Ne.symm h, hout,
                      Ne.symm hout, hcross, Ne.symm hcross, hcross']

@[simp] theorem tauFusionPathMatrix_f_block_11
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : Fin (TauTripleMultiplicity X Y Z)) :
    tauFusionPathMatrix X Y Z τ s
        (leftTauFInputOne X Y Z i)
        (rightTauFOutputOne X Y Z i) = τ := by
  simp [tauFusionPathMatrix, tauFusionPathEntry, leftTauFInputOne,
    rightTauFOutputOne]

@[simp] theorem tauFusionPathMatrix_f_block_12
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : Fin (TauTripleMultiplicity X Y Z)) :
    tauFusionPathMatrix X Y Z τ s
        (leftTauFInputOne X Y Z i)
        (rightTauFOutputTwo X Y Z i) = s := by
  have hne : rightTauFOutputOne X Y Z i ≠ rightTauFOutputTwo X Y Z i := by
    intro h
    cases h
  have hne' := Ne.symm hne
  simp [tauFusionPathMatrix, tauFusionPathEntry, leftTauFInputOne,
    rightTauFOutputTwo, hne, hne', rightTauFOutputOne]

@[simp] theorem tauFusionPathMatrix_f_block_21
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : Fin (TauTripleMultiplicity X Y Z)) :
    tauFusionPathMatrix X Y Z τ s
        (leftTauFInputTwo X Y Z i)
        (rightTauFOutputOne X Y Z i) = s := by
  simp [tauFusionPathMatrix, tauFusionPathEntry, leftTauFInputTwo,
    rightTauFOutputOne]

@[simp] theorem tauFusionPathMatrix_f_block_22
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : Fin (TauTripleMultiplicity X Y Z)) :
    tauFusionPathMatrix X Y Z τ s
        (leftTauFInputTwo X Y Z i)
        (rightTauFOutputTwo X Y Z i) = -τ := by
  have hne : rightTauFOutputOne X Y Z i ≠ rightTauFOutputTwo X Y Z i := by
    intro h
    cases h
  have hne' := Ne.symm hne
  simp [tauFusionPathMatrix, tauFusionPathEntry, leftTauFInputTwo,
    rightTauFOutputTwo, hne, hne', rightTauFOutputOne]

/-! The `F` block before reindexing it into the full channel carrier. -/

noncomputable def tauTripleFMatrix (n : ℕ) (τ s : ℂ) :
    Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℂ :=
  fun i j => match i, j with
  | Sum.inl i, Sum.inl j => if i = j then τ else 0
  | Sum.inl i, Sum.inr j => if i = j then s else 0
  | Sum.inr i, Sum.inl j => if i = j then s else 0
  | Sum.inr i, Sum.inr j => if i = j then -τ else 0

@[simp] theorem tauTripleFMatrix_inl_inl
    (n : ℕ) (τ s : ℂ) (i j : Fin n) :
    tauTripleFMatrix n τ s (Sum.inl i) (Sum.inl j) =
      if i = j then τ else 0 := by
  rfl

@[simp] theorem tauTripleFMatrix_inl_inr
    (n : ℕ) (τ s : ℂ) (i j : Fin n) :
    tauTripleFMatrix n τ s (Sum.inl i) (Sum.inr j) =
      if i = j then s else 0 := by
  rfl

@[simp] theorem tauTripleFMatrix_inr_inl
    (n : ℕ) (τ s : ℂ) (i j : Fin n) :
    tauTripleFMatrix n τ s (Sum.inr i) (Sum.inl j) =
      if i = j then s else 0 := by
  rfl

@[simp] theorem tauTripleFMatrix_inr_inr
    (n : ℕ) (τ s : ℂ) (i j : Fin n) :
    tauTripleFMatrix n τ s (Sum.inr i) (Sum.inr j) =
      if i = j then -τ else 0 := by
  rfl

noncomputable def tauTripleFBlockMatrix (n : ℕ) (τ s : ℂ) :
    Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℂ :=
  Matrix.fromBlocks
    (τ • (1 : Matrix (Fin n) (Fin n) ℂ))
    (s • (1 : Matrix (Fin n) (Fin n) ℂ))
    (s • (1 : Matrix (Fin n) (Fin n) ℂ))
    ((-τ) • (1 : Matrix (Fin n) (Fin n) ℂ))

theorem tauTripleFMatrix_eq_reindex_block
    (n : ℕ) (τ s : ℂ) :
    tauTripleFMatrix n τ s = tauTripleFBlockMatrix n τ s := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [tauTripleFMatrix, tauTripleFBlockMatrix,
          Matrix.one_apply, mul_ite]
      | inr j =>
          by_cases h : i = j
          · simp [tauTripleFMatrix, tauTripleFBlockMatrix,
              Matrix.one_apply, mul_ite, h]
          · simp [tauTripleFMatrix, tauTripleFBlockMatrix,
              Matrix.one_apply, mul_ite, h]
  | inr i =>
      cases j with
      | inl j => simp [tauTripleFMatrix, tauTripleFBlockMatrix,
          Matrix.one_apply, mul_ite]
      | inr j =>
          by_cases h : i = j
          · simp [tauTripleFMatrix, tauTripleFBlockMatrix,
              Matrix.one_apply, mul_ite, h]
          · simp [tauTripleFMatrix, tauTripleFBlockMatrix,
              Matrix.one_apply, mul_ite, h]

theorem tauTripleFMatrix_sq
    (n : ℕ) (τ s : ℂ) (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    tauTripleFMatrix n τ s * tauTripleFMatrix n τ s = 1 := by
  rw [tauTripleFMatrix_eq_reindex_block]
  unfold tauTripleFBlockMatrix
  rw [Matrix.fromBlocks_multiply]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  have hτ' : τ * τ + s * s = 1 := by
    calc
      τ * τ + s * s = τ ^ 2 + s ^ 2 := by ring
      _ = τ ^ 2 + τ := by rw [hs]
      _ = 1 := hτ
  have hcross : τ * s + s * (-τ) = 0 := by ring
  have hcross' : s * τ + (-τ) * s = 0 := by ring
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
      | inr j =>
          by_cases h : i = j
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
  | inr i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
      | inr j =>
          by_cases h : i = j
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]
          · simp [Matrix.fromBlocks, Matrix.one_apply,
              hτ', hcross, hcross', mul_ite, h, mul_comm, add_comm]

def leftTauFBlockInput
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Sum (Fin (TauTripleMultiplicity X Y Z))
      (Fin (TauTripleMultiplicity X Y Z)) →
      LeftTauFusionPathIndex X Y Z
  | Sum.inl i => leftTauFInputOne X Y Z i
  | Sum.inr i => leftTauFInputTwo X Y Z i

def rightTauFBlockOutput
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Sum (Fin (TauTripleMultiplicity X Y Z))
      (Fin (TauTripleMultiplicity X Y Z)) →
      RightTauFusionPathIndex X Y Z
  | Sum.inl i => rightTauFOutputOne X Y Z i
  | Sum.inr i => rightTauFOutputTwo X Y Z i

theorem tauFusionPathMatrix_f_block_eq
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
        (leftTauFBlockInput X Y Z)
        (rightTauFBlockOutput X Y Z) =
      tauTripleFMatrix (TauTripleMultiplicity X Y Z) τ s := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · subst j
            simp [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix]
          · have h₁ : leftTauFInputOne X Y Z i ≠
                leftTauFInputOne X Y Z j := by
              intro e
              exact h ((leftTauFInputOne_injective X Y Z) e)
            have h₂ : leftTauFInputOne X Y Z i ≠
                leftTauFInputTwo X Y Z j :=
              leftTauFInputOne_ne_two X Y Z i j
            have hz := tauFusionPathEntry_ordinary_row_at_f_output_one
              X Y Z τ s (leftTauFInputOne X Y Z i) j h₁ h₂
            simpa [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix,
              tauFusionPathMatrix, h] using hz
      | inr j =>
          by_cases h : i = j
          · subst j
            simp [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix]
          · have h₁ : leftTauFInputOne X Y Z i ≠
                leftTauFInputOne X Y Z j := by
              intro e
              exact h ((leftTauFInputOne_injective X Y Z) e)
            have h₂ : leftTauFInputOne X Y Z i ≠
                leftTauFInputTwo X Y Z j :=
              leftTauFInputOne_ne_two X Y Z i j
            have hz := tauFusionPathEntry_ordinary_row_at_f_output_two
              X Y Z τ s (leftTauFInputOne X Y Z i) j h₁ h₂
            simpa [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix,
              tauFusionPathMatrix, h] using hz
  | inr i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · subst j
            simp [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix]
          · have h₁ : leftTauFInputTwo X Y Z i ≠
                leftTauFInputOne X Y Z j := by
              exact Ne.symm (leftTauFInputOne_ne_two X Y Z j i)
            have h₂ : leftTauFInputTwo X Y Z i ≠
                leftTauFInputTwo X Y Z j := by
              intro e
              exact h ((leftTauFInputTwo_injective X Y Z) e)
            have hz := tauFusionPathEntry_ordinary_row_at_f_output_one
              X Y Z τ s (leftTauFInputTwo X Y Z i) j h₁ h₂
            simpa [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix,
              tauFusionPathMatrix, h] using hz
      | inr j =>
          by_cases h : i = j
          · subst j
            simp [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix]
          · have h₁ : leftTauFInputTwo X Y Z i ≠
                leftTauFInputOne X Y Z j := by
              exact Ne.symm (leftTauFInputOne_ne_two X Y Z j i)
            have h₂ : leftTauFInputTwo X Y Z i ≠
                leftTauFInputTwo X Y Z j := by
              intro e
              exact h ((leftTauFInputTwo_injective X Y Z) e)
            have hz := tauFusionPathEntry_ordinary_row_at_f_output_two
              X Y Z τ s (leftTauFInputTwo X Y Z i) j h₁ h₂
            simpa [Matrix.submatrix, leftTauFBlockInput,
              rightTauFBlockOutput, tauTripleFMatrix,
              tauFusionPathMatrix, h] using hz

theorem tauFusionPathMatrix_f_block_sq
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
        (leftTauFBlockInput X Y Z)
        (rightTauFBlockOutput X Y Z) *
      Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
        (leftTauFBlockInput X Y Z)
        (rightTauFBlockOutput X Y Z) =
      (1 : Matrix
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z)))
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z))) ℂ) := by
  rw [tauFusionPathMatrix_f_block_eq]
  exact tauTripleFMatrix_sq (TauTripleMultiplicity X Y Z) τ s hs hτ

theorem tauTripleFMatrix_transpose
    (n : ℕ) (τ s : ℂ) :
    Matrix.transpose (tauTripleFMatrix n τ s) =
      tauTripleFMatrix n τ s := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [tauTripleFMatrix, eq_comm]
      | inr j => simp [tauTripleFMatrix, eq_comm]
  | inr i =>
      cases j with
      | inl j => simp [tauTripleFMatrix, eq_comm]
      | inr j => simp [tauTripleFMatrix, eq_comm]

theorem tauFusionPathMatrix_f_block_transpose_mul
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Matrix.transpose (Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
        (leftTauFBlockInput X Y Z)
        (rightTauFBlockOutput X Y Z)) *
      Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
        (leftTauFBlockInput X Y Z)
        (rightTauFBlockOutput X Y Z) =
      (1 : Matrix
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z)))
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z))) ℂ) := by
  rw [tauFusionPathMatrix_f_block_eq]
  rw [tauTripleFMatrix_transpose]
  exact tauTripleFMatrix_sq (TauTripleMultiplicity X Y Z) τ s hs hτ

/-
def leftTauOrdinaryPath (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  {i : LeftTauFusionPathIndex X Y Z //
    (∀ k, i ≠ leftTauFInputOne X Y Z k) ∧
    (∀ k, i ≠ leftTauFInputTwo X Y Z k)}

def rightTauOrdinaryPath (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  {j : RightTauFusionPathIndex X Y Z //
    (∀ k, j ≠ rightTauFOutputOne X Y Z k) ∧
    (∀ k, j ≠ rightTauFOutputTwo X Y Z k)}

def leftTauOrdinaryPathEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    leftTauOrdinaryPath X Y Z ≃ rightTauOrdinaryPath X Y Z :=
  { toFun := fun i =>
    ⟨leftTauSemanticPathMap X Y Z i.1, by
      constructor
      · intro k h
        exact i.2.1 k ((leftTauSemanticPathMap_eq_f_output_one_iff
          X Y Z i.1 k).1 h)
      · intro k h
        exact i.2.2 k ((leftTauSemanticPathMap_eq_f_output_two_iff
          X Y Z i.1 k).1 h)⟩
    invFun := fun j =>
    ⟨rightTauSemanticPathMap X Y Z j.1, by
      constructor
      · intro k h
        apply j.2.1 k
        calc
          j.1 = leftTauSemanticPathMap X Y Z
              (rightTauSemanticPathMap X Y Z j.1) := by
                exact (leftTauSemanticPathEquivRight X Y Z).right_inv j.1 |>.symm
          _ = leftTauSemanticPathMap X Y Z
              (leftTauFInputOne X Y Z k) := congrArg
                (leftTauSemanticPathMap X Y Z) h
          _ = rightTauFOutputOne X Y Z k := by rfl
      · intro k h
        apply j.2.2 k
        calc
          j.1 = leftTauSemanticPathMap X Y Z
              (rightTauSemanticPathMap X Y Z j.1) := by
                exact (leftTauSemanticPathEquivRight X Y Z).right_inv j.1 |>.symm
          _ = leftTauSemanticPathMap X Y Z
              (leftTauFInputTwo X Y Z k) := congrArg
                (leftTauSemanticPathMap X Y Z) h
          _ = rightTauFOutputTwo X Y Z k := by rfl⟩
    left_inv := by
      intro i
      apply Subtype.ext
      exact (leftTauSemanticPathEquivRight X Y Z).left_inv i.1
    right_inv := by
      intro j
      apply Subtype.ext
      exact (leftTauSemanticPathEquivRight X Y Z).right_inv j.1 }

noncomputable def tauFusionPathOrdinaryMatrix
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    Matrix (leftTauOrdinaryPath X Y Z)
      (rightTauOrdinaryPath X Y Z) ℂ :=
  Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
    Subtype.val Subtype.val

noncomputable def tauFusionPathOrdinaryPermutation
    {α β : Type*}
    (e : α ≃ β) : Matrix α β ℂ := by
  classical
  exact fun i j => if e i = j then 1 else 0

def rectangularMatrixMul
    {α β γ R : Type*} [Fintype β] [AddCommMonoid R] [Mul R]
    (M : Matrix α β R) (N : Matrix β γ R) : Matrix α γ R :=
  fun i k => ∑ j, M i j * N j k

theorem tauFusionPathOrdinaryMatrix_eq_permutation
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    tauFusionPathOrdinaryMatrix X Y Z τ s =
      tauFusionPathOrdinaryPermutation
        (leftTauOrdinaryPathEquivRight X Y Z) := by
  classical
  ext i j
  simp [tauFusionPathOrdinaryMatrix, tauFusionPathOrdinaryPermutation,
    Matrix.submatrix, tauFusionPathMatrix, tauFusionPathEntry,
    leftTauOrdinaryPath, rightTauOrdinaryPath]

theorem tauFusionPathOrdinaryMatrix_mul_transpose
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    rectangularMatrixMul
        (tauFusionPathOrdinaryMatrix X Y Z τ s)
        (Matrix.transpose (tauFusionPathOrdinaryMatrix X Y Z τ s)) =
      (1 : Matrix (leftTauOrdinaryPath X Y Z)
        (leftTauOrdinaryPath X Y Z) ℂ) := by
  classical
  letI : Fintype (leftTauOrdinaryPath X Y Z) :=
    Fintype.subtype Finset.univ (by simp)
  letI : Fintype (rightTauOrdinaryPath X Y Z) :=
    Fintype.subtype Finset.univ (by simp)
  rw [tauFusionPathOrdinaryMatrix_eq_permutation]
  ext i k
  by_cases h : i = k
  · subst k
    simp [tauFusionPathOrdinaryPermutation, rectangularMatrixMul]
  · simp [tauFusionPathOrdinaryPermutation, rectangularMatrixMul, h]

theorem tauFusionPathOrdinaryMatrix_transpose_mul
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    rectangularMatrixMul
        (Matrix.transpose (tauFusionPathOrdinaryMatrix X Y Z τ s))
        (tauFusionPathOrdinaryMatrix X Y Z τ s) =
      (1 : Matrix (rightTauOrdinaryPath X Y Z)
        (rightTauOrdinaryPath X Y Z) ℂ) := by
  classical
  letI : Fintype (leftTauOrdinaryPath X Y Z) :=
    Fintype.subtype Finset.univ (by simp)
  letI : Fintype (rightTauOrdinaryPath X Y Z) :=
    Fintype.subtype Finset.univ (by simp)
  rw [tauFusionPathOrdinaryMatrix_eq_permutation]
  ext j l
  by_cases h : j = l
  · subst l
    simp [tauFusionPathOrdinaryPermutation, rectangularMatrixMul]
  · simp [tauFusionPathOrdinaryPermutation, rectangularMatrixMul, h]

-/
/-! The five unit-output channels are only reassociated; no Fibonacci block
appears there. -/

abbrev LeftUnitFusionPathIndex (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  Sum (Fin (X FibSimple.unit * Y FibSimple.unit * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.tau))
         (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau)))))

abbrev RightUnitFusionPathIndex (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  Sum (Fin (X FibSimple.unit * Y FibSimple.unit * Z FibSimple.unit))
    (Sum (Fin (X FibSimple.unit * Y FibSimple.tau * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.unit * Z FibSimple.tau))
    (Sum (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.unit))
         (Fin (X FibSimple.tau * Y FibSimple.tau * Z FibSimple.tau)))))

def leftUnitFusionPathEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftUnitFusionPathIndex X Y Z ≃ RightUnitFusionPathIndex X Y Z where
  toFun := fun i => match i with
    | Sum.inl i => Sum.inl i
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
    | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => Sum.inr (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))
  invFun := fun i => match i with
    | Sum.inl i => Sum.inl i
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr (Sum.inl i)) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))
  left_inv := by
    intro i
    cases i <;> aesop
  right_inv := by
    intro i
    cases i <;> aesop

noncomputable def leftUnitFusionFunctionsEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    (LeftUnitFusionPathIndex X Y Z → ℂ) ≃ₗ[ℂ]
      (RightUnitFusionPathIndex X Y Z → ℂ) where
  toFun x j := x ((leftUnitFusionPathEquivRight X Y Z).symm j)
  invFun y i := y (leftUnitFusionPathEquivRight X Y Z i)
  map_add' x y := by ext j; rfl
  map_smul' c x := by ext j; rfl
  left_inv x := by ext i; simp
  right_inv y := by ext j; simp

theorem leftUnitFusionPathIndex_card (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (LeftUnitFusionPathIndex X Y Z) =
      (fibTensorObj (fibTensorObj X Y) Z) FibSimple.unit := by
  simp [LeftUnitFusionPathIndex, fibTensorObj]
  <;> ring

theorem rightUnitFusionPathIndex_card (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (RightUnitFusionPathIndex X Y Z) =
      (fibTensorObj X (fibTensorObj Y Z)) FibSimple.unit := by
  simp [RightUnitFusionPathIndex, fibTensorObj]
  <;> ring

noncomputable def leftUnitFusionPathFinEquiv
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftUnitFusionPathIndex X Y Z ≃
      Fin ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.unit) :=
  (Fintype.equivFin (LeftUnitFusionPathIndex X Y Z)).trans
    (Equiv.cast (congrArg Fin (leftUnitFusionPathIndex_card X Y Z)))

noncomputable def rightUnitFusionPathFinEquiv
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    RightUnitFusionPathIndex X Y Z ≃
      Fin ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.unit) :=
  (Fintype.equivFin (RightUnitFusionPathIndex X Y Z)).trans
    (Equiv.cast (congrArg Fin (rightUnitFusionPathIndex_card X Y Z)))

noncomputable def unitFusionPathMatrix
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Matrix (LeftUnitFusionPathIndex X Y Z)
      (RightUnitFusionPathIndex X Y Z) ℂ := by
  classical
  exact fun i j => if leftUnitFusionPathEquivRight X Y Z i = j then 1 else 0

noncomputable def unitFusionPathMatrixTransport
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Matrix (Fin ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.unit))
      (Fin ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.unit)) ℂ :=
  Matrix.reindex (leftUnitFusionPathFinEquiv X Y Z)
    (rightUnitFusionPathFinEquiv X Y Z)
    (unitFusionPathMatrix X Y Z)

theorem leftTauChannelIndex_card (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (LeftTauChannelIndex X Y Z) =
      (fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau := by
  simp [LeftTauChannelIndex, fibTensorObj]
  <;> ring

theorem rightTauChannelIndex_card (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (RightTauChannelIndex X Y Z) =
      (fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau := by
  simp [RightTauChannelIndex, fibTensorObj]
  <;> ring

theorem leftTauChannelIndex_card_eq_right
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype.card (LeftTauChannelIndex X Y Z) =
      Fintype.card (RightTauChannelIndex X Y Z) := by
  rw [leftTauChannelIndex_card, rightTauChannelIndex_card]
  simpa [fibTensorObj] using
    congrArg (fun W : FibCat => W FibSimple.tau)
      (fibTensorObj_assoc X Y Z)

noncomputable def leftTauChannelEquivRightTauChannel
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftTauChannelIndex X Y Z ≃ RightTauChannelIndex X Y Z :=
  (Fintype.equivFin (LeftTauChannelIndex X Y Z)).trans
    ((Equiv.cast (congrArg Fin (leftTauChannelIndex_card_eq_right X Y Z))).trans
      (Fintype.equivFin (RightTauChannelIndex X Y Z)).symm)

abbrev LeftTauChannelFunctions (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  LeftTauChannelIndex X Y Z → ℂ

abbrev RightTauChannelFunctions (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  RightTauChannelIndex X Y Z → ℂ

/-! The induced linear equivalence on channel-valued functions.  This is the
reindexing layer for a future block-preserving `FibHom`; it does not yet
choose the Fibonacci `F`-matrix on the two distinguished channels. -/
noncomputable def leftTauChannelFunctionsEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
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
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (x : LeftTauChannelFunctions X Y Z)
    (j : RightTauChannelIndex X Y Z) :
    leftTauChannelFunctionsEquivRight X Y Z x j =
      x ((leftTauChannelEquivRightTauChannel X Y Z).symm j) :=
  rfl

/-! --------------------------------------------------------------------------
    Canonical `Fin` bases for the refined τ fusion paths

    `FibHom.tau_comp` is indexed by `Fin` dimensions, whereas the refined
    path carriers above deliberately retain their fusion-tree sum structure.
    These equivalences are the canonical boundary between the two views.
    No associator is chosen here: this is only basis transport.
    -------------------------------------------------------------------------- -/

noncomputable def leftTauFusionPathFinEquiv
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    LeftTauFusionPathIndex X Y Z ≃
      Fin ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau) :=
  (Fintype.equivFin (LeftTauFusionPathIndex X Y Z)).trans
    (Equiv.cast (congrArg Fin (leftTauFusionPathIndex_card X Y Z)))

noncomputable def rightTauFusionPathFinEquiv
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    RightTauFusionPathIndex X Y Z ≃
      Fin ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau) :=
  (Fintype.equivFin (RightTauFusionPathIndex X Y Z)).trans
    (Equiv.cast (congrArg Fin (rightTauFusionPathIndex_card X Y Z)))

@[simp] theorem leftTauFusionPathFinEquiv_apply
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (i : LeftTauFusionPathIndex X Y Z) :
    leftTauFusionPathFinEquiv X Y Z i =
      (Equiv.cast (congrArg Fin (leftTauFusionPathIndex_card X Y Z)))
        (Fintype.equivFin (LeftTauFusionPathIndex X Y Z) i) :=
  rfl

@[simp] theorem rightTauFusionPathFinEquiv_apply
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (i : RightTauFusionPathIndex X Y Z) :
    rightTauFusionPathFinEquiv X Y Z i =
      (Equiv.cast (congrArg Fin (rightTauFusionPathIndex_card X Y Z)))
        (Fintype.equivFin (RightTauFusionPathIndex X Y Z) i) :=
  rfl

noncomputable def leftTauFusionPathMatrixTransport
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (M : Matrix (LeftTauFusionPathIndex X Y Z)
      (LeftTauFusionPathIndex X Y Z) ℂ) :
    Matrix (Fin ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau))
      (Fin ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau)) ℂ :=
  Matrix.reindex (leftTauFusionPathFinEquiv X Y Z)
    (leftTauFusionPathFinEquiv X Y Z) M

noncomputable def rightTauFusionPathMatrixTransport
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (M : Matrix (RightTauFusionPathIndex X Y Z)
      (RightTauFusionPathIndex X Y Z) ℂ) :
    Matrix (Fin ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau))
      (Fin ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau)) ℂ :=
  Matrix.reindex (rightTauFusionPathFinEquiv X Y Z)
    (rightTauFusionPathFinEquiv X Y Z) M

/-! `blockDiag3` is the native channel carrier used by `fibTensorHom`.
The following readback exposes its final channel without introducing a
second channel index type. -/

theorem blockDiag3_lastBlock_apply
    {α : Type} [Zero α]
    {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) α)
    (B : Matrix (Fin m₂) (Fin n₂) α)
    (C : Matrix (Fin m₃) (Fin n₃) α)
    (i : Fin m₃) (j : Fin n₃) :
    blockDiag3 A B C
        (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inr j)) = C i j := by
  simp [blockDiag3, blockDiag2, Matrix.reindex, Matrix.fromBlocks]

/-
abbrev LeftTauFusionPathFunctions (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  LeftTauFusionPathIndex X Y Z → ℂ

abbrev RightTauFusionPathFunctions (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  RightTauFusionPathIndex X Y Z → ℂ

noncomputable def tauFusionPathFLinearMap
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    LeftTauFusionPathFunctions X Y Z →ₗ[ℂ]
      RightTauFusionPathFunctions X Y Z where
  toFun x j := match j with
    | Sum.inl j => x (rightTauSemanticPathMap X Y Z (Sum.inl j))
    | Sum.inr (Sum.inl j) => x (rightTauSemanticPathMap X Y Z (Sum.inr (Sum.inl j)))
    | Sum.inr (Sum.inr (Sum.inl j)) => x (rightTauSemanticPathMap X Y Z (Sum.inr (Sum.inr (Sum.inl j))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) => x (rightTauSemanticPathMap X Y Z (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) =>
        τ * x (leftTauFInputOne X Y Z j) + s * x (leftTauFInputTwo X Y Z j)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) => x (rightTauSemanticPathMap X Y Z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))) => x (rightTauSemanticPathMap X Y Z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))))) =>
        s * x (leftTauFInputOne X Y Z j) - τ * x (leftTauFInputTwo X Y Z j)
  map_add' x y := by
    funext j
    rcases j with j | j
    · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
    · rcases j with j | j
      · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
      · rcases j with j | j
        · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
        · rcases j with j | j
          · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
          · rcases j with j | j
            · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
            · rcases j with j | j
              · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
              · rcases j with j | j
                · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
                · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
  map_smul' c x := by
    funext j
    rcases j with j | j
    · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
    · rcases j with j | j
      · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
      · rcases j with j | j
        · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
        · rcases j with j | j
          · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
          · rcases j with j | j
            · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
            · rcases j with j | j
              · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
              · rcases j with j | j
                · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
                · simp [tauFusionPathFLinearMap, add_mul, mul_add, smul_add, mul_smul]
/-
-/
noncomputable def tauFusionPathMatrixTransport
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    Matrix (Fin ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau))
      (Fin ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau)) ℂ :=
  Matrix.reindex (leftTauFusionPathFinEquiv X Y Z)
    (rightTauFusionPathFinEquiv X Y Z)
    (tauFusionPathMatrix X Y Z τ s)

noncomputable def fibonacciAssociatorHom
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    FibHom (fibTensorObj (fibTensorObj X Y) Z)
      (fibTensorObj X (fibTensorObj Y Z)) :=
  { unit_comp := unitFusionPathMatrixTransport X Y Z
    tau_comp := tauFusionPathMatrixTransport X Y Z τ s }

noncomputable def fibonacciAssociatorInv
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    FibHom (fibTensorObj X (fibTensorObj Y Z))
      (fibTensorObj (fibTensorObj X Y) Z) :=
  { unit_comp := Matrix.transpose (unitFusionPathMatrixTransport X Y Z)
    tau_comp := Matrix.transpose (tauFusionPathMatrixTransport X Y Z τ s) }

@[simp] theorem fibonacciAssociatorHom_unit_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorHom X Y Z τ s).unit_comp =
      unitFusionPathMatrixTransport X Y Z :=
  rfl

@[simp] theorem fibonacciAssociatorHom_tau_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorHom X Y Z τ s).tau_comp =
      tauFusionPathMatrixTransport X Y Z τ s :=
  rfl

@[simp] theorem fibonacciAssociatorInv_unit_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorInv X Y Z τ s).unit_comp =
      Matrix.transpose (unitFusionPathMatrixTransport X Y Z) :=
  rfl

@[simp] theorem fibonacciAssociatorInv_tau_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorInv X Y Z τ s).tau_comp =
      Matrix.transpose (tauFusionPathMatrixTransport X Y Z τ s) :=
  rfl
 -/

end InfoGeometry.Categorical.FibonacciGlobalChannelBasis
