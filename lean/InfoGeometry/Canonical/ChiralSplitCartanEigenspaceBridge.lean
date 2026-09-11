import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

/-!
# Eigenspace routing for the finite chiral block

The auxiliary block grading `gamma` has `qPlus` and `qMinus` as opposite
off-diagonal maps.  This file packages that fact as maps between the two
`±1` eigenspaces.  The eigenspaces are local to the two-by-two matrix carrier;
no identification with a native Clifford chirality or a Krein fundamental
symmetry is asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralSplitCartanEigenspaceBridge

open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

abbrev Two := Fin 2
abbrev TwoVector (A : Type*) := Two → A

def GammaPlus (A : Type*) [Ring A] [Algebra ℝ A] :
    Submodule ℝ (TwoVector A) where
  carrier := {v | Matrix.mulVec gamma v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Matrix.mulVec gamma (v + w) = v + w
    rw [Matrix.mulVec_add, hv, hw]
  smul_mem' := by
    intro c v hv
    change Matrix.mulVec gamma (c • v) = c • v
    rw [Matrix.mulVec_smul, hv]

def GammaMinus (A : Type*) [Ring A] [Algebra ℝ A] :
    Submodule ℝ (TwoVector A) where
  carrier := {v | Matrix.mulVec gamma v = -v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Matrix.mulVec gamma (v + w) = -(v + w)
    rw [Matrix.mulVec_add, hv, hw, neg_add]
  smul_mem' := by
    intro c v hv
    change Matrix.mulVec gamma (c • v) = -(c • v)
    rw [Matrix.mulVec_smul, hv, smul_neg]

def qPlusMap {A : Type*} [Ring A] [Algebra ℝ A] (a : A) :
    GammaMinus A → GammaPlus A := fun v =>
  ⟨Matrix.mulVec (qPlus a) v.1, by
    calc
      Matrix.mulVec gamma (Matrix.mulVec (qPlus a) v.1) =
          Matrix.mulVec (gamma * qPlus a) v.1 := by
            rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (-(qPlus a * gamma)) v.1 := by
            rw [gamma_qPlus_anticomm]
      _ = -Matrix.mulVec (qPlus a) (Matrix.mulVec gamma v.1) := by
            rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (qPlus a) v.1 := by
            rw [v.2]
            rw [Matrix.mulVec_neg]
            simp⟩

def qMinusMap {A : Type*} [Ring A] [Algebra ℝ A] (b : A) :
    GammaPlus A → GammaMinus A := fun v =>
  ⟨Matrix.mulVec (qMinus b) v.1, by
    calc
      Matrix.mulVec gamma (Matrix.mulVec (qMinus b) v.1) =
          Matrix.mulVec (gamma * qMinus b) v.1 := by
            rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (-(qMinus b * gamma)) v.1 := by
            rw [gamma_qMinus_anticomm]
      _ = -Matrix.mulVec (qMinus b) (Matrix.mulVec gamma v.1) := by
            rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
      _ = -Matrix.mulVec (qMinus b) v.1 := by
            rw [v.2]
            ⟩

def qPlusLinearMap {A : Type*} [Ring A] [Algebra ℝ A] (a : A) :
    GammaMinus A →ₗ[ℝ] GammaPlus A where
  toFun := qPlusMap a
  map_add' := by
    intro v w
    apply Subtype.ext
    simp [qPlusMap, Matrix.mulVec_add]
  map_smul' := by
    intro c v
    apply Subtype.ext
    change Matrix.mulVec (qPlus a) (c • v.1) =
      c • Matrix.mulVec (qPlus a) v.1
    exact Matrix.mulVec_smul (qPlus a) c v.1

def qMinusLinearMap {A : Type*} [Ring A] [Algebra ℝ A] (b : A) :
    GammaPlus A →ₗ[ℝ] GammaMinus A where
  toFun := qMinusMap b
  map_add' := by
    intro v w
    apply Subtype.ext
    simp [qMinusMap, Matrix.mulVec_add]
  map_smul' := by
    intro c v
    apply Subtype.ext
    change Matrix.mulVec (qMinus b) (c • v.1) =
      c • Matrix.mulVec (qMinus b) v.1
    exact Matrix.mulVec_smul (qMinus b) c v.1

@[simp] theorem qPlusMap_val {A : Type*} [Ring A] [Algebra ℝ A] (a : A)
    (v : GammaMinus A) :
    (qPlusMap a v).1 = Matrix.mulVec (qPlus a) v.1 := rfl

@[simp] theorem qMinusMap_val {A : Type*} [Ring A] [Algebra ℝ A] (b : A)
    (v : GammaPlus A) :
    (qMinusMap b v).1 = Matrix.mulVec (qMinus b) v.1 := rfl

@[simp] theorem qPlusLinearMap_apply {A : Type*} [Ring A] [Algebra ℝ A] (a : A)
    (v : GammaMinus A) :
    qPlusLinearMap a v = qPlusMap a v := rfl

@[simp] theorem qMinusLinearMap_apply {A : Type*} [Ring A] [Algebra ℝ A] (b : A)
    (v : GammaPlus A) :
    qMinusLinearMap b v = qMinusMap b v := rfl

end InfoGeometry.OperatorAlgebra.ChiralSplitCartanEigenspaceBridge
