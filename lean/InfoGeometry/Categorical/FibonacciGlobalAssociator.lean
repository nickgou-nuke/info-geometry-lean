import InfoGeometry.Categorical.FibonacciGlobalChannelBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Categorical.FibonacciGlobalAssociator

open InfoGeometry.Categorical.FibonacciGlobalChannelBasis
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciHomSpace

/-! A permutation matrix associated to a finite equivalence. -/

noncomputable def equivPermutationMatrix
    {α β R : Type*} [Zero R] [One R]
    (e : α ≃ β) : Matrix α β R := by
  classical
  exact fun i j => if e i = j then 1 else 0

theorem equivPermutationMatrix_mul_transpose
    {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Semiring R]
    (e : α ≃ β) :
    equivPermutationMatrix e * Matrix.transpose (equivPermutationMatrix e) =
      (1 : Matrix α α R) := by
  classical
  ext i k
  by_cases h : i = k
  · subst k
    simp [equivPermutationMatrix, Matrix.mul_apply]
  · simp [equivPermutationMatrix, Matrix.mul_apply, h]

theorem equivPermutationMatrix_transpose_mul
    {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Semiring R]
    (e : α ≃ β) :
    Matrix.transpose (equivPermutationMatrix e) * equivPermutationMatrix e =
      (1 : Matrix β β R) := by
  classical
  ext j l
  by_cases h : j = l
  · subst l
    rw [Matrix.mul_apply]
    rw [Fintype.sum_equiv e
      (fun x => Matrix.transpose (equivPermutationMatrix e) j x *
        equivPermutationMatrix e x j)
      (fun x => if x = j then 1 else 0)]
    · simp
    · intro x
      simp only [Matrix.transpose_apply, equivPermutationMatrix]
      by_cases hx : e x = j <;> simp [hx]
  · rw [Matrix.mul_apply]
    rw [Fintype.sum_equiv e
      (fun x => Matrix.transpose (equivPermutationMatrix e) j x *
        equivPermutationMatrix e x l)
      (fun x => (if x = j then 1 else 0) *
        (if x = l then 1 else 0))]
    · simp [h, Ne.symm h]
    · intro x
      simp only [Matrix.transpose_apply, equivPermutationMatrix]
      by_cases hx : e x = j <;> by_cases hy : e x = l <;>
        simp [hx, hy]

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

theorem tauTripleFMatrix_transpose_mul
    (n : ℕ) (τ s : ℂ) (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    Matrix.transpose (tauTripleFMatrix n τ s) *
        tauTripleFMatrix n τ s = 1 := by
  rw [tauTripleFMatrix_transpose]
  exact tauTripleFMatrix_sq n τ s hs hτ

theorem fibonacciAssociator_tau_f_block_transpose_mul
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
  exact tauFusionPathMatrix_f_block_transpose_mul X Y Z τ s hs hτ

/-! The global typed maps below reuse the existing finite channel basis and
reindexing owners.  They deliberately do not install a monoidal instance.
The inverse has the opposite source and target; it is not obtained by
permuting the object arguments. -/

noncomputable def fibonacciAssociatorHom
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    FibHom (fibTensorObj (fibTensorObj X Y) Z)
      (fibTensorObj X (fibTensorObj Y Z)) :=
  { unit_comp := unitFusionPathMatrixTransport X Y Z
    tau_comp :=
      Matrix.reindex (leftTauFusionPathFinEquiv X Y Z)
        (rightTauFusionPathFinEquiv X Y Z)
        (tauFusionPathMatrix X Y Z τ s) }

noncomputable def fibonacciAssociatorInv
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    FibHom (fibTensorObj X (fibTensorObj Y Z))
      (fibTensorObj (fibTensorObj X Y) Z) :=
  { unit_comp := Matrix.transpose (unitFusionPathMatrixTransport X Y Z)
    tau_comp :=
      Matrix.transpose
        (Matrix.reindex (leftTauFusionPathFinEquiv X Y Z)
          (rightTauFusionPathFinEquiv X Y Z)
          (tauFusionPathMatrix X Y Z τ s)) }

theorem unitFusionPathMatrix_mul_transpose
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    unitFusionPathMatrix X Y Z *
        Matrix.transpose (unitFusionPathMatrix X Y Z) =
      (1 : Matrix (LeftUnitFusionPathIndex X Y Z)
        (LeftUnitFusionPathIndex X Y Z) ℂ) := by
  have hM : unitFusionPathMatrix X Y Z =
      equivPermutationMatrix (R := ℂ)
        (leftUnitFusionPathEquivRight X Y Z) := by
    funext i j
    simp [unitFusionPathMatrix, equivPermutationMatrix]
  rw [hM]
  exact equivPermutationMatrix_mul_transpose (R := ℂ)
    (leftUnitFusionPathEquivRight X Y Z :
      LeftUnitFusionPathIndex X Y Z ≃ RightUnitFusionPathIndex X Y Z)

theorem unitFusionPathMatrix_transpose_mul
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Matrix.transpose (unitFusionPathMatrix X Y Z) *
        unitFusionPathMatrix X Y Z =
      (1 : Matrix (RightUnitFusionPathIndex X Y Z)
        (RightUnitFusionPathIndex X Y Z) ℂ) := by
  have hM : unitFusionPathMatrix X Y Z =
      equivPermutationMatrix (R := ℂ)
        (leftUnitFusionPathEquivRight X Y Z) := by
    funext i j
    simp [unitFusionPathMatrix, equivPermutationMatrix]
  rw [hM]
  exact equivPermutationMatrix_transpose_mul (R := ℂ)
    (leftUnitFusionPathEquivRight X Y Z :
      LeftUnitFusionPathIndex X Y Z ≃ RightUnitFusionPathIndex X Y Z)

@[simp] theorem fibonacciAssociatorHom_unit_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorHom X Y Z τ s).unit_comp =
      unitFusionPathMatrixTransport X Y Z := rfl

@[simp] theorem fibonacciAssociatorHom_tau_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorHom X Y Z τ s).tau_comp =
      Matrix.reindex (leftTauFusionPathFinEquiv X Y Z)
        (rightTauFusionPathFinEquiv X Y Z)
        (tauFusionPathMatrix X Y Z τ s) := rfl

@[simp] theorem fibonacciAssociatorInv_unit_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorInv X Y Z τ s).unit_comp =
      Matrix.transpose (unitFusionPathMatrixTransport X Y Z) := rfl

@[simp] theorem fibonacciAssociatorInv_tau_comp
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    (fibonacciAssociatorInv X Y Z τ s).tau_comp =
      Matrix.transpose
        (Matrix.reindex (leftTauFusionPathFinEquiv X Y Z)
          (rightTauFusionPathFinEquiv X Y Z)
          (tauFusionPathMatrix X Y Z τ s)) := rfl

end InfoGeometry.Categorical.FibonacciGlobalAssociator
