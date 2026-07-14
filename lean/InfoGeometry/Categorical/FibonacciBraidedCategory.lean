import Mathlib.Data.Finsupp.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import InfoGeometry.Categorical.FibonacciFusionCategoryData
import InfoGeometry.Categorical.MTC_PentagonTriangle
import InfoGeometry.Categorical.FibonacciHomSpace

/-!
# Fibonacci Braided Category

This module initiates the formal implementation of the mathlib `BraidedCategory` 
instance for the Fibonacci fusion category, leveraging the verified finite matrix 
readouts (the pentagon and hexagon coherences) from `MTC_PentagonTriangle.lean`.

Since the full `MonoidalCategory` data requires constructing the finite
Hom-spaces for fusion trees, this file only exposes checked tensor-object and
block-matrix ingredients. It deliberately does not emit a `MonoidalCategory` or
`BraidedCategory` instance.
-/

namespace FibonacciBraidedCategory

open CategoryTheory
open CategoryTheory.MonoidalCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.MTC_PentagonTriangle
open InfoGeometry.Categorical.FibonacciHomSpace

-- We need an underlying category to host the braiding.
-- Because τ ⊗ τ = 𝟙 ⊕ τ, the objects cannot just be the simple labels.
-- We define the objects as formal direct sums (multiplicities) of simple labels.
-- (This relies on `FibCat` and its `Category` instance from `FibonacciHomSpace`)

/-- 
The tensor product of two formal sums follows the Fibonacci fusion rules:
(X ⊗ Y)_unit = X_unit * Y_unit + X_tau * Y_tau
(X ⊗ Y)_tau = X_unit * Y_tau + X_tau * Y_unit + X_tau * Y_tau
-/
noncomputable def fibTensorObj (X Y : FibCat) : FibCat :=
  Finsupp.single FibSimple.unit (X FibSimple.unit * Y FibSimple.unit + X FibSimple.tau * Y FibSimple.tau) +
  Finsupp.single FibSimple.tau (X FibSimple.unit * Y FibSimple.tau + X FibSimple.tau * Y FibSimple.unit + X FibSimple.tau * Y FibSimple.tau)

/-- The tensor unit is exactly 1 copy of the simple label `𝟙`. -/
noncomputable def fibTensorUnit : FibCat :=
  Finsupp.single FibSimple.unit 1

@[simp] theorem fibTensorObj_apply_unit (X Y : FibCat) :
    fibTensorObj X Y FibSimple.unit =
      X FibSimple.unit * Y FibSimple.unit + X FibSimple.tau * Y FibSimple.tau := by
  simp [fibTensorObj]

@[simp] theorem fibTensorObj_apply_tau (X Y : FibCat) :
    fibTensorObj X Y FibSimple.tau =
      X FibSimple.unit * Y FibSimple.tau +
        X FibSimple.tau * Y FibSimple.unit +
          X FibSimple.tau * Y FibSimple.tau := by
  simp [fibTensorObj]

@[simp] theorem fibTensorUnit_apply_unit :
    fibTensorUnit FibSimple.unit = 1 := by
  simp [fibTensorUnit]

@[simp] theorem fibTensorUnit_apply_tau :
    fibTensorUnit FibSimple.tau = 0 := by
  simp [fibTensorUnit]

/-- 
Open Debt: The MonoidalCategory instance.
The tensor product of objects is defined via `fusionMultiplicity`.
The associator `α_` is constructed from the verified `MTC_FusionMatrix` (F-matrix).
-/
noncomputable def blockDiag2 {α : Type} [Zero α] {m₁ n₁ m₂ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) α) (B : Matrix (Fin m₂) (Fin n₂) α) :
  Matrix (Fin (m₁ + m₂)) (Fin (n₁ + n₂)) α :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

noncomputable def blockDiag3 {α : Type} [Zero α] {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ}
  (A : Matrix (Fin m₁) (Fin n₁) α) (B : Matrix (Fin m₂) (Fin n₂) α) (C : Matrix (Fin m₃) (Fin n₃) α) :
  Matrix (Fin (m₁ + m₂ + m₃)) (Fin (n₁ + n₂ + n₃)) α :=
  blockDiag2 (blockDiag2 A B) C

noncomputable def kron {m₁ n₁ m₂ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) ℂ) (B : Matrix (Fin m₂) (Fin n₂) ℂ) :
  Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker A B)

noncomputable def fibTensorHom {X₁ X₂ Y₁ Y₂ : FibCat} (f : FibHom X₁ X₂) (g : FibHom Y₁ Y₂) : FibHom (fibTensorObj X₁ Y₁) (fibTensorObj X₂ Y₂) where
  unit_comp := Matrix.reindex
    (Equiv.cast (by simp [fibTensorObj]))
    (Equiv.cast (by simp [fibTensorObj]))
    (blockDiag2 (kron f.unit_comp g.unit_comp) (kron f.tau_comp g.tau_comp))
  tau_comp := Matrix.reindex
    (Equiv.cast (by simp [fibTensorObj]))
    (Equiv.cast (by simp [fibTensorObj]))
    (blockDiag3 (kron f.unit_comp g.tau_comp) (kron f.tau_comp g.unit_comp) (kron f.tau_comp g.tau_comp))

noncomputable def fibWhiskerLeft (X : FibCat) {Y₁ Y₂ : FibCat} (f : FibHom Y₁ Y₂) : FibHom (fibTensorObj X Y₁) (fibTensorObj X Y₂) :=
  fibTensorHom (FibHom.id X) f

noncomputable def fibWhiskerRight {X₁ X₂ : FibCat} (f : FibHom X₁ X₂) (Y : FibCat) : FibHom (fibTensorObj X₁ Y) (fibTensorObj X₂ Y) :=
  fibTensorHom f (FibHom.id Y)

/-
No mathlib `MonoidalCategory` or `BraidedCategory` instance is declared in this
file. The remaining construction requires explicit associator/unitors, naturality
proofs, and pentagon/hexagon coherence for the full `FibCat` Hom-spaces.
-/

end FibonacciBraidedCategory
