import Mathlib.Data.Finsupp.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace InfoGeometry.Categorical.FibonacciBraidedCategory

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

/-- The Fibonacci fusion product is associative on formal sums of simple
objects. -/
theorem fibTensorObj_assoc (X Y Z : FibCat) :
    fibTensorObj (fibTensorObj X Y) Z =
      fibTensorObj X (fibTensorObj Y Z) := by
  ext s
  cases s <;> simp [fibTensorObj] <;> ring

/-- The formal vacuum object is a left unit for the Fibonacci fusion product. -/
theorem fibTensorObj_unit_left (X : FibCat) :
    fibTensorObj fibTensorUnit X = X := by
  ext s
  cases s <;> simp [fibTensorObj, fibTensorUnit]

/-- The formal vacuum object is a right unit for the Fibonacci fusion product. -/
theorem fibTensorObj_unit_right (X : FibCat) :
    fibTensorObj X fibTensorUnit = X := by
  ext s
  cases s <;> simp [fibTensorObj, fibTensorUnit]

/-! ## Skeletal coherence isomorphisms

The object-level fusion equalities give canonical transport isomorphisms in
the explicit skeletal category.  These are equality transports; they do not
claim that the nontrivial Fibonacci `F`-matrix has been bundled as a
monoidal associator.
-/

noncomputable def fibAssociator (X Y Z : FibCat) :
    fibTensorObj (fibTensorObj X Y) Z ≅
      fibTensorObj X (fibTensorObj Y Z) :=
  CategoryTheory.eqToIso (fibTensorObj_assoc X Y Z)

noncomputable def fibLeftUnitor (X : FibCat) :
    fibTensorObj fibTensorUnit X ≅ X :=
  CategoryTheory.eqToIso (fibTensorObj_unit_left X)

noncomputable def fibRightUnitor (X : FibCat) :
    fibTensorObj X fibTensorUnit ≅ X :=
  CategoryTheory.eqToIso (fibTensorObj_unit_right X)

@[simp] theorem fibAssociator_hom (X Y Z : FibCat) :
    (fibAssociator X Y Z).hom =
      CategoryTheory.eqToHom (fibTensorObj_assoc X Y Z) := rfl

@[simp] theorem fibLeftUnitor_hom (X : FibCat) :
    (fibLeftUnitor X).hom =
      CategoryTheory.eqToHom (fibTensorObj_unit_left X) := rfl

@[simp] theorem fibRightUnitor_hom (X : FibCat) :
    (fibRightUnitor X).hom =
      CategoryTheory.eqToHom (fibTensorObj_unit_right X) := rfl

theorem fibAssociator_hom_inv_id (X Y Z : FibCat) :
    (fibAssociator X Y Z).hom ≫ (fibAssociator X Y Z).inv = 𝟙 _ :=
  (fibAssociator X Y Z).hom_inv_id

theorem fibLeftUnitor_hom_inv_id (X : FibCat) :
    (fibLeftUnitor X).hom ≫ (fibLeftUnitor X).inv = 𝟙 _ :=
  (fibLeftUnitor X).hom_inv_id

theorem fibRightUnitor_hom_inv_id (X : FibCat) :
    (fibRightUnitor X).hom ≫ (fibRightUnitor X).inv = 𝟙 _ :=
  (fibRightUnitor X).hom_inv_id

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

theorem reindex_mul
    {m n o m' n' o' : Type*} [Fintype n] [Fintype n']
    (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    Matrix.reindex eₘ eₒ (A * B) =
      Matrix.reindex eₘ eₙ A * Matrix.reindex eₙ eₒ B := by
  exact (Matrix.reindexLinearEquiv_mul ℂ ℂ eₘ eₙ eₒ A B).symm

@[simp]
theorem kron_mul
    {m₁ n₁ p₁ m₂ n₂ p₂ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B : Matrix (Fin n₁) (Fin p₁) ℂ)
    (C : Matrix (Fin m₂) (Fin n₂) ℂ)
    (D : Matrix (Fin n₂) (Fin p₂) ℂ) :
    kron (A * B) (C * D) = kron A C * kron B D := by
  unfold kron
  rw [← reindex_mul]
  congr 1
  exact Matrix.mul_kronecker_mul A B C D

@[simp]
theorem blockDiag2_mul
    {m₁ n₁ p₁ m₂ n₂ p₂ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B : Matrix (Fin n₁) (Fin p₁) ℂ)
    (C : Matrix (Fin m₂) (Fin n₂) ℂ)
    (D : Matrix (Fin n₂) (Fin p₂) ℂ) :
    blockDiag2 (A * B) (C * D) = blockDiag2 A C * blockDiag2 B D := by
  unfold blockDiag2
  rw [← reindex_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

@[simp]
theorem blockDiag3_mul
    {m₁ n₁ p₁ m₂ n₂ p₂ m₃ n₃ p₃ : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B₁ : Matrix (Fin n₁) (Fin p₁) ℂ)
    (A₂ : Matrix (Fin m₂) (Fin n₂) ℂ)
    (B₂ : Matrix (Fin n₂) (Fin p₂) ℂ)
    (A₃ : Matrix (Fin m₃) (Fin n₃) ℂ)
    (B₃ : Matrix (Fin n₃) (Fin p₃) ℂ) :
    blockDiag3 (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) =
      blockDiag3 A₁ A₂ A₃ * blockDiag3 B₁ B₂ B₃ := by
  simp [blockDiag3]

noncomputable def fibTensorHom {X₁ X₂ Y₁ Y₂ : FibCat} (f : FibHom X₁ X₂) (g : FibHom Y₁ Y₂) : FibHom (fibTensorObj X₁ Y₁) (fibTensorObj X₂ Y₂) where
  unit_comp := Matrix.reindex
    (Equiv.cast (by simp [fibTensorObj]))
    (Equiv.cast (by simp [fibTensorObj]))
    (blockDiag2 (kron f.unit_comp g.unit_comp) (kron f.tau_comp g.tau_comp))
  tau_comp := Matrix.reindex
    (Equiv.cast (by simp [fibTensorObj]))
    (Equiv.cast (by simp [fibTensorObj]))
    (blockDiag3 (kron f.unit_comp g.tau_comp) (kron f.tau_comp g.unit_comp) (kron f.tau_comp g.tau_comp))

@[simp]
theorem fibTensorHom_id (X Y : FibCat) :
    fibTensorHom (FibHom.id X) (FibHom.id Y) =
      FibHom.id (fibTensorObj X Y) := by
  ext <;>
    simp [fibTensorHom, FibHom.id, fibTensorObj, blockDiag2, blockDiag3, kron]

@[simp]
theorem fibTensorHom_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : FibCat}
    (f₁ : FibHom X₁ X₂) (f₂ : FibHom X₂ X₃)
    (g₁ : FibHom Y₁ Y₂) (g₂ : FibHom Y₂ Y₃) :
    fibTensorHom (FibHom.comp f₁ f₂) (FibHom.comp g₁ g₂) =
      FibHom.comp (fibTensorHom f₁ g₁) (fibTensorHom f₂ g₂) := by
  ext <;>
    simp [fibTensorHom, FibHom.comp]

theorem fibTensorHom_left_eqToHom
    {X₁ X₂ Y : FibCat} (hX : X₁ = X₂) :
    fibTensorHom (CategoryTheory.eqToHom hX) (FibHom.id Y) =
      CategoryTheory.eqToHom (congrArg (fun X => fibTensorObj X Y) hX) := by
  cases hX
  change fibTensorHom (FibHom.id X₁) (FibHom.id Y) = FibHom.id (fibTensorObj X₁ Y)
  exact fibTensorHom_id X₁ Y

theorem fibTensorHom_right_eqToHom
    {X Y₁ Y₂ : FibCat} (hY : Y₁ = Y₂) :
    fibTensorHom (FibHom.id X) (CategoryTheory.eqToHom hY) =
      CategoryTheory.eqToHom (congrArg (fun Y => fibTensorObj X Y) hY) := by
  cases hY
  change fibTensorHom (FibHom.id X) (FibHom.id Y₁) = FibHom.id (fibTensorObj X Y₁)
  exact fibTensorHom_id X Y₁

theorem fibAssociator_pentagon (W X Y Z : FibCat) :
    (fibAssociator (fibTensorObj W X) Y Z).hom ≫
        (fibAssociator W X (fibTensorObj Y Z)).hom =
      (fibTensorHom (fibAssociator W X Y).hom (FibHom.id Z)) ≫
        (fibAssociator W (fibTensorObj X Y) Z).hom ≫
        (fibTensorHom (FibHom.id W) (fibAssociator X Y Z).hom) := by
  rw [fibAssociator_hom, fibAssociator_hom, fibAssociator_hom,
    fibAssociator_hom, fibAssociator_hom]
  rw [fibTensorHom_left_eqToHom (fibTensorObj_assoc W X Y)]
  rw [fibTensorHom_right_eqToHom (fibTensorObj_assoc X Y Z)]
  simp

theorem fibAssociator_triangle (X Y : FibCat) :
    (fibAssociator X fibTensorUnit Y).hom ≫
        (fibTensorHom (FibHom.id X) (fibLeftUnitor Y).hom) =
      fibTensorHom (fibRightUnitor X).hom (FibHom.id Y) := by
  rw [fibAssociator_hom, fibLeftUnitor_hom, fibRightUnitor_hom]
  rw [fibTensorHom_right_eqToHom (fibTensorObj_unit_left Y)]
  rw [fibTensorHom_left_eqToHom (fibTensorObj_unit_right X)]
  simp

noncomputable def fibWhiskerLeft (X : FibCat) {Y₁ Y₂ : FibCat} (f : FibHom Y₁ Y₂) : FibHom (fibTensorObj X Y₁) (fibTensorObj X Y₂) :=
  fibTensorHom (FibHom.id X) f

noncomputable def fibWhiskerRight {X₁ X₂ : FibCat} (f : FibHom X₁ X₂) (Y : FibCat) : FibHom (fibTensorObj X₁ Y) (fibTensorObj X₂ Y) :=
  fibTensorHom f (FibHom.id Y)

@[simp]
theorem fibWhiskerLeft_id (X Y : FibCat) :
    fibWhiskerLeft X (FibHom.id Y) = FibHom.id (fibTensorObj X Y) := by
  simp [fibWhiskerLeft]

@[simp]
theorem fibWhiskerRight_id (X Y : FibCat) :
    fibWhiskerRight (FibHom.id X) Y = FibHom.id (fibTensorObj X Y) := by
  simp [fibWhiskerRight]

@[simp]
theorem fibWhiskerLeft_comp
    (X : FibCat) {Y₁ Y₂ Y₃ : FibCat}
    (f : FibHom Y₁ Y₂) (g : FibHom Y₂ Y₃) :
    fibWhiskerLeft X (FibHom.comp f g) =
      FibHom.comp (fibWhiskerLeft X f) (fibWhiskerLeft X g) := by
  unfold fibWhiskerLeft
  calc
    fibTensorHom (FibHom.id X) (FibHom.comp f g) =
        fibTensorHom
          (FibHom.comp (FibHom.id X) (FibHom.id X))
          (FibHom.comp f g) := by
      apply congrArg (fun h => fibTensorHom h (FibHom.comp f g))
      ext <;> simp [FibHom.id, FibHom.comp]
    _ = FibHom.comp
          (fibTensorHom (FibHom.id X) f)
          (fibTensorHom (FibHom.id X) g) :=
      fibTensorHom_comp (FibHom.id X) (FibHom.id X) f g

@[simp]
theorem fibWhiskerRight_comp
    {X₁ X₂ X₃ : FibCat} (f : FibHom X₁ X₂) (g : FibHom X₂ X₃)
    (Y : FibCat) :
    fibWhiskerRight (FibHom.comp f g) Y =
      FibHom.comp (fibWhiskerRight f Y) (fibWhiskerRight g Y) := by
  unfold fibWhiskerRight
  calc
    fibTensorHom (FibHom.comp f g) (FibHom.id Y) =
        fibTensorHom
          (FibHom.comp f g)
          (FibHom.comp (FibHom.id Y) (FibHom.id Y)) := by
      apply congrArg (fibTensorHom (FibHom.comp f g))
      ext <;> simp [FibHom.id, FibHom.comp]
    _ = FibHom.comp
          (fibTensorHom f (FibHom.id Y))
          (fibTensorHom g (FibHom.id Y)) :=
      fibTensorHom_comp f g (FibHom.id Y) (FibHom.id Y)

/-- Left tensoring by a Fibonacci object, expressed as a native Mathlib functor. -/
noncomputable def fibTensorLeftFunctor (X : FibCat) : FibCat ⥤ FibCat where
  obj Y := fibTensorObj X Y
  map f := fibWhiskerLeft X f
  map_id Y := fibWhiskerLeft_id X Y
  map_comp f g := fibWhiskerLeft_comp X f g

/-- Right tensoring by a Fibonacci object, expressed as a native Mathlib functor. -/
noncomputable def fibTensorRightFunctor (Y : FibCat) : FibCat ⥤ FibCat where
  obj X := fibTensorObj X Y
  map f := fibWhiskerRight f Y
  map_id X := fibWhiskerRight_id X Y
  map_comp f g := fibWhiskerRight_comp f g Y

theorem fibTensor_interchange
    {X₁ X₂ Y₁ Y₂ : FibCat}
    (f : FibHom X₁ X₂) (g : FibHom Y₁ Y₂) :
    FibHom.comp
        (fibWhiskerLeft X₁ g)
        (fibWhiskerRight f Y₂) =
      FibHom.comp
        (fibWhiskerRight f Y₁)
        (fibWhiskerLeft X₂ g) := by
  unfold fibWhiskerLeft fibWhiskerRight
  calc
    FibHom.comp
        (fibTensorHom (FibHom.id X₁) g)
        (fibTensorHom f (FibHom.id Y₂)) =
      fibTensorHom
        (FibHom.comp (FibHom.id X₁) f)
        (FibHom.comp g (FibHom.id Y₂)) :=
      (fibTensorHom_comp (FibHom.id X₁) f g (FibHom.id Y₂)).symm
    _ = fibTensorHom f g := by
      congr 1 <;> ext <;> simp [FibHom.id, FibHom.comp]
    _ = fibTensorHom
        (FibHom.comp f (FibHom.id X₂))
        (FibHom.comp (FibHom.id Y₁) g) := by
      congr 1 <;> ext <;> simp [FibHom.id, FibHom.comp]
    _ = FibHom.comp
        (fibTensorHom f (FibHom.id Y₁))
        (fibTensorHom (FibHom.id X₂) g) :=
      fibTensorHom_comp f (FibHom.id X₂) (FibHom.id Y₁) g

/-- A morphism in the first variable induces a natural transformation between
the corresponding left-tensoring functors. -/
noncomputable def fibTensorNatTrans
    {X₁ X₂ : FibCat} (f : FibHom X₁ X₂) :
    fibTensorLeftFunctor X₁ ⟶ fibTensorLeftFunctor X₂ where
  app Y := fibWhiskerRight f Y
  naturality _ _ g := fibTensor_interchange f g

/-- Tensor product on Fibonacci objects and morphisms as a genuine Mathlib
bifunctor, curried through the functor category. -/
noncomputable def fibTensorBifunctor : FibCat ⥤ (FibCat ⥤ FibCat) where
  obj X := fibTensorLeftFunctor X
  map f := fibTensorNatTrans f
  map_id X := by
    ext Y
    exact fibWhiskerRight_id X Y
  map_comp f g := by
    ext Y
    exact fibWhiskerRight_comp f g Y

/-!
## Remaining closure debt

This file is verified scaffolding only; no `MonoidalCategory`/`BraidedCategory`
instance is declared.

Exact kernel-checked lemmas still owed before full monoidal closure:
- TODO: associator unit/tau block lemmas from `MTC_FusionMatrix`
- TODO: pentagon/triangle proofs as `FibHom.ext` calc chains
- TODO: braiding naturality `right/left` as `FibHom.ext` simp calc
- TODO: hexagon forward/reverse as `FibHom.ext` block calc
-/

end InfoGeometry.Categorical.FibonacciBraidedCategory
