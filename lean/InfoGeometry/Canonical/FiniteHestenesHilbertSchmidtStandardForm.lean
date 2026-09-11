import InfoGeometry.Canonical.HestenesHermitianMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteHestenesModularOperator
import Mathlib.Algebra.Star.Module

/-!
# Finite Hilbert--Schmidt standard form for the Hestenes algebra

This owner upgrades matrix adjunction from an additive involution to its
native complex star-semilinear form, proves the Hilbert--Schmidt antiunitarity
identity, and identifies the commutant of all left regular actions with the
right regular actions.
-/

noncomputable section
namespace FiniteHestenesHilbertSchmidtStandardForm

open HestenesPauliSheetBridge HestenesEvenPauliEquiv
open FiniteHestenesTomitaBridge HestenesHermitianMatrixBridge
open HestenesCl14 HestenesHermitianAdjoint

abbrev HS2 := FiniteHestenesTomitaBridge.HS2
abbrev HSEnd := HS2 →ₗ[ℂ] HS2

/-- Tomita conjugation as a native conjugate-linear equivalence. -/
def matrixTomitaSemilinearEquiv : HS2 ≃ₗ⋆[ℂ] HS2 :=
  starLinearEquiv ℂ

@[simp] theorem matrixTomitaSemilinearEquiv_apply (X : HS2) :
    matrixTomitaSemilinearEquiv X = matrixTomita X := by
  rfl

@[simp] theorem matrixTomita_smul (z : ℂ) (X : HS2) :
    matrixTomita (z • X) = star z • matrixTomita X := by
  change star (z • X) = star z • star X
  exact star_smul z X

/-- The Hilbert--Schmidt pairing, conjugate-linear in the first variable. -/
def hilbertSchmidtInner (X Y : HS2) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, star (X i j) * Y i j

@[simp] theorem hilbertSchmidtInner_zero_left (Y : HS2) :
    hilbertSchmidtInner 0 Y = 0 := by
  simp [hilbertSchmidtInner]

@[simp] theorem hilbertSchmidtInner_add_left (X Y Z : HS2) :
    hilbertSchmidtInner (X + Y) Z =
      hilbertSchmidtInner X Z + hilbertSchmidtInner Y Z := by
  simp [hilbertSchmidtInner, Fin.sum_univ_two]
  ring

@[simp] theorem hilbertSchmidtInner_smul_left (z : ℂ) (X Y : HS2) :
    hilbertSchmidtInner (z • X) Y =
      star z * hilbertSchmidtInner X Y := by
  simp [hilbertSchmidtInner, Fin.sum_univ_two]
  ring

@[simp] theorem hilbertSchmidtInner_add_right (X Y Z : HS2) :
    hilbertSchmidtInner X (Y + Z) =
      hilbertSchmidtInner X Y + hilbertSchmidtInner X Z := by
  simp [hilbertSchmidtInner, Fin.sum_univ_two]
  ring

@[simp] theorem hilbertSchmidtInner_smul_right (z : ℂ) (X Y : HS2) :
    hilbertSchmidtInner X (z • Y) =
      z * hilbertSchmidtInner X Y := by
  simp [hilbertSchmidtInner, Fin.sum_univ_two]
  ring

/-- The standard-form conjugation is antiunitary for the Hilbert--Schmidt pairing. -/
theorem matrixTomita_antiunitary (X Y : HS2) :
    hilbertSchmidtInner (matrixTomita X) (matrixTomita Y) =
      star (hilbertSchmidtInner X Y) := by
  simp [hilbertSchmidtInner, matrixTomita, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]
  ring

def leftActionLinear (A : HS2) : HSEnd where
  toFun X := A * X
  map_add' X Y := Matrix.mul_add A X Y
  map_smul' z X := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

def rightActionLinear (B : HS2) : HSEnd where
  toFun X := X * B
  map_add' X Y := Matrix.add_mul X Y B
  map_smul' z X := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[simp] theorem leftActionLinear_apply (A X : HS2) :
    leftActionLinear A X = A * X := rfl

@[simp] theorem rightActionLinear_apply (B X : HS2) :
    rightActionLinear B X = X * B := rfl

def LeftCommutant : Set HSEnd :=
  {F | ∀ A : HS2,
    F.comp (leftActionLinear A) = (leftActionLinear A).comp F}

def RightRegular : Set HSEnd := Set.range rightActionLinear

theorem rightAction_mem_leftCommutant (B : HS2) :
    rightActionLinear B ∈ LeftCommutant := by
  intro A
  apply LinearMap.ext
  intro X
  simp [LinearMap.comp_apply, Matrix.mul_assoc]

theorem leftCommutant_eq_rightRegular : LeftCommutant = RightRegular := by
  ext F
  constructor
  · intro hF
    refine ⟨F 1, ?_⟩
    apply LinearMap.ext
    intro X
    have hcomm := LinearMap.congr_fun (hF X) 1
    simpa [LinearMap.comp_apply] using hcomm.symm
  · rintro ⟨B, rfl⟩
    exact rightAction_mem_leftCommutant B

/-- Pulling matrix Tomita back through the Pauli equivalence gives exactly
the native Hestenes Hermitian adjoint. -/
theorem hestenesAdjoint_standardForm (x : HestenesCl14.ClPlus14) :
    hestenesAdjoint x = cliffordTomita x :=
  hestenesAdjoint_eq_cliffordTomita x

theorem hilbertSchmidt_standardForm_packet :
    (∀ z : ℂ, ∀ X : HS2,
      matrixTomita (z • X) = star z • matrixTomita X) ∧
    (∀ X Y : HS2,
      hilbertSchmidtInner (matrixTomita X) (matrixTomita Y) =
        star (hilbertSchmidtInner X Y)) ∧
    LeftCommutant = RightRegular :=
  ⟨matrixTomita_smul, matrixTomita_antiunitary,
    leftCommutant_eq_rightRegular⟩

end FiniteHestenesHilbertSchmidtStandardForm
end noncomputable section
