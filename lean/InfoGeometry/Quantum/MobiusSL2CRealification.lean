import InfoGeometry.Quantum.MobiusRealCotangentLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Realified `SL(2,ℂ)` carrier action

This owner makes the missing realification datum explicit.  A concrete
identification `(Fin 2 → ℂ) ≃ₗ[ℝ] Vector 4` can be supplied later; the
cotangent representation and its form-preservation laws are derived here
without identifying complex matrices with raw Zorn multiplication.
-/

namespace InfoGeometry.Quantum.MobiusSL2CRealification

open InfoGeometry.Quantum.DualFlatKreinGraph
open InfoGeometry.Quantum.MobiusRealCotangentLift

abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

structure Realification where
  toLinear : SL2C → Vector 4 ≃ₗ[ℝ] Vector 4
  map_one : toLinear 1 = LinearEquiv.refl ℝ (Vector 4)
  map_mul : ∀ g h, toLinear (g * h) = (toLinear h).trans (toLinear g)

def complexVectorToRealPi : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun z := ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  map_add' z w := by
    ext i
    fin_cases i <;> simp
  map_smul' c z := by
    ext i
    fin_cases i <;> simp

def realPiToComplexVector : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun x := ![x 0 + x 1 * Complex.I, x 2 + x 3 * Complex.I]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_mul] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

noncomputable def complexVectorRealEquiv : (Fin 2 → ℂ) ≃ₗ[ℝ] Vector 4 :=
  LinearEquiv.ofLinear
    ((EuclideanSpace.equiv (Fin 4) ℝ).symm.toLinearMap.comp complexVectorToRealPi)
    (realPiToComplexVector.comp (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv.toLinearMap)
    (by
      apply LinearMap.ext
      intro z
      apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
      funext i
      fin_cases i <;> simp [complexVectorToRealPi, realPiToComplexVector,
        EuclideanSpace.equiv])
    (by
      apply LinearMap.ext
      intro x
      funext i
      fin_cases i <;> simp [complexVectorToRealPi, realPiToComplexVector,
        EuclideanSpace.equiv])

theorem complexVectorRealEquiv_apply (z : Fin 2 → ℂ) :
    complexVectorRealEquiv z =
      ![(z 0).re, (z 0).im, (z 1).re, (z 1).im] := by
  ext i
  fin_cases i <;> simp [complexVectorRealEquiv, complexVectorToRealPi,
    EuclideanSpace.equiv]

theorem complexVectorRealEquiv_symm_apply (x : Vector 4) :
    complexVectorRealEquiv.symm x =
      ![x 0 + x 1 * Complex.I, x 2 + x 3 * Complex.I] := by
  ext i
  fin_cases i <;> simp [complexVectorRealEquiv, realPiToComplexVector,
    EuclideanSpace.equiv]

noncomputable def realifiedSL2C (g : SL2C) : Vector 4 ≃ₗ[ℝ] Vector 4 :=
  (complexVectorRealEquiv.symm.trans
      (LinearEquiv.restrictScalars ℝ (Matrix.SpecialLinearGroup.toLin' g))).trans
    complexVectorRealEquiv

theorem realifiedSL2C_one :
    realifiedSL2C (1 : SL2C) = LinearEquiv.refl ℝ (Vector 4) := by
  ext x
  simp [realifiedSL2C]

theorem realifiedSL2C_mul (g h : SL2C) :
    realifiedSL2C (g * h) = (realifiedSL2C h).trans (realifiedSL2C g) := by
  ext x
  simp [realifiedSL2C, Matrix.SpecialLinearGroup.toLin']

def cotangentLift (ρ : Realification) (g : SL2C) : Carrier 4 → Carrier 4 :=
  lift (ρ.toLinear g)

theorem cotangentLift_one (ρ : Realification) (x : Carrier 4) :
    cotangentLift ρ 1 x = x := by
  rw [cotangentLift, ρ.map_one]
  exact lift_identity x

theorem cotangentLift_mul (ρ : Realification) (g h : SL2C) (x : Carrier 4) :
    cotangentLift ρ (g * h) x =
      cotangentLift ρ g (cotangentLift ρ h x) := by
  rw [cotangentLift, ρ.map_mul]
  exact lift_comp (ρ.toLinear h) (ρ.toLinear g) x

theorem cotangentLift_preserves_neutral (ρ : Realification)
    (g : SL2C) (x y : Carrier 4) :
    neutralPair (cotangentLift ρ g x) (cotangentLift ρ g y) = neutralPair x y := by
  exact lift_preserves_neutral (ρ.toLinear g) x y

theorem cotangentLift_preserves_symplectic (ρ : Realification)
    (g : SL2C) (x y : Carrier 4) :
    symplecticPair (cotangentLift ρ g x) (cotangentLift ρ g y) = symplecticPair x y := by
  exact lift_preserves_symplectic (ρ.toLinear g) x y

theorem cotangentLift_preserves_grading (ρ : Realification)
    (g : SL2C) (x : Carrier 4) :
    grading (cotangentLift ρ g x) = cotangentLift ρ g (grading x) := by
  exact lift_preserves_grading (ρ.toLinear g) x

noncomputable def canonicalRealification : Realification where
  toLinear := realifiedSL2C
  map_one := realifiedSL2C_one
  map_mul := realifiedSL2C_mul

theorem canonicalCotangentLift_preserves_neutral
    (g : SL2C) (x y : Carrier 4) :
    neutralPair (cotangentLift canonicalRealification g x)
      (cotangentLift canonicalRealification g y) = neutralPair x y := by
  exact cotangentLift_preserves_neutral canonicalRealification g x y

theorem canonicalCotangentLift_preserves_symplectic
    (g : SL2C) (x y : Carrier 4) :
    symplecticPair (cotangentLift canonicalRealification g x)
      (cotangentLift canonicalRealification g y) = symplecticPair x y := by
  exact cotangentLift_preserves_symplectic canonicalRealification g x y

end InfoGeometry.Quantum.MobiusSL2CRealification
