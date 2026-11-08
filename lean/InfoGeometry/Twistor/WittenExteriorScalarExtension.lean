/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WittenCl55ExteriorBridge
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Explicit real-to-complex comparison for the four exterior modes

The coordinate inclusion `ℝ⁴ → ℂ⁴` induces a unital real algebra
homomorphism between the two native exterior algebras. It intertwines their
actual Euler operators and hence their real and complex helicity operators.
This supplies a concrete coefficient comparison for the real Cl(5,5) bridge.

The map is not asserted to be a complex algebra isomorphism or a scalar-
extension equivalence. The real source and the complex target remain distinct
types, with restriction of scalars displayed in the generator construction.
-/

noncomputable section

namespace InfoGeometry.Twistor.WittenExteriorScalarExtension

open InfoGeometry.Twistor.WittenExteriorHelicity
open InfoGeometry.Twistor.WittenCl55ExteriorBridge

/-- The coordinate-wise canonical scalar inclusion. -/
def realFourToComplex : (Fin 4 → ℝ) →ₗ[ℝ] FourModeSpace where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

@[simp] theorem realFourToComplex_apply (v : Fin 4 → ℝ) (i : Fin 4) :
    realFourToComplex v i = (v i : ℂ) := rfl

theorem realFourToComplex_injective : Function.Injective realFourToComplex := by
  intro v w h
  funext i
  exact Complex.ofReal_injective (congrArg (fun z : FourModeSpace => z i) h)

/-- The native exterior universal property, with the target restricted to `ℝ`. -/
def realToComplexFourForms :
    ExteriorAlgebra ℝ (Fin 4 → ℝ) →ₐ[ℝ] FourModeForms :=
  ExteriorAlgebra.lift ℝ
    ⟨((ExteriorAlgebra.ι ℂ).restrictScalars ℝ).comp realFourToComplex,
      fun v => ExteriorAlgebra.ι_sq_zero (R := ℂ) (realFourToComplex v)⟩

@[simp] theorem realToComplexFourForms_generator (v : Fin 4 → ℝ) :
    realToComplexFourForms (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℂ (realFourToComplex v) :=
  ExteriorAlgebra.lift_ι_apply ℝ _ _ v

/-- The genuine number operator commutes with coefficient extension on every form. -/
theorem realToComplexFourForms_euler (ψ : ExteriorAlgebra ℝ (Fin 4 → ℝ)) :
    exteriorEuler ℂ 4 (realToComplexFourForms ψ) =
      realToComplexFourForms (exteriorEuler ℝ 4 ψ) := by
  induction ψ using CliffordAlgebra.left_induction with
  | algebraMap r =>
      have hφ : realToComplexFourForms
          (r • (1 : ExteriorAlgebra ℝ (Fin 4 → ℝ))) =
          r • realToComplexFourForms (1 : ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
        realToComplexFourForms.toLinearMap.map_smul r
          (1 : ExteriorAlgebra ℝ (Fin 4 → ℝ))
      have hComplex : exteriorEuler ℂ 4 (r • (1 : FourModeForms)) =
          r • exteriorEuler ℂ 4 (1 : FourModeForms) :=
        ((exteriorEuler ℂ 4).restrictScalars ℝ).map_smul r (1 : FourModeForms)
      have hReal : exteriorEuler ℝ 4
          (r • (1 : ExteriorAlgebra ℝ (Fin 4 → ℝ))) =
          r • exteriorEuler ℝ 4 (1 : ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
        (exteriorEuler ℝ 4).map_smul r (1 : ExteriorAlgebra ℝ (Fin 4 → ℝ))
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [hφ, map_one, hComplex, hReal]
      simp only [exteriorEuler_one, smul_zero, map_zero]
      exact (smul_zero r : r • (0 : FourModeForms) = 0)
  | add ψ χ hψ hχ =>
      simp only [map_add, hψ, hχ]
  | ι_mul ψ v hψ =>
      change exteriorEuler ℂ 4
          (realToComplexFourForms (ExteriorAlgebra.ι ℝ v * ψ)) =
        realToComplexFourForms (exteriorEuler ℝ 4 (ExteriorAlgebra.ι ℝ v * ψ))
      simp only [map_mul, realToComplexFourForms_generator,
        exteriorEuler_generator_mul, map_add, hψ]

/-- The real native-number normalization feeds the same complex helicity formula. -/
theorem realToComplexFourForms_helicity (ψ : ExteriorAlgebra ℝ (Fin 4 → ℝ)) :
    realToComplexFourForms (realFermionicHelicity ψ) =
      fermionicHelicity (realToComplexFourForms ψ) := by
  have hφ : realToComplexFourForms ((1 / 2 : ℝ) • exteriorEuler ℝ 4 ψ) =
      (1 / 2 : ℝ) • realToComplexFourForms (exteriorEuler ℝ 4 ψ) :=
    realToComplexFourForms.toLinearMap.map_smul (1 / 2 : ℝ) (exteriorEuler ℝ 4 ψ)
  have hCoefficient (x : FourModeForms) :
      (1 / 2 : ℝ) • x = (1 / 2 : ℂ) • x := by
    calc
      (1 / 2 : ℝ) • x = (algebraMap ℝ ℂ (1 / 2 : ℝ)) • x :=
        (algebraMap_smul ℂ (1 / 2 : ℝ) x).symm
      _ = (1 / 2 : ℂ) • x := by norm_num
  calc
    realToComplexFourForms (realFermionicHelicity ψ) =
        realToComplexFourForms ψ -
          (1 / 2 : ℝ) • realToComplexFourForms (exteriorEuler ℝ 4 ψ) := by
      change realToComplexFourForms (ψ - (1 / 2 : ℝ) • exteriorEuler ℝ 4 ψ) = _
      rw [map_sub, hφ]
    _ = realToComplexFourForms ψ -
        (1 / 2 : ℝ) • exteriorEuler ℂ 4 (realToComplexFourForms ψ) := by
      rw [realToComplexFourForms_euler ψ]
    _ = realToComplexFourForms ψ -
        (1 / 2 : ℂ) • exteriorEuler ℂ 4 (realToComplexFourForms ψ) := by
      rw [hCoefficient]
    _ = fermionicHelicity (realToComplexFourForms ψ) := rfl

end InfoGeometry.Twistor.WittenExteriorScalarExtension
