/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AtiyahBottShapiroSymbol
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of the actual finite-dimensional ABS symbol

The forward symbol is a continuous family of continuous linear maps. On the
negative unit level set the inverse is the opposite Clifford multiplication,
and is continuous in the same operator topology. These are actual maps on the
grading subspaces, not scalar determinant witnesses. No vector-bundle or K-theory
quotient is introduced by this continuity result alone.
-/

noncomputable section
namespace InfoGeometry.Canonical.AtiyahBottShapiroSymbolContinuity
open CliffordAlgebra PinOperatorFamilyBridge AtiyahBottShapiroSymbol

section LinearFamilies
variable {M W : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup W] [Module ℝ W]
variable {Q : QuadraticForm ℝ M}
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := W) (Q := Q))

/-- The symbol depends linearly on its Clifford-vector parameter. -/
def symbolFamily : M →ₗ[ℝ] (oddSpace ρ →ₗ[ℝ] evenSpace ρ) where
  toFun := symbol ρ
  map_add' v u := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [symbol, map_add, add_comm]
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [symbol, map_smul]

/-- On `Q(v)=-1`, this reverse Clifford multiplication is the inverse symbol. -/
def inverseUnitSymbol (v : M) : evenSpace ρ →ₗ[ℝ] oddSpace ρ where
  toFun w := ⟨ρ.representation (ι Q v) w, generator_mem_oddSpace ρ v w.property⟩
  map_add' x y := by apply Subtype.ext; exact (ρ.representation (ι Q v)).map_add x y
  map_smul' r x := by apply Subtype.ext; exact (ρ.representation (ι Q v)).map_smul r x

@[simp] theorem inverseUnitSymbol_apply (v : M) (w : evenSpace ρ) :
    (inverseUnitSymbol ρ v w : W) = ρ.representation (ι Q v) w := rfl

def inverseUnitSymbolFamily : M →ₗ[ℝ] (evenSpace ρ →ₗ[ℝ] oddSpace ρ) where
  toFun := inverseUnitSymbol ρ
  map_add' v u := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [inverseUnitSymbol, map_add]
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [inverseUnitSymbol, map_smul]

end LinearFamilies

section ContinuousFamilies
variable {M W : Type*}
variable [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable {Q : QuadraticForm ℝ M}
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := W) (Q := Q))

/-- The actual forward symbol with its finite-dimensional boundedness proof. -/
def continuousSymbol (v : M) : oddSpace ρ →L[ℝ] evenSpace ρ :=
  (symbol ρ v).toContinuousLinearMap

/-- The actual reverse Clifford map with its boundedness proof. -/
def continuousInverseUnitSymbol (v : M) : evenSpace ρ →L[ℝ] oddSpace ρ :=
  (inverseUnitSymbol ρ v).toContinuousLinearMap

/-- Norm-topology continuity of the full forward operator family. -/
theorem continuous_continuousSymbol : Continuous (continuousSymbol ρ) := by
  let f : M →ₗ[ℝ] (oddSpace ρ →L[ℝ] evenSpace ρ) :=
    (LinearMap.toContinuousLinearMap :
      (oddSpace ρ →ₗ[ℝ] evenSpace ρ) ≃ₗ[ℝ]
        (oddSpace ρ →L[ℝ] evenSpace ρ)).toLinearMap.comp (symbolFamily ρ)
  exact f.continuous_of_finiteDimensional

/-- Norm-topology continuity of the reverse operator family. -/
theorem continuous_continuousInverseUnitSymbol : Continuous (continuousInverseUnitSymbol ρ) := by
  let f : M →ₗ[ℝ] (evenSpace ρ →L[ℝ] oddSpace ρ) :=
    (LinearMap.toContinuousLinearMap :
      (evenSpace ρ →ₗ[ℝ] oddSpace ρ) ≃ₗ[ℝ]
        (evenSpace ρ →L[ℝ] oddSpace ρ)).toLinearMap.comp (inverseUnitSymbolFamily ρ)
  exact f.continuous_of_finiteDimensional

/-- The negative quadratic unit sphere with its inherited topology. -/
abbrev NegativeUnitSphere (Q : QuadraticForm ℝ M) := {v : M // Q v = -1}

/-- A continuous family of the exact invertible symbols on the unit sphere. -/
theorem continuous_symbol_on_negativeUnitSphere :
    Continuous (fun v : NegativeUnitSphere Q => continuousSymbol ρ v.val) :=
  (continuous_continuousSymbol ρ).comp continuous_subtype_val

/-- The inverse of the algebraic symbol is exactly the continuous reverse family. -/
theorem inverseSymbol_eq_inverseUnitSymbol (v : NegativeUnitSphere Q) :
    inverseSymbol ρ v.val = inverseUnitSymbol ρ v.val := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  simp [inverseSymbol_apply, inverseUnitSymbol_apply, v.property]

/-- The actual inverse symbols are continuous in operator norm on the sphere. -/
theorem continuous_inverseSymbol_on_negativeUnitSphere :
    Continuous (fun v : NegativeUnitSphere Q =>
      (inverseSymbol ρ v.val).toContinuousLinearMap) := by
  have h : (fun v : NegativeUnitSphere Q => (inverseSymbol ρ v.val).toContinuousLinearMap) =
      (fun v : NegativeUnitSphere Q => continuousInverseUnitSymbol ρ v.val) := by
    funext v
    rw [inverseSymbol_eq_inverseUnitSymbol]
    rfl
  rw [h]
  exact (continuous_continuousInverseUnitSymbol ρ).comp continuous_subtype_val

end ContinuousFamilies
end InfoGeometry.Canonical.AtiyahBottShapiroSymbolContinuity
