import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Module.Basic

/-!
# Krein-Clifford Cl(1,1) Foundations

This module implements the canonical doubled space and the Cl(1,1)
algebraic relations required for chiral self-reflection.
Using LinearMap to avoid topological instance complexities.
-/

namespace SelfReference

section KreinClifford

variable {E : Type _} [AddCommGroup E] [Module ℝ E]

/-- The canonical doubled space E ⊕ E. -/
abbrev DoubledSpace (E : Type _) := E × E

/-- The modular swap involution J: (x,y) ↦ (y,x). -/
def modularJ : DoubledSpace E →ₗ[ℝ] DoubledSpace E where
  toFun v := (v.2, v.1)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- The spectral sign involution ε: (x,y) ↦ (x,-y). -/
def spectralEpsilon : DoubledSpace E →ₗ[ℝ] DoubledSpace E where
  toFun v := (v.1, -v.2)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' r x := by ext <;> simp

/-- The complex structure I = J ∘ ε mapping (x,y) ↦ (-y, x). -/
def complexI : DoubledSpace E →ₗ[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

/-- Pointwise formula for `modularJ`. -/
@[simp] lemma modularJ_apply (v : DoubledSpace E) :
    modularJ v = (v.2, v.1) := rfl

/-- Pointwise formula for `spectralEpsilon`. -/
@[simp] lemma spectralEpsilon_apply (v : DoubledSpace E) :
    spectralEpsilon v = (v.1, -v.2) := rfl

/-- Pointwise formula for `complexI`. -/
@[simp] lemma complexI_apply (v : DoubledSpace E) :
    complexI v = (-v.2, v.1) := by
  simp [complexI]

/-- `modularJ` is an involution. -/
lemma modularJ_involution :
    modularJ.comp modularJ = (LinearMap.id : DoubledSpace E →ₗ[ℝ] DoubledSpace E) := by
  apply LinearMap.ext
  intro v
  rfl

/-- `spectralEpsilon` is an involution. -/
lemma spectralEpsilon_involution :
    spectralEpsilon.comp spectralEpsilon =
      (LinearMap.id : DoubledSpace E →ₗ[ℝ] DoubledSpace E) := by
  apply LinearMap.ext
  intro v
  ext <;> simp [spectralEpsilon]

/-- `complexI` squares to `-id`. -/
lemma complexI_sq :
    complexI.comp complexI = -(LinearMap.id : DoubledSpace E →ₗ[ℝ] DoubledSpace E) := by
  apply LinearMap.ext
  intro v
  ext <;> simp [complexI]

end KreinClifford

end SelfReference
