import InfoGeometry.Arithmetic.PrimeCyclotomicAmbientTower
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Directed-system maps for the six-prime cyclotomic field tower

This file upgrades the order-theoretic intermediate-field tower to actual
`ℚ`-algebra homomorphisms.  Since every stage is an `IntermediateField ℚ K∞`
and a directed path is only a proof of `i ≤ j`, Mathlib's native
`IntermediateField.inclusion` supplies the transition map.

The identity, composition, faithfulness, and path-independence laws are proved
without external certificates or new axioms.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCyclotomicFieldDirectedSystem

open InfoGeometry.Arithmetic.PrimeCyclotomicDirectedTower
open InfoGeometry.Arithmetic.PrimeCyclotomicAmbientTower

/-- Native transition map along a directed path in the prime tower. -/
def stageInclusion {i j : Fin 7} (p : DirectedPath i j) :
    fieldStage i →ₐ[ℚ] fieldStage j :=
  IntermediateField.inclusion (fieldStage_le_of_directedPath p)

/-- Transition maps are injective because they are literal field inclusions. -/
theorem stageInclusion_injective {i j : Fin 7} (p : DirectedPath i j) :
    Function.Injective (stageInclusion p) :=
  IntermediateField.inclusion_injective (fieldStage_le_of_directedPath p)

/-- Readback in the common ambient carrier: transition maps do not change elements. -/
@[simp] theorem coe_stageInclusion {i j : Fin 7} (p : DirectedPath i j)
    (x : fieldStage i) :
    ((stageInclusion p x : fieldStage j) : KInf) = (x : KInf) := by
  exact IntermediateField.coe_inclusion (fieldStage_le_of_directedPath p) x

/-- The constant directed path induces the identity algebra homomorphism. -/
@[simp] theorem stageInclusion_refl (i : Fin 7) :
    stageInclusion (DirectedPath.refl i) = AlgHom.id ℚ (fieldStage i) := by
  exact IntermediateField.inclusion_self

/-- Native functoriality: transition along two paths equals direct transition. -/
theorem stageInclusion_comp {i j k : Fin 7}
    (p : DirectedPath i j) (q : DirectedPath j k) :
    (stageInclusion q).comp (stageInclusion p) =
      stageInclusion (DirectedPath.comp p q) := by
  ext x
  simp [stageInclusion, IntermediateField.coe_inclusion]

/-- Thin directed homotopy makes the transition map independent of path witness. -/
theorem stageInclusion_path_independent {i j : Fin 7}
    (p q : DirectedPath i j) : stageInclusion p = stageInclusion q := by
  rw [directedPath_homotopy p q]

/-- Every stage has one canonical native inclusion into the terminal field stage. -/
def toTerminal (i : Fin 7) : fieldStage i →ₐ[ℚ] fieldStage 6 :=
  stageInclusion (by
    change i ≤ (6 : Fin 7)
    omega)

/-- The terminal transition is definitionally the identity up to native inclusion. -/
@[simp] theorem toTerminal_terminal :
    toTerminal 6 = AlgHom.id ℚ (fieldStage 6) := by
  apply stageInclusion_refl

/-- Constant-size endpoint readback in `K∞`. -/
@[simp] theorem coe_toTerminal (i : Fin 7) (x : fieldStage i) :
    ((toTerminal i x : fieldStage 6) : KInf) = (x : KInf) := by
  exact coe_stageInclusion _ x

/-- O(1) coherence: any factorization through an intermediate stage gives the
same map to the terminal stage. -/
theorem toTerminal_factor {i j : Fin 7} (p : DirectedPath i j) :
    (toTerminal j).comp (stageInclusion p) = toTerminal i := by
  ext x
  simp [toTerminal, stageInclusion, IntermediateField.coe_inclusion]

end InfoGeometry.Arithmetic.PrimeCyclotomicFieldDirectedSystem
