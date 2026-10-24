/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSFaithfulAlgebraicQuotient
import InfoGeometry.Canonical.FilteredGNSHilbertNontrivial
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Faithfulness of the native GNS representation for simple stages

Uncompiled sandbox candidate. Normalization supplies a nonzero global vacuum;
simple stages then have faithful unital representations. Common-stage induction
proves faithfulness on the existing algebraic colimit. No faithful state is assumed.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSMatrixFaithfulness

open FilteredGNSHilbertColimit FilteredGNSGlobalStageRepresentation
open FilteredStarAlgebraDirectLimit FilteredGNSAlgebraicColimitRepresentation
open FilteredGNSFaithfulAlgebraicQuotient

universe u

section SimpleStages

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
variable [∀ i, IsSimpleRing (Stage i)]

/-- Simplicity, not faithfulness of the state, makes each unital stage action faithful. -/
theorem globalStageRepresentation_injective (i : I) :
    Function.Injective (globalStageRepresentationStarAlgHom Stage sys ω i) := by
  exact RingHom.injective
    (globalStageRepresentationStarAlgHom Stage sys ω i).toAlgHom.toRingHom

/-- Two algebraic-colimit elements can be compared at one simple finite stage. -/
theorem algebraicColimitGNSRepresentation_injective :
    Function.Injective (algebraicColimitGNSRepresentation Stage sys ω) := by
  intro x y hxy
  induction x, y using DirectLimit.induction₂ with
  | _ i a b =>
      change algebraicColimitGNSRepresentation Stage sys ω
          (algebraicStarDirectLimitOf Stage sys i a) =
        algebraicColimitGNSRepresentation Stage sys ω
          (algebraicStarDirectLimitOf Stage sys i b) at hxy
      rw [algebraicColimitGNSRepresentation_of,
        algebraicColimitGNSRepresentation_of] at hxy
      have hab := globalStageRepresentation_injective Stage sys ω i hxy
      subst b
      rfl

/-- Discharges the injectivity input of the existing faithful completion owners. -/
theorem rangeAlgHom_injective :
    Function.Injective (rangeAlgHom Stage sys ω) := by
  intro x y hxy
  apply algebraicColimitGNSRepresentation_injective Stage sys ω
  exact congrArg Subtype.val hxy

end SimpleStages

open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open scoped ComplexOrder

private noncomputable instance matrixStageSimple (n : ℕ) :
    IsSimpleRing (CStarMatrixStage n) :=
  IsSimpleRing.of_ringEquiv
    (CStarMatrix.ofMatrixStarAlgEquiv :
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ≃⋆ₐ[ℂ]
        CStarMatrixStage n).toAlgEquiv.toRingEquiv
    inferInstance

/-- Concrete growing matrix tower: every compatible normalized state family
has a faithful algebraic-colimit GNS representation. -/
theorem matrix_algebraicColimitGNSRepresentation_injective
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem) :
    Function.Injective (algebraicColimitGNSRepresentation
      CStarMatrixStage cstarMatrixInductiveSystem ω) := by
  exact algebraicColimitGNSRepresentation_injective
    CStarMatrixStage cstarMatrixInductiveSystem ω

/-- Concrete input for `faithfulStarRepresentation` and the existing kernel criterion. -/
theorem matrix_rangeAlgHom_injective
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem) :
    Function.Injective (rangeAlgHom CStarMatrixStage cstarMatrixInductiveSystem ω) := by
  exact rangeAlgHom_injective CStarMatrixStage cstarMatrixInductiveSystem ω

end CStarStateColimit.Native.FilteredGNSMatrixFaithfulness
