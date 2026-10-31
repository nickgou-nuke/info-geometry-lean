/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.CoxeterPort.MatrixGroup
import InfoGeometry.Cantor.PermutationOperator
import Coxeter.PermutationRepresentation
import Mathlib.Basic.Real.Basic

/-!
# Coxeter symmetries as noncommutative operators

The faithful signed-reflection permutation representation from `lean-coxeter`
acts by inverse reindexing on real-valued functions. This realizes every
matrix-presented Coxeter group faithfully inside the units of a genuine
endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.CoxeterPort

open Coxeter

variable {B : Type*} (M : CoxeterMatrix B)

private abbrev ReflectionCarrier := Coxeter.AbstractRootSet M.Group

/-- The operator on functions induced by a signed-reflection permutation. -/
def coxeterOperator (w : M.Group) :
    Module.End ℝ (ReflectionCarrier M → ℝ) :=
  InfoGeometry.Cantor.PermutationOperator.operator (R := ℝ) (Coxeter.permRep w)

/-- The invertible operator represented by a Coxeter element. -/
def coxeterOperatorUnit (w : M.Group) :
    (Module.End ℝ (ReflectionCarrier M → ℝ))ˣ :=
  InfoGeometry.Cantor.PermutationOperator.operatorUnit (R := ℝ) (Coxeter.permRep w)

/-- The Coxeter group homomorphism into endomorphism-algebra units. -/
def coxeterOperatorUnitRep :
    M.Group →* (Module.End ℝ (ReflectionCarrier M → ℝ))ˣ :=
  InfoGeometry.Cantor.PermutationOperator.operatorUnitRep (R := ℝ) |>.comp
    Coxeter.permRep

/-- The signed-reflection permutation action remains faithful after passage to
operators on the full function space. -/
theorem coxeterOperatorUnitRep_injective :
    Function.Injective (coxeterOperatorUnitRep M) := by
  exact (InfoGeometry.Cantor.PermutationOperator.operatorUnitRep_injective
    (R := ℝ)).comp Coxeter.permRep_inj

/-- Faithfulness preserves every noncommuting pair as noncommuting operator
units. -/
theorem coxeterOperatorUnitRep_ne_mul_swap (g h : M.Group)
    (hgh : g * h ≠ h * g) :
    coxeterOperatorUnitRep M g * coxeterOperatorUnitRep M h ≠
      coxeterOperatorUnitRep M h * coxeterOperatorUnitRep M g := by
  intro hcomm
  apply hgh
  apply coxeterOperatorUnitRep_injective M
  simpa only [map_mul] using hcomm

/-- The Coxeter operator group, as an actual subgroup of noncommutative
endomorphism-algebra units. -/
def coxeterOperatorGroup :
    Subgroup (Module.End ℝ (ReflectionCarrier M → ℝ))ˣ :=
  (⊤ : Subgroup M.Group).map (coxeterOperatorUnitRep M)

theorem coxeterOperatorUnitRep_mem_group (w : M.Group) :
    coxeterOperatorUnitRep M w ∈ coxeterOperatorGroup M := by
  rw [coxeterOperatorGroup, Subgroup.mem_map]
  exact ⟨w, by simp, rfl⟩

end InfoGeometry.CoxeterPort

end
