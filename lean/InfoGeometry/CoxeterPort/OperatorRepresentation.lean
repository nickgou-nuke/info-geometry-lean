/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.CoxeterPort.MatrixGroup
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
    Module.End ℝ (ReflectionCarrier M → ℝ) where
  toFun f x := f ((Coxeter.permRep w)⁻¹ x)
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

/-- The invertible operator represented by a Coxeter element. -/
def coxeterOperatorUnit (w : M.Group) :
    (Module.End ℝ (ReflectionCarrier M → ℝ))ˣ where
  val := coxeterOperator M w
  inv := coxeterOperator M w⁻¹
  val_inv := by ext f x; simp [coxeterOperator]
  inv_val := by ext f x; simp [coxeterOperator]

/-- The Coxeter group homomorphism into endomorphism-algebra units. -/
def coxeterOperatorUnitRep :
    M.Group →* (Module.End ℝ (ReflectionCarrier M → ℝ))ˣ where
  toFun := coxeterOperatorUnit M
  map_one' := by apply Units.ext; ext f x; rfl
  map_mul' g h := by
    apply Units.ext
    ext f x
    change f ((Coxeter.permRep (g * h))⁻¹ x) =
      f ((Coxeter.permRep h)⁻¹ ((Coxeter.permRep g)⁻¹ x))
    rw [map_mul, mul_inv_rev]
    rfl

/-- The signed-reflection permutation action remains faithful after passage to
operators on the full function space. -/
theorem coxeterOperatorUnitRep_injective :
    Function.Injective (coxeterOperatorUnitRep M) := by
  classical
  intro g h hgh
  have hval : coxeterOperator M g = coxeterOperator M h :=
    congrArg (fun u : (Module.End ℝ (ReflectionCarrier M → ℝ))ˣ =>
      (u : Module.End ℝ (ReflectionCarrier M → ℝ))) hgh
  have hinv : (Coxeter.permRep g)⁻¹ = (Coxeter.permRep h)⁻¹ := by
    apply Equiv.ext
    intro x
    let δ : ReflectionCarrier M → ℝ :=
      fun y => if y = (Coxeter.permRep g)⁻¹ x then (1 : ℝ) else 0
    have heval := congrArg
      (fun T : Module.End ℝ (ReflectionCarrier M → ℝ) => T δ x) hval
    have hpoint : (Coxeter.permRep h)⁻¹ x = (Coxeter.permRep g)⁻¹ x := by
      simpa [δ, coxeterOperator] using heval.symm
    exact hpoint.symm
  apply Coxeter.permRep_inj
  exact congrArg Inv.inv hinv

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
