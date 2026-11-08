/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageCompatibility
import InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit

/-! The native algebraic matrix colimit embeds in the corrected Cuntz quotient.
No completion, positivity, or KMS assertion is made here. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom

def finiteHom (n : ℕ) : MatrixStage n →⋆ₐ[ℂ] ComplexStarCuntzAlg Bool :=
  (stageHom n).comp (stageStarAlgEquiv n).symm.toStarAlgHom

theorem finiteHom_step (n : ℕ) (A : MatrixStage n) :
    finiteHom (n + 1) (concreteStep n A) = finiteHom n A := by
  have h := stageStarAlgEquiv_bond n ((stageStarAlgEquiv n).symm A)
  simp only [StarAlgEquiv.apply_symm_apply] at h
  rw [← h]
  change stageHom (n + 1) ((stageStarAlgEquiv (n + 1)).symm
    (stageStarAlgEquiv (n + 1) _)) = _
  rw [StarAlgEquiv.symm_apply_apply, stageHom_bond]
  rfl

theorem finiteHom_transition {i j : ℕ} (h : i ≤ j) (A : MatrixStage i) :
    finiteHom j (rawMap h A) = finiteHom i A := by
  change finiteHom j (map concreteData h A) = _
  induction h with
  | refl => simp
  | step h ih =>
      rw [map_succ]
      change finiteHom _ (concreteStep _ (map concreteData h A)) = _
      rw [finiteHom_step, ih]

def quotientAlgHom : Carrier →ₐ[ℂ] ComplexStarCuntzAlg Bool :=
  DirectLimit.Algebra.lift MatrixStage (fun _ _ h => rawMap h)
    (ComplexStarCuntzAlg Bool) (fun n => (finiteHom n).toAlgHom)
    (fun _ _ h A => finiteHom_transition h A)

@[simp] theorem quotientAlgHom_stage (n : ℕ) (A : MatrixStage n) :
    quotientAlgHom (stageInjection n A) = finiteHom n A := rfl

theorem quotientAlgHom_star (x : Carrier) :
    quotientAlgHom (star x) = star (quotientAlgHom x) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [← stageInjection_apply, ← stageInjection_star,
        quotientAlgHom_stage, quotientAlgHom_stage, map_star]

def quotientHom : Carrier →⋆ₐ[ℂ] ComplexStarCuntzAlg Bool :=
  { quotientAlgHom with map_star' := quotientAlgHom_star }

@[simp] theorem quotientHom_stage (n : ℕ) (A : MatrixStage n) :
    quotientHom (stageInjection n A) = finiteHom n A := rfl

theorem quotientHom_injective : Function.Injective quotientHom := by
  intro x y
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      intro h
      change finiteHom n A = finiteHom n B at h
      have hab := stageHom_injective n h
      have hab' : A = B := (stageStarAlgEquiv n).symm.injective hab
      exact congrArg (stageInjection n) hab'

end InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
end
