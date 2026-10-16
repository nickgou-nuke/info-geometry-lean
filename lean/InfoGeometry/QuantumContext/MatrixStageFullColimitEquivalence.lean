/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
import InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
import InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

/-!
# Equivalence of the two algebraic full-matrix colimit presentations

The BitWord-indexed quotient colimit and the `Fin (2^n)` Mathlib direct limit
are equivalent through the existing finite-stage star-algebra equivalences.
This theorem identifies only the two algebraic colimit presentations; it does
not identify either carrier with a completion or transport a functional.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence

open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

/-- The inverse finite-stage map, followed by the quotient-stage inclusion. -/
def carrierStageToQuotient (n : ℕ) : MatrixStage n →⋆ₐ[ℂ] MatrixStageLimit :=
  (canonicalStageHom n).comp (stageStarAlgEquiv n).symm.toStarAlgHom

/-- Naturality of the inverse stage maps under the standard matrix embeddings. -/
theorem carrierStageToQuotient_compatible {m n : ℕ} (h : m ≤ n) :
    (carrierStageToQuotient n).comp (rawMap h) = carrierStageToQuotient m := by
  ext A
  change canonicalStageHom n
      ((stageStarAlgEquiv n).symm (rawMap h A)) =
    canonicalStageHom m ((stageStarAlgEquiv m).symm A)
  have hnat := stageStarAlgEquiv_stageMorphism h ((stageStarAlgEquiv m).symm A)
  have hinv : (stageStarAlgEquiv n).symm (rawMap h A) =
      stageMorphism m n h ((stageStarAlgEquiv m).symm A) := by
    have hnat' : stageStarAlgEquiv n
        (stageMorphism m n h ((stageStarAlgEquiv m).symm A)) = rawMap h A := by
      simpa using hnat
    rw [← hnat']
    exact (stageStarAlgEquiv n).symm_apply_apply _
  rw [hinv]
  exact congrArg (fun f : Stage m →⋆ₐ[ℂ] MatrixStageLimit =>
    f ((stageStarAlgEquiv m).symm A)) (canonicalStageHom_comp h)

/-- Ring-homomorphism lift of the inverse cone. -/
noncomputable def carrierToQuotientRingHom : Carrier →+* MatrixStageLimit :=
  DirectLimit.Ring.lift MatrixStage (fun _ _ h => rawMap h) MatrixStageLimit
    (fun n => (carrierStageToQuotient n).toRingHom) (by
      intro m n h A
      change carrierStageToQuotient n (rawMap h A) = carrierStageToQuotient m A
      exact congrArg (fun f : MatrixStage m →⋆ₐ[ℂ] MatrixStageLimit => f A)
        (carrierStageToQuotient_compatible h))

@[simp] theorem carrierToQuotientRingHom_stage (n : ℕ) (A : MatrixStage n) :
    carrierToQuotientRingHom (stageInjection n A) =
      canonicalStageHom n ((stageStarAlgEquiv n).symm A) := by
  change DirectLimit.Ring.lift MatrixStage (fun _ _ h => rawMap h)
    MatrixStageLimit (fun n => (carrierStageToQuotient n).toRingHom) _
    (DirectLimit.Ring.of MatrixStage (fun _ _ h => rawMap h) n A) = _
  rw [DirectLimit.Ring.lift_of]
  rfl

/-- The inverse map is a star-algebra homomorphism. -/
noncomputable def carrierToQuotient : Carrier →⋆ₐ[ℂ] MatrixStageLimit where
  toFun := carrierToQuotientRingHom
  map_one' := map_one carrierToQuotientRingHom
  map_mul' := map_mul carrierToQuotientRingHom
  map_zero' := map_zero carrierToQuotientRingHom
  map_add' := map_add carrierToQuotientRingHom
  commutes' c := by
    rw [← (stageInjection 0).commutes c]
    change carrierToQuotientRingHom
        (stageInjection 0 (algebraMap ℂ (MatrixStage 0) c)) =
      algebraMap ℂ MatrixStageLimit c
    rw [carrierToQuotientRingHom_stage]
    exact (carrierStageToQuotient 0).commutes c
  map_star' := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A =>
        change carrierToQuotientRingHom (stageInjection n (star A)) =
          star (carrierToQuotientRingHom (stageInjection n A))
        rw [carrierToQuotientRingHom_stage, carrierToQuotientRingHom_stage]
        exact map_star (carrierStageToQuotient n) A

@[simp] theorem carrierToQuotient_stage (n : ℕ) (A : MatrixStage n) :
    carrierToQuotient (stageInjection n A) =
      canonicalStageHom n ((stageStarAlgEquiv n).symm A) := by
  change carrierToQuotientRingHom (stageInjection n A) = _
  exact carrierToQuotientRingHom_stage n A

/-- The forward stage map into the canonical Mathlib direct-limit carrier. -/
def stageToCarrier (n : ℕ) : Stage n →⋆ₐ[ℂ] Carrier :=
  (stageInjection n).comp (stageStarAlgEquiv n).toStarAlgHom

/-- Naturality of the forward stage maps under every finite-stage transition. -/
theorem stageToCarrier_compatible {m n : ℕ} (h : m ≤ n) :
    (stageToCarrier n).comp (stageMorphism m n h) = stageToCarrier m := by
  ext A
  change stageInjection n (stageStarAlgEquiv n (stageMorphism m n h A)) =
    stageInjection m (stageStarAlgEquiv m A)
  rw [stageStarAlgEquiv_stageMorphism]
  exact stageInjection_transition h (stageStarAlgEquiv m A)

/-- The universal-property map from the quotient colimit to the direct limit. -/
noncomputable def quotientToCarrier : MatrixStageLimit →⋆ₐ[ℂ] Carrier :=
  liftStarAlgHom stageToCarrier (fun _ _ h => stageToCarrier_compatible h)

/-- The maps are inverse on each quotient-stage inclusion. -/
theorem carrierToQuotient_quotientToCarrier_stage (n : ℕ) (A : Stage n) :
    carrierToQuotient (quotientToCarrier (toLimit n A)) = toLimit n A := by
  change carrierToQuotient (stageInjection n (stageStarAlgEquiv n A)) = toLimit n A
  rw [carrierToQuotient_stage]
  simpa only [canonicalStageHom_apply] using
    congrArg (canonicalStageHom n) ((stageStarAlgEquiv n).symm_apply_apply A)

/-- The maps are inverse on each canonical direct-limit injection. -/
theorem quotientToCarrier_carrierToQuotient_stage (n : ℕ) (A : MatrixStage n) :
    quotientToCarrier (carrierToQuotient (stageInjection n A)) = stageInjection n A := by
  rw [carrierToQuotient_stage]
  change quotientToCarrier (toLimit n ((stageStarAlgEquiv n).symm A)) = stageInjection n A
  change stageInjection n (stageStarAlgEquiv n ((stageStarAlgEquiv n).symm A)) =
    stageInjection n A
  exact congrArg (stageInjection n) ((stageStarAlgEquiv n).apply_symm_apply A)

/-- The maps are inverse on the BitWord-indexed quotient carrier. -/
theorem carrierToQuotient_comp_quotientToCarrier :
    carrierToQuotient.comp quotientToCarrier = StarAlgHom.id ℂ MatrixStageLimit := by
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨n, A⟩
      change carrierToQuotient (quotientToCarrier (toLimit n A)) = toLimit n A
      exact carrierToQuotient_quotientToCarrier_stage n A

/-- The maps are inverse on the canonical Mathlib direct-limit carrier. -/
theorem quotientToCarrier_comp_carrierToQuotient :
    quotientToCarrier.comp carrierToQuotient = StarAlgHom.id ℂ Carrier := by
  ext x
  induction x using DirectLimit.induction with
  | _ n A =>
      change quotientToCarrier (carrierToQuotient (stageInjection n A)) = stageInjection n A
      exact quotientToCarrier_carrierToQuotient_stage n A

/-- The two algebraic full-matrix colimit presentations are equivalent. -/
noncomputable def carrierStarAlgEquiv : MatrixStageLimit ≃⋆ₐ[ℂ] Carrier :=
  StarAlgEquiv.ofStarAlgHom quotientToCarrier carrierToQuotient
    carrierToQuotient_comp_quotientToCarrier quotientToCarrier_comp_carrierToQuotient

end InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence
