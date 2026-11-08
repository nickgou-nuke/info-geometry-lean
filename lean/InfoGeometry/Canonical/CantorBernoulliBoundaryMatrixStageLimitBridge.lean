import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
import InfoGeometry.Canonical.GenuineMatrixStageMorphism

/-!
# Boundary representation of the algebraic matrix-stage limit

This owner is the canonical algebraic colimit bridge.  It does not introduce a
second boundary algebra or a completion: it applies the universal property of
`MatrixStageInductiveLimit` to the already proved finite-stage Cuntz boundary
representation.
-/

namespace InfoGeometry.Canonical.CantorBernoulliBoundaryMatrixStageLimitBridge

open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge

noncomputable section

theorem boundaryRep_stageMorphism_compatible
    {i j : ℕ} (hij : i ≤ j) :
    (boundaryRep j).comp (stageMorphism i j hij) = boundaryRep i := by
  apply StarAlgHom.ext
  intro A
  induction hij with
  | refl =>
      simp [stageMorphism_id]
  | @step j hij ih =>
      rw [stageMorphism_step hij]
      change boundaryRep (j + 1)
          (bondStarAlgHom j (stageMorphism i j hij A)) =
        boundaryRep i A
      rw [show bondStarAlgHom j (stageMorphism i j hij A) =
          dyadicMatrixEmbedding j (stageMorphism i j hij A) by
            rw [bondStarAlgHom_apply, bondFun_eq_dyadicMatrixEmbedding]]
      calc
        boundaryRep (j + 1)
            (dyadicMatrixEmbedding j (stageMorphism i j hij A)) =
            boundaryRep j (stageMorphism i j hij A) :=
          (boundaryRep_bond_compatible j _).symm
        _ = boundaryRep i A := by
          simpa only [StarAlgHom.comp_apply] using ih

/-- The unique global algebraic boundary representation induced by the finite
stage cone.  Its restriction to every stage is definitionally the existing
`boundaryRep`, by `boundaryMatrixStageLimitRep_comp` below. -/
def boundaryMatrixStageLimitRep :
    MatrixStageLimit →⋆ₐ[ℂ] BoundaryOperator :=
  liftStarAlgHom (fun n => boundaryRep n)
    (fun i j hij => boundaryRep_stageMorphism_compatible hij)

theorem boundaryMatrixStageLimitRep_comp (n : ℕ) :
    (boundaryMatrixStageLimitRep).comp (canonicalStageHom n) = boundaryRep n := by
  exact liftStarAlgHom_comp (fun n => boundaryRep n)
    (fun i j hij => boundaryRep_stageMorphism_compatible hij) n

@[simp] theorem boundaryMatrixStageLimitRep_apply_stage
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    boundaryMatrixStageLimitRep (canonicalStageHom n A) = boundaryRep n A := by
  exact congrArg (fun f => f A) (boundaryMatrixStageLimitRep_comp n)

theorem boundaryMatrixStageLimitRep_unique
    (F : MatrixStageLimit →⋆ₐ[ℂ] BoundaryOperator)
    (hF : ∀ n : ℕ, F.comp (canonicalStageHom n) = boundaryRep n) :
    F = boundaryMatrixStageLimitRep := by
  exact liftStarAlgHom_unique (fun n => boundaryRep n)
    (fun i j hij => boundaryRep_stageMorphism_compatible hij) F hF

end

end InfoGeometry.Canonical.CantorBernoulliBoundaryMatrixStageLimitBridge
