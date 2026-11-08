import InfoGeometry.Canonical.AlgebraicStarEnvelopeNorm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Faithful realizations of the algebraic star envelope

The algebraic envelope is norm-free until a concrete faithful realization is
supplied.  This file packages that datum in stage form, so the descended map
and its norm readout are both controlled by the existing colimit universal
property.
-/

noncomputable section

namespace InfoGeometry.Canonical.AlgebraicStarEnvelope

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit

universe u v

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable {B : Type v} [CStarAlgebra B]

/-- A faithful realization is a compatible family of stage maps together with
the actual injectivity proof for its algebraic descent. -/
structure FaithfulRealization where
  stageMap : ∀ i, Stage i →⋆ₐ[ℂ] B
  stage_coherence : ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
    stageMap j (sys.map hij x) = stageMap i x
  faithful : Function.Injective
    (lift Stage sys stageMap (fun hij x => stage_coherence hij x))

/-- The descended star-algebra representation supplied by a faithful
realization. -/
def representation (R : FaithfulRealization Stage sys (B := B)) :
    Carrier Stage sys →⋆ₐ[ℂ] B :=
  lift Stage sys R.stageMap (fun hij x => R.stage_coherence hij x)

@[simp] theorem representation_stage
    (R : FaithfulRealization Stage sys (B := B))
    (i : I) (x : Stage i) :
    representation Stage sys R (stageInjection Stage sys i x) =
      R.stageMap i x := by
  exact lift_stage Stage sys R.stageMap (fun hij x => R.stage_coherence hij x) i x

/-- The stage-form realization is an instance of the generic faithful
representation interface. -/
def toFaithfulStarRepresentation
    (R : FaithfulRealization Stage sys (B := B)) :
    CStarStateColimit.Native.FaithfulStarRepresentation
      (A := Carrier Stage sys) (B := B) where
  rep := representation Stage sys R
  faithful := R.faithful

@[simp] theorem pulledNorm_stage
    (R : FaithfulRealization Stage sys (B := B))
    (i : I) (x : Stage i) :
    (toFaithfulStarRepresentation Stage sys R).pulledNorm
        (stageInjection Stage sys i x) =
      ‖R.stageMap i x‖ := by
  change ‖representation Stage sys R (stageInjection Stage sys i x)‖ =
    ‖R.stageMap i x‖
  rw [representation_stage]

theorem pulledRingNorm_stage
    (R : FaithfulRealization Stage sys (B := B))
    (i : I) (x : Stage i) :
    (toFaithfulStarRepresentation Stage sys R).pulledRingNorm
        (stageInjection Stage sys i x) =
      ‖R.stageMap i x‖ := by
  exact pulledNorm_stage Stage sys R i x

end InfoGeometry.Canonical.AlgebraicStarEnvelope
