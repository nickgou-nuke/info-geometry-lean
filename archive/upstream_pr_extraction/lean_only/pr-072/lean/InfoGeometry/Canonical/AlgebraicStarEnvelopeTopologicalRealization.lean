import InfoGeometry.Canonical.AlgebraicStarEnvelopeNorm
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Topology.Algebra.UniformRing

/-!
# Topology and completion after faithful norm transport

This owner deliberately comes after the faithful norm owner.  The topology is
the one induced by the transported `NormedRing`; the completion is Mathlib's
uniform-space carrier.

What is proved/packaged here:
* pulled-norm metric/uniform structure;
* canonical completion embedding (`coe`), density, continuity, and isometry;
* compatibility lemmas for already-existing algebraic operations (`coe_add`,
  `coe_mul`, `coeRingHom`);
* C⋆-identity only on the dense embedded algebraic core.

What is deliberately **not** packaged here:
* no automatic `StarRing`/`CStarRing` instance on `UniformSpace.Completion A`;
* no claim that generic completion already carries full C⋆ structure.

So no algebraic structure is manufactured by analytic continuation: algebraic
operations remain those supplied by the algebraic colimit and represented
C⋆-closure data.
-/

noncomputable section

namespace CStarStateColimit.Native.FaithfulStarRepresentation

universe u v

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {B : Type v} [CStarAlgebra B]
variable (R : FaithfulStarRepresentation (A := A) (B := B))

theorem star_isometry :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    Isometry (star : A → A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  intro a b
  rw [edist_dist, edist_dist]
  apply congrArg ENNReal.ofReal
  rw [dist_eq_norm, dist_eq_norm, ← star_sub]
  exact FaithfulStarRepresentation.pulledNorm_star R (a - b)

noncomputable def completionStar :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    UniformSpace.Completion A → UniformSpace.Completion A := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.map (star : A → A)

@[simp] theorem completionStar_coe (a : A) :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    completionStar R (a : UniformSpace.Completion A) =
      ((star a : A) : UniformSpace.Completion A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.map_coe
    (FaithfulStarRepresentation.star_isometry R).uniformContinuous a

theorem completionStar_continuous :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    Continuous (completionStar R) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.continuous_map

@[simp] theorem completion_coe_mul (a b : A) :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    ((a * b : A) : UniformSpace.Completion A) =
      (a : UniformSpace.Completion A) * b := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.coe_mul a b

@[simp] theorem completion_coe_add (a b : A) :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    ((a + b : A) : UniformSpace.Completion A) =
      (a : UniformSpace.Completion A) + b := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.coe_add a b

def completion_coe_ringHom :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    A →+* UniformSpace.Completion A := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.coeRingHom

/-! The C*-identity is already exact on the dense algebraic core.  This is
the honest completion-level statement available without inventing a star
operation on the completion carrier. -/
theorem completion_coe_cstar_identity (a : A) :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    ‖((star a * a : A) : UniformSpace.Completion A)‖ =
      ‖(a : UniformSpace.Completion A)‖ *
        ‖(a : UniformSpace.Completion A)‖ := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  simpa only [UniformSpace.Completion.norm_coe] using
    FaithfulStarRepresentation.pulledRingNorm_star_mul_self R a

/-- The metric completion induced by the chosen faithful C-star realization. -/
noncomputable def completion : Type u :=
  @UniformSpace.Completion A
    (FaithfulStarRepresentation.pulledNormedRing R).toMetricSpace.toUniformSpace

theorem completion_completeSpace :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    CompleteSpace (UniformSpace.Completion A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.completeSpace A

theorem completion_coe_dense :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    DenseRange (UniformSpace.Completion.coe' : A → UniformSpace.Completion A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.denseRange_coe

theorem completion_coe_continuous :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    Continuous (UniformSpace.Completion.coe' : A → UniformSpace.Completion A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.continuous_coe A

theorem completion_coe_isometry :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    Isometry (UniformSpace.Completion.coe' : A → UniformSpace.Completion A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  exact UniformSpace.Completion.coe_isometry

end CStarStateColimit.Native.FaithfulStarRepresentation
