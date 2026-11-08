import InfoGeometry.Canonical.AlgebraicStarEnvelopeNorm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
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

/-- Subtraction is uniformly continuous for the metric uniformity on a
    normed additive commutative group.  The product metric is the maximum of
    the two component distances, while the norm of a difference of differences
    is bounded by the sum of the component norms. -/
private theorem normedAddCommGroup_isUniformAddGroup (E : Type*)
    [NormedAddCommGroup E] : IsUniformAddGroup E := by
  refine ⟨?_⟩
  have hsub : LipschitzWith 2 (fun p : E × E => p.1 - p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    calc
      ‖(p.1 - p.2) - (q.1 - q.2)‖ =
          ‖(p.1 - q.1) - (p.2 - q.2)‖ := by congr 1 <;> abel
      _ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := norm_sub_le _ _
      _ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ +
          max ‖p.1 - q.1‖ ‖p.2 - q.2‖ :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := by ring
  exact hsub.uniformContinuous

theorem star_isometry :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    Isometry (star : A → A) := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  intro a b
  rw [edist_dist, edist_dist]
  apply congrArg ENNReal.ofReal
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖star a - star b‖ = ‖star (a - b)‖ :=
      congrArg norm (star_sub a b).symm
    _ = ‖a - b‖ := by
      change R.pulledNorm (star (a - b)) = R.pulledNorm (a - b)
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
  letI : NonUnitalSeminormedRing A := inferInstance
  letI : IsTopologicalRing A := NonUnitalSeminormedRing.toIsTopologicalRing
  letI : IsUniformAddGroup A := normedAddCommGroup_isUniformAddGroup A
  exact UniformSpace.Completion.coe_mul a b

@[simp] theorem completion_coe_add (a b : A) :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    ((a + b : A) : UniformSpace.Completion A) =
      (a : UniformSpace.Completion A) + b := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  letI : NonUnitalSeminormedRing A := inferInstance
  letI : IsTopologicalRing A := NonUnitalSeminormedRing.toIsTopologicalRing
  letI : IsUniformAddGroup A := normedAddCommGroup_isUniformAddGroup A
  exact UniformSpace.Completion.coe_add a b

def completion_coe_ringHom :
    letI := FaithfulStarRepresentation.pulledNormedRing R
    A →+* UniformSpace.Completion A := by
  letI := FaithfulStarRepresentation.pulledNormedRing R
  letI : NonUnitalSeminormedRing A := inferInstance
  letI : IsTopologicalRing A := NonUnitalSeminormedRing.toIsTopologicalRing
  letI : IsUniformAddGroup A := normedAddCommGroup_isUniformAddGroup A
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
  simp only [UniformSpace.Completion.norm_coe]
  change R.pulledRingNorm (star a * a) =
    R.pulledRingNorm a * R.pulledRingNorm a
  exact FaithfulStarRepresentation.pulledRingNorm_star_mul_self R a

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
