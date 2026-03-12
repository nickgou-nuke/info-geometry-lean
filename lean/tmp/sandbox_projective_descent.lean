import InfoGeometry.Projective.Rays
import InfoGeometry.Clifford.Grading

namespace InfoGeometry.Projective

open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Any linear endomorphism respects the same_ray relation. -/
lemma same_ray_map (A : DoubledSpace E →L[ℝ] DoubledSpace E) {v w : DoubledSpace E} :
    same_ray v w → same_ray (A v) (A w) := by
  rintro ⟨a, ha, rfl⟩
  -- A (a • v) = a • A v
  refine ⟨a, ha, by simp⟩

/-- Descent of a linear map to the pointed projective space. -/
def projectiveMap (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    ProjectiveState E → ProjectiveState E :=
  Quotient.map A (fun _ _ => same_ray_map A)

/-- The vacuum state is the ray representing the zero vector. -/
def vacuum (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ProjectiveState E :=
  projectivize (0 : DoubledSpace E)

/-- Every linear map fixes the vacuum (the apex of the cone). -/
lemma projectiveMap_vacuum (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap A (vacuum E) = vacuum E := by
  simp [vacuum, projectivize, projectiveMap]

/-- Even operators (grade preserving) descend to projective states. -/
def projectiveMapEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) (_hA : isEven A) :
    ProjectiveState E → ProjectiveState E :=
  projectiveMap A

end InfoGeometry.Projective
