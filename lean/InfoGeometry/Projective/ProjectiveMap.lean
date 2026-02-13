import InfoGeometry.Projective.Rays
import InfoGeometry.Clifford.Grading
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sameRayDoubled_map
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    {v w : DoubledSpace E} :
    SameRayDoubled (E := E) v w →
      SameRayDoubled (E := E) (A v) (A w) := by
  rintro ⟨a, ha, hw⟩
  refine ⟨a, ha, ?_⟩
  rw [hw]
  simp

/-- Any linear endomorphism descends to projective rays. -/
def projectiveMap
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    ProjectiveState (E := E) → ProjectiveState (E := E) :=
  Quotient.map (fun v => A v) (by
    intro v w hvw
    exact sameRayDoubled_map (E := E) A hvw)

lemma projectiveMap_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (v : DoubledSpace E) :
    projectiveMap (E := E) A (projectivize (E := E) v)
      = projectivize (E := E) (A v) := rfl

/-- Grade-preserving (even) endomorphisms descend to projective states. -/
def projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (_hA : isEven (E := E) A) :
    ProjectiveState (E := E) → ProjectiveState (E := E) :=
  projectiveMap (E := E) A

lemma projectiveMapEven_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A)
    (v : DoubledSpace E) :
    projectiveMapEven (E := E) A hA (projectivize (E := E) v)
      = projectivize (E := E) (A v) := rfl

lemma projectiveMap_id :
    projectiveMap (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E))
      = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  rfl

lemma projectiveMap_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (E := E) (A.comp B)
      = (projectiveMap (E := E) A) ∘ (projectiveMap (E := E) B) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  rfl

lemma projectiveMapEven_id
    (hId : isEven (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E))) :
    projectiveMapEven (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) hId = id :=
  projectiveMap_id (E := E)

lemma projectiveMapEven_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A)
    (hB : isEven (E := E) B) :
    projectiveMapEven (E := E) (A.comp B)
      (by
        unfold isEven at *
        calc
          (modularJ (E := E)).comp (A.comp B)
              = ((modularJ (E := E)).comp A).comp B := by
                  simp [ContinuousLinearMap.comp_assoc]
          _ = (A.comp (modularJ (E := E))).comp B := by rw [hA]
          _ = A.comp ((modularJ (E := E)).comp B) := by
                simp [ContinuousLinearMap.comp_assoc]
          _ = A.comp (B.comp (modularJ (E := E))) := by rw [hB]
          _ = (A.comp B).comp (modularJ (E := E)) := by
                simp [ContinuousLinearMap.comp_assoc])
      = (projectiveMapEven (E := E) A hA) ∘ (projectiveMapEven (E := E) B hB) :=
  projectiveMap_comp (E := E) A B

end KreinClifford
