import InfoGeometry.Projective.Rays
import InfoGeometry.Clifford.Grading

/-!
# InfoGeometry.Projective.ProjectiveMap

Descent of doubled-space linear maps to the pointed projective ray space.
This correctly accounts for the "vacuum" (the zero class) as the apex of the cone.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Projective

open InfoGeometry.Krein

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma map_smul_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (u : Gauge) (v : DoubledSpace E) :
    A (u • v) = u • A v := by
  simp

/-- Any linear endomorphism respects the same_ray relation. -/
lemma same_ray_map
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    {v w : DoubledSpace E} :
    same_ray v w → same_ray (A v) (A w) := by
  rintro ⟨a, ha, rfl⟩
  refine ⟨a, ha, by simp⟩

/-- Descent of a linear map to the pointed projective space. -/
def projectiveMap
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    ProjectiveState E → ProjectiveState E :=
  Quotient.map A (fun _ _ => same_ray_map A)

/-- The vacuum / cone-point ray (the class of `0`). -/
def vacuum (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ProjectiveState E :=
  projectivize (0 : DoubledSpace E)

instance : Inhabited (ProjectiveState E) := ⟨vacuum E⟩

lemma projectiveMap_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (v : DoubledSpace E) :
    projectiveMap A (projectivize v) = projectivize (A v) := rfl

/-- Every linear map fixes the vacuum (the apex of the cone). -/
lemma projectiveMap_vacuum
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap A (vacuum E) = vacuum E := by
  simp [vacuum, projectivize, projectiveMap]

lemma projectiveMap_mk_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap A (projectivize (u • v)) = projectiveMap A (projectivize v) := by
  simp [projectiveMap_mk]

/-- Grade-preserving (even) endomorphisms descend to projective states. -/
def projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (_hA : isEven A) :
    ProjectiveState E → ProjectiveState E :=
  projectiveMap A

lemma projectiveMapEven_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A)
    (v : DoubledSpace E) :
    projectiveMapEven A hA (projectivize v) = projectivize (A v) := rfl

lemma projectiveMapEven_vacuum
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A) :
    projectiveMapEven A hA (vacuum E) = vacuum E :=
  projectiveMap_vacuum A

/-- Harmonic ray predicate for a projective dynamics map. -/
def IsHarmonicRay
    (Φ : ProjectiveState E → ProjectiveState E)
    (q : ProjectiveState E) : Prop :=
  Φ q = q

lemma vacuum_isHarmonic_projectiveMap
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    IsHarmonicRay (projectiveMap A) (vacuum E) :=
  projectiveMap_vacuum A

lemma vacuum_isHarmonic_projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A) :
    IsHarmonicRay (projectiveMapEven A hA) (vacuum E) :=
  projectiveMapEven_vacuum A hA

lemma projectiveMapEven_mk_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A)
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMapEven A hA (projectivize (u • v)) = projectiveMapEven A hA (projectivize v) :=
  projectiveMap_mk_gauge A u v

lemma modular_j_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    modular_j (u • v) = u • modular_j v := by
  simp

lemma spectral_epsilon_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    spectral_epsilon (u • v) = u • spectral_epsilon v := by
  simp

lemma complex_i_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    complex_i (u • v) = u • complex_i v := by
  simp

lemma projectiveMap_modular_j_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap modular_j (projectivize (u • v)) = projectiveMap modular_j (projectivize v) :=
  projectiveMap_mk_gauge modular_j u v

lemma projectiveMap_spectral_epsilon_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap spectral_epsilon (projectivize (u • v)) = projectiveMap spectral_epsilon (projectivize v) :=
  projectiveMap_mk_gauge spectral_epsilon u v

lemma projectiveMap_complex_i_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap complex_i (projectivize (u • v)) = projectiveMap complex_i (projectivize v) :=
  projectiveMap_mk_gauge complex_i u v

lemma projectiveMap_id :
    projectiveMap (ContinuousLinearMap.id ℝ (DoubledSpace E)) = id := by
  ext q
  refine Quotient.inductionOn q ?_
  intro v
  rw [projectiveMap, Quotient.map_mk]
  simp

lemma projectiveMap_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (A.comp B) = (projectiveMap A) ∘ (projectiveMap B) := by
  ext q
  refine Quotient.inductionOn q ?_
  intro v
  rw [projectiveMap, Quotient.map_mk]
  rfl

/-- Nonzero scalar rescaling of a linear map does not change its descended projective map. -/
lemma projectiveMap_smul_gauge
    (u : Gauge)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (E := E) ((u : ℝ) • A) = projectiveMap (E := E) A := by
  ext q
  refine Quotient.inductionOn q ?_
  intro v
  rw [projectiveMap, Quotient.map_mk, projectiveMap, Quotient.map_mk]
  change projectivize (E := E) (u • A v) = projectivize (E := E) (A v)
  exact projectivize_smul (E := E) u (A v)

/-- Negating a linear map does not change its descended projective dynamics. -/
lemma projectiveMap_neg
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (E := E) (-A) = projectiveMap (E := E) A := by
  ext q
  refine Quotient.inductionOn q ?_
  intro v
  rw [projectiveMap, Quotient.map_mk, projectiveMap, Quotient.map_mk]
  change projectivize (E := E) (-A v) = projectivize (E := E) (A v)
  simpa using (projectivize_smul (E := E) (-1 : Gauge) (A v))

lemma projectiveMapEven_id
    (hId : isEven (ContinuousLinearMap.id ℝ (DoubledSpace E))) :
    projectiveMapEven (ContinuousLinearMap.id ℝ (DoubledSpace E)) hId = id := by
  unfold projectiveMapEven
  exact projectiveMap_id

lemma projectiveMapEven_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A)
    (hB : isEven B) :
    projectiveMapEven (A.comp B)
      (by
        unfold isEven at *
        calc
          (modular_j (E := E)).comp (A.comp B)
              = ((modular_j (E := E)).comp A).comp B := by rw [ContinuousLinearMap.comp_assoc]
            _ = (A.comp (modular_j (E := E))).comp B := by rw [hA]
            _ = A.comp ((modular_j (E := E)).comp B) := by rw [← ContinuousLinearMap.comp_assoc]
            _ = A.comp (B.comp (modular_j (E := E))) := by rw [hB]
            _ = (A.comp B).comp (modular_j (E := E)) := by rw [ContinuousLinearMap.comp_assoc])
      = (projectiveMapEven A hA) ∘ (projectiveMapEven B hB) := by
  unfold projectiveMapEven
  exact projectiveMap_comp A B

end KreinClifford

end InfoGeometry.Projective
