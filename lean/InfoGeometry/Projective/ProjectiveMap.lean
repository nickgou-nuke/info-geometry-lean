import InfoGeometry.Projective.Rays
import InfoGeometry.Clifford.Grading

/-!
# InfoGeometry.Projective.ProjectiveMap

Descent of doubled-space linear maps to the projective ray quotient.
-/

namespace InfoGeometry.Projective

open InfoGeometry.Krein

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma map_smul_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (u : Gauge) (v : DoubledSpace E) :
    A (u • v) = u • A v := by
  change A ((↑u : ℝ) • v) = (↑u : ℝ) • A v
  simp

lemma sameRayDoubled_map
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    {v w : DoubledSpace E} :
    SameRayDoubled v w →
      SameRayDoubled (A v) (A w) := by
  rintro ⟨a, ha, hw⟩
  refine ⟨a, ha, ?_⟩
  rw [hw]
  simp

/-- Any linear endomorphism descends to projective rays. -/
def projectiveMap
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    ProjectiveState E → ProjectiveState E :=
  Quotient.map (fun v => A v) (by
    intro v w hvw
    exact sameRayDoubled_map A hvw)

/-- The vacuum / cone-point ray (the class of `0`). -/
def vacuum (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : ProjectiveState E :=
  projectivize (0 : DoubledSpace E)

instance : Inhabited (ProjectiveState E) := ⟨vacuum E⟩

lemma projectiveMap_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (v : DoubledSpace E) :
    projectiveMap A (projectivize v) = projectivize (A v) := rfl

lemma projectiveMap_vacuum
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap A (vacuum E) = vacuum E := by
  simp [vacuum, projectiveMap_mk]

lemma projectiveMap_mk_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap A (projectivize (u • v)) = projectiveMap A (projectivize v) := by
  calc
    projectiveMap A (projectivize (u • v))
        = projectivize (A (u • v)) := rfl
    _ = projectivize (u • A v) := by rw [map_smul_gauge A u v]
    _ = projectiveMap A (projectivize v) := by simp [projectiveMap_mk]

/-- Grade-preserving (even) endomorphisms descend to projective states. -/
def projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A) :
    ProjectiveState E → ProjectiveState E :=
  let _ := hA
  projectiveMap A

lemma projectiveMapEven_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A)
    (v : DoubledSpace E) :
    projectiveMapEven A hA (projectivize v) = projectivize (A v) := rfl

lemma projectiveMapEven_vacuum
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A) :
    projectiveMapEven A hA (vacuum E) = vacuum E := by
  unfold projectiveMapEven
  exact projectiveMap_vacuum A

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
    projectiveMapEven A hA (projectivize (u • v)) = projectiveMapEven A hA (projectivize v) := by
  exact projectiveMap_mk_gauge A u v

lemma modular_j_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    modular_j (u • v) = u • modular_j v := by
  exact map_smul_gauge (modular_j E) u v

lemma spectral_epsilon_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    spectral_epsilon (u • v) = u • spectral_epsilon v := by
  exact map_smul_gauge (spectral_epsilon E) u v

lemma complex_i_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    complex_i (u • v) = u • complex_i v := by
  exact map_smul_gauge (complex_i E) u v

lemma projectiveMap_modular_j_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (modular_j E) (projectivize (u • v)) = projectiveMap (modular_j E) (projectivize v) := by
  exact projectiveMap_mk_gauge (modular_j E) u v

lemma projectiveMap_spectral_epsilon_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (spectral_epsilon E) (projectivize (u • v)) = projectiveMap (spectral_epsilon E) (projectivize v) := by
  exact projectiveMap_mk_gauge (spectral_epsilon E) u v

lemma projectiveMap_complex_i_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (complex_i E) (projectivize (u • v)) = projectiveMap (complex_i E) (projectivize v) := by
  exact projectiveMap_mk_gauge (complex_i E) u v

lemma projectiveMap_id :
    projectiveMap (ContinuousLinearMap.id ℝ (DoubledSpace E)) = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  rfl

lemma projectiveMap_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (A.comp B) = (projectiveMap A) ∘ (projectiveMap B) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  rfl

lemma projectiveMapEven_id
    (hId : isEven (ContinuousLinearMap.id ℝ (DoubledSpace E))) :
    projectiveMapEven (ContinuousLinearMap.id ℝ (DoubledSpace E)) hId = id :=
  projectiveMap_id

lemma projectiveMapEven_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven A)
    (hB : isEven B) :
    projectiveMapEven (A.comp B)
      (by
        unfold isEven at *
        rw [← ContinuousLinearMap.comp_assoc, hA, ContinuousLinearMap.comp_assoc, hB, ← ContinuousLinearMap.comp_assoc])
      = (projectiveMapEven A hA) ∘ (projectiveMapEven B hB) :=
  projectiveMap_comp A B

end KreinClifford

end InfoGeometry.Projective
