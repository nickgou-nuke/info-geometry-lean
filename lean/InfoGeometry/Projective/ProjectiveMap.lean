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

lemma modularJ_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    modularJ (u • v) = u • modularJ v := by
  exact map_smul_gauge (modularJ E) u v

lemma spectralEpsilon_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    spectralEpsilon (u • v) = u • spectralEpsilon v := by
  exact map_smul_gauge (spectralEpsilon E) u v

lemma complexI_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    complexI (u • v) = u • complexI v := by
  exact map_smul_gauge (complexI E) u v

lemma projectiveMap_modularJ_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (modularJ E) (projectivize (u • v)) = projectiveMap (modularJ E) (projectivize v) := by
  exact projectiveMap_mk_gauge (modularJ E) u v

lemma projectiveMap_spectralEpsilon_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (spectralEpsilon E) (projectivize (u • v)) = projectiveMap (spectralEpsilon E) (projectivize v) := by
  exact projectiveMap_mk_gauge (spectralEpsilon E) u v

lemma projectiveMap_complexI_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (complexI E) (projectivize (u • v)) = projectiveMap (complexI E) (projectivize v) := by
  exact projectiveMap_mk_gauge (complexI E) u v

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
