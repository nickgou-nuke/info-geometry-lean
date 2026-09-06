import InfoGeometry.Projective.Rays
import InfoGeometry.Clifford.Grading

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

/-- The vacuum / cone-point ray (the class of `0`). -/
def vacuum : ProjectiveState (E := E) :=
  projectivize (E := E) (0 : DoubledSpace E)

instance : Inhabited (ProjectiveState (E := E)) := ⟨vacuum (E := E)⟩

lemma projectiveMap_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (v : DoubledSpace E) :
    projectiveMap (E := E) A (projectivize (E := E) v)
      = projectivize (E := E) (A v) := rfl

lemma projectiveMap_vacuum
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    projectiveMap (E := E) A (vacuum (E := E)) = vacuum (E := E) := by
  simp [vacuum, projectiveMap_mk]

lemma projectiveMap_mk_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (E := E) A (projectivize (E := E) (u • v))
      = projectiveMap (E := E) A (projectivize (E := E) v) := by
  calc
    projectiveMap (E := E) A (projectivize (E := E) (u • v))
        = projectivize (E := E) (A (u • v)) := by
            rfl
    _ = projectivize (E := E) (u • A v) := by
          rw [map_smul_gauge (E := E) A u v]
    _ = projectiveMap (E := E) A (projectivize (E := E) v) := by
          simp [projectiveMap_mk]

/-- Grade-preserving (even) endomorphisms descend to projective states. -/
def projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A) :
    ProjectiveState (E := E) → ProjectiveState (E := E) :=
  let _ := hA
  projectiveMap (E := E) A

lemma projectiveMapEven_mk
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A)
    (v : DoubledSpace E) :
    projectiveMapEven (E := E) A hA (projectivize (E := E) v)
      = projectivize (E := E) (A v) := rfl

lemma projectiveMapEven_vacuum
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A) :
    projectiveMapEven (E := E) A hA (vacuum (E := E)) = vacuum (E := E) := by
  unfold projectiveMapEven
  exact projectiveMap_vacuum (E := E) A

/-- Harmonic ray predicate for a projective dynamics map. -/
def IsHarmonicRay
    (Φ : ProjectiveState (E := E) → ProjectiveState (E := E))
    (q : ProjectiveState (E := E)) : Prop :=
  Φ q = q

lemma vacuum_isHarmonic_projectiveMap
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    IsHarmonicRay (E := E) (projectiveMap (E := E) A) (vacuum (E := E)) :=
  projectiveMap_vacuum (E := E) A

lemma vacuum_isHarmonic_projectiveMapEven
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A) :
    IsHarmonicRay (E := E) (projectiveMapEven (E := E) A hA) (vacuum (E := E)) :=
  projectiveMapEven_vacuum (E := E) A hA

lemma projectiveMapEven_mk_gauge
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : isEven (E := E) A)
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMapEven (E := E) A hA (projectivize (E := E) (u • v))
      = projectiveMapEven (E := E) A hA (projectivize (E := E) v) := by
  exact projectiveMap_mk_gauge (E := E) A u v

lemma modularJ_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    modularJ (E := E) (u • v) = u • modularJ (E := E) v := by
  exact map_smul_gauge (E := E) (modularJ (E := E)) u v

lemma spectralEpsilon_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    spectralEpsilon (E := E) (u • v) = u • spectralEpsilon (E := E) v := by
  exact map_smul_gauge (E := E) (spectralEpsilon (E := E)) u v

lemma complexI_gauge_equivariant
    (u : Gauge) (v : DoubledSpace E) :
    complexI (E := E) (u • v) = u • complexI (E := E) v := by
  exact map_smul_gauge (E := E) (complexI (E := E)) u v

lemma projectiveMap_modularJ_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (E := E) (modularJ (E := E))
      (projectivize (E := E) (u • v))
        =
      projectiveMap (E := E) (modularJ (E := E))
        (projectivize (E := E) v) := by
  exact projectiveMap_mk_gauge (E := E) (modularJ (E := E)) u v

lemma projectiveMap_spectralEpsilon_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (E := E) (spectralEpsilon (E := E))
      (projectivize (E := E) (u • v))
        =
      projectiveMap (E := E) (spectralEpsilon (E := E))
        (projectivize (E := E) v) := by
  exact projectiveMap_mk_gauge (E := E) (spectralEpsilon (E := E)) u v

lemma projectiveMap_complexI_mk_gauge
    (u : Gauge) (v : DoubledSpace E) :
    projectiveMap (E := E) (complexI (E := E))
      (projectivize (E := E) (u • v))
        =
      projectiveMap (E := E) (complexI (E := E))
        (projectivize (E := E) v) := by
  exact projectiveMap_mk_gauge (E := E) (complexI (E := E)) u v

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
