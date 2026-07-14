import InfoGeometry.Projective.Bridge

/-!
# InfoGeometry.Projective.Normalize

Normalization of positive measures modulo projective ray equivalence.
-/

namespace Normalize

section NormalizeOnProj

variable {α : Type u}
variable [Fintype α] [Nonempty α]

/-- Normalization is constant on projective rays. -/
lemma normalize_eq_of_sameRay
    {μ ν : PositiveMeasure α ℝ}
    (h : PositiveMeasure.SameRay μ ν) :
    PositiveMeasure.normalize (α := α) (R := ℝ) μ = PositiveMeasure.normalize (α := α) (R := ℝ) ν := by
  rcases h with ⟨c, rfl⟩
  have hc : 0 < c.1 := c.2
  symm
  exact PositiveMeasure.normalize_scale (α := α) (c := c.1) hc μ

/-- Legacy quotient-based normalization map (kept private). -/
private noncomputable def normalizeOnProjLegacy : PositiveMeasure.Proj (α := α) → PositiveMeasure α ℝ :=
  Quotient.lift
    (fun μ => PositiveMeasure.normalize (α := α) (R := ℝ) μ)
    (by
      intro μ ν h
      exact normalize_eq_of_sameRay (α := α) h)

/-- Normalization on cone-interior rays via the bridge equivalence. -/
noncomputable def normalizeOnConeInteriorStateSpace :
    InfoGeometry.Projective.ConeInteriorStateSpace
      ((InfoGeometry.Projective.positiveOrthant (α := α)).cone) → PositiveMeasure α ℝ :=
  normalizeOnProjLegacy (α := α) ∘
    (InfoGeometry.Projective.coneInteriorStateSpaceToProjectiveClass (α := α))

/-- Canonical simplex representative of a projective ray. -/
noncomputable def normalizeOnProj : PositiveMeasure.Proj (α := α) → PositiveMeasure α ℝ :=
  normalizeOnConeInteriorStateSpace (α := α) ∘
    (InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace (α := α))

@[simp] lemma normalizeOnProj_mk (μ : InfoGeometry.PositiveMeasure α ℝ) :
    normalizeOnProj (α := α) (Quotient.mk _ μ) = PositiveMeasure.normalize (α := α) (R := ℝ) μ := by
  unfold normalizeOnProj normalizeOnConeInteriorStateSpace
  rw [Function.comp_apply, Function.comp_apply]
  rw [InfoGeometry.Projective.coneInteriorStateSpaceToProjectiveClass_projectiveClass]
  rfl

/-- The canonical representative has unit mass. -/
@[simp] lemma Z_normalizeOnProj (q : InfoGeometry.PositiveMeasure.Proj (α := α)) :
    PositiveMeasure.Z (α := α) (R := ℝ) (normalizeOnProj (α := α) q) = 1 := by
  refine Quotient.inductionOn q ?_
  intro μ
  simpa using (PositiveMeasure.Z_normalize (α := α) (R := ℝ) μ)

end NormalizeOnProj

namespace InfoGeometry.PositiveMeasure

section NormalizeCompat

variable {α : Type u}
variable [Fintype α] [Nonempty α]

noncomputable abbrev normalizeOnConeInteriorStateSpace :
    InfoGeometry.Projective.ConeInteriorStateSpace
      ((InfoGeometry.Projective.positiveOrthant (α := α)).cone) →
      InfoGeometry.PositiveMeasure α ℝ :=
  InfoGeometry.Projective.Normalize.normalizeOnConeInteriorStateSpace (α := α)

noncomputable abbrev normalizeOnProj : InfoGeometry.PositiveMeasure.Proj (α := α) → InfoGeometry.PositiveMeasure α ℝ :=
  InfoGeometry.Projective.Normalize.normalizeOnProj (α := α)

@[simp] lemma normalizeOnProj_mk (μ : InfoGeometry.PositiveMeasure α ℝ) :
    normalizeOnProj (α := α) (Quotient.mk _ μ) = PositiveMeasure.normalize (α := α) (R := ℝ) μ := by
  simp [normalizeOnProj]

@[simp] lemma Z_normalizeOnProj (q : InfoGeometry.PositiveMeasure.Proj (α := α)) :
    PositiveMeasure.Z (α := α) (R := ℝ) (normalizeOnProj (α := α) q) = 1 := by
  simpa [normalizeOnProj] using
    (InfoGeometry.Projective.Normalize.Z_normalizeOnProj (α := α) q)

end NormalizeCompat

end InfoGeometry.PositiveMeasure

end Normalize
