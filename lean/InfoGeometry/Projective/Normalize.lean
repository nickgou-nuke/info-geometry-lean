import InfoGeometry.Projective.Projective

namespace InfoGeometry.Projective.Normalize
end InfoGeometry.Projective.Normalize

namespace PositiveMeasure

variable {α : Type u}

section NormalizeOnProj

variable [Fintype α] [Nonempty α]

/-- Normalization is constant on projective rays. -/
lemma normalize_eq_of_sameRay
    {μ ν : PositiveMeasure α ℝ}
    (h : SameRay μ ν) :
    normalize (α := α) (R := ℝ) μ = normalize (α := α) (R := ℝ) ν := by
  rcases h with ⟨c, hc, rfl⟩
  symm
  exact normalize_scale (α := α) (c := c) hc μ

/-- Canonical simplex representative of a projective ray. -/
noncomputable def normalizeOnProj : Proj (α := α) → PositiveMeasure α ℝ :=
  Quotient.lift
    (fun μ => normalize (α := α) (R := ℝ) μ)
    (by
      intro μ ν h
      exact normalize_eq_of_sameRay (α := α) h)

@[simp] lemma normalizeOnProj_mk (μ : PositiveMeasure α ℝ) :
    normalizeOnProj (α := α) (Quotient.mk _ μ) = normalize (α := α) (R := ℝ) μ := rfl

/-- The canonical representative has unit mass. -/
@[simp] lemma Z_normalizeOnProj (q : Proj (α := α)) :
    Z (α := α) (R := ℝ) (normalizeOnProj (α := α) q) = 1 := by
  refine Quotient.inductionOn q ?_
  intro μ
  simpa using (Z_normalize (α := α) (R := ℝ) μ)

end NormalizeOnProj

end PositiveMeasure
