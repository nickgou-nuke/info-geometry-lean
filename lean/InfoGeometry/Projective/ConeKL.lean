import InfoGeometry.Projective.FaithfulKL
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.Normalize
set_option linter.unnecessarySimpa false

/-!
# Cone-facing KL/Gauge Reduction

Lifted KL/gauge decomposition to projective and cone-interior state-space
interfaces, with compatibility wrappers to the legacy `PositiveMeasure` API.
-/

namespace InfoGeometry.Projective.ConeKL
end InfoGeometry.Projective.ConeKL

namespace InfoGeometry.Projective

section ConeFacingKL

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Rays in the interior of the positive orthant cone. -/
abbrev OrthantConeInteriorStateSpace :=
  ConeInteriorStateSpace ((positiveOrthant (α := α)).cone)

/-- KL-like divergence on projective classes via canonical simplex representatives. -/
noncomputable def klLikeOnProj
    (q r : PositiveMeasure.Proj (α := α)) : ℝ :=
  PositiveMeasure.klLike (α := α)
    (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q)
    (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) r)

/-- Generalized KL on projective classes via canonical simplex representatives. -/
noncomputable def generalizedKLOnProj
    (q r : PositiveMeasure.Proj (α := α)) : ℝ :=
  PositiveMeasure.generalizedKL (α := α)
    (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q)
    (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) r)

@[simp] lemma klLikeOnProj_mk
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    klLikeOnProj (α := α) (Quotient.mk _ μ) (Quotient.mk _ ν)
      =
    PositiveMeasure.klLike (α := α)
      (PositiveMeasure.normalize (α := α) (R := ℝ) μ)
      (PositiveMeasure.normalize (α := α) (R := ℝ) ν) := by
  simp [klLikeOnProj, InfoGeometry.Projective.Normalize.normalizeOnProj_mk]

@[simp] lemma generalizedKLOnProj_mk
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    generalizedKLOnProj (α := α) (Quotient.mk _ μ) (Quotient.mk _ ν)
      =
    PositiveMeasure.generalizedKL (α := α)
      (PositiveMeasure.normalize (α := α) (R := ℝ) μ)
      (PositiveMeasure.normalize (α := α) (R := ℝ) ν) := by
  simp [generalizedKLOnProj, InfoGeometry.Projective.Normalize.normalizeOnProj_mk]

/-- On projective classes (simplex gauge), generalized KL equals `klLike`. -/
@[simp] lemma generalizedKLOnProj_eq_klLikeOnProj
    (q r : PositiveMeasure.Proj (α := α)) :
    generalizedKLOnProj (α := α) q r = klLikeOnProj (α := α) q r := by
  refine Quotient.inductionOn₂ q r ?_
  intro μ ν
  simpa [generalizedKLOnProj, klLikeOnProj, InfoGeometry.Projective.Normalize.normalizeOnProj_mk] using
    (PositiveMeasure.generalizedKL_normalize_eq_klLike_normalize (α := α) μ ν)

/-- Faithful nonnegativity in projective gauge. -/
lemma generalizedKLOnProj_nonneg
    (q r : PositiveMeasure.Proj (α := α)) :
    0 ≤ generalizedKLOnProj (α := α) q r := by
  refine Quotient.inductionOn₂ q r ?_
  intro μ ν
  simpa [generalizedKLOnProj, InfoGeometry.Projective.Normalize.normalizeOnProj_mk] using
    (PositiveMeasure.generalizedKL_normalize_nonneg (α := α) μ ν)

/-- Faithful nonnegativity of the KL-like projective form. -/
lemma klLikeOnProj_nonneg
    (q r : PositiveMeasure.Proj (α := α)) :
    0 ≤ klLikeOnProj (α := α) q r := by
  have h := generalizedKLOnProj_nonneg (α := α) q r
  simpa [generalizedKLOnProj_eq_klLikeOnProj (α := α) (q := q) (r := r)] using h

/-- Radial/projective decomposition with the projective part expressed by `generalizedKLOnProj`. -/
lemma generalizedKL_projective_radial_decomposition_onProj
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    PositiveMeasure.generalizedKL (α := α) μ ν
      =
    PositiveMeasure.Z (α := α) (R := ℝ) μ
      * generalizedKLOnProj (α := α) (Quotient.mk _ μ) (Quotient.mk _ ν)
      + PositiveMeasure.gklTerm
          (PositiveMeasure.Z (α := α) (R := ℝ) μ)
          (PositiveMeasure.Z (α := α) (R := ℝ) ν) := by
  simpa [generalizedKLOnProj, InfoGeometry.Projective.Normalize.normalizeOnProj_mk] using
    (PositiveMeasure.generalizedKL_projective_radial_decomposition (α := α) μ ν)

/-- Cone-facing KL-like divergence via canonical simplex representatives. -/
noncomputable def klLikeOnConeInteriorStateSpace
    (s t : OrthantConeInteriorStateSpace (α := α)) : ℝ :=
  PositiveMeasure.klLike (α := α)
    (InfoGeometry.Projective.Normalize.normalizeOnConeInteriorStateSpace (α := α) s)
    (InfoGeometry.Projective.Normalize.normalizeOnConeInteriorStateSpace (α := α) t)

/-- Cone-facing generalized KL via canonical simplex representatives. -/
noncomputable def generalizedKLOnConeInteriorStateSpace
    (s t : OrthantConeInteriorStateSpace (α := α)) : ℝ :=
  PositiveMeasure.generalizedKL (α := α)
    (InfoGeometry.Projective.Normalize.normalizeOnConeInteriorStateSpace (α := α) s)
    (InfoGeometry.Projective.Normalize.normalizeOnConeInteriorStateSpace (α := α) t)

@[simp] lemma klLikeOnConeInteriorStateSpace_projectiveClass
    (q r : PositiveMeasure.Proj (α := α)) :
    klLikeOnConeInteriorStateSpace (α := α)
      (projectiveClassToConeInteriorStateSpace (α := α) q)
      (projectiveClassToConeInteriorStateSpace (α := α) r)
      =
    klLikeOnProj (α := α) q r := by
  simp [klLikeOnConeInteriorStateSpace, klLikeOnProj, InfoGeometry.Projective.Normalize.normalizeOnProj]

@[simp] lemma generalizedKLOnConeInteriorStateSpace_projectiveClass
    (q r : PositiveMeasure.Proj (α := α)) :
    generalizedKLOnConeInteriorStateSpace (α := α)
      (projectiveClassToConeInteriorStateSpace (α := α) q)
      (projectiveClassToConeInteriorStateSpace (α := α) r)
      =
    generalizedKLOnProj (α := α) q r := by
  simp [generalizedKLOnConeInteriorStateSpace, generalizedKLOnProj,
    InfoGeometry.Projective.Normalize.normalizeOnProj]

/-- Cone-facing gauge reduction: generalized KL equals `klLike`. -/
@[simp] lemma generalizedKLOnConeInteriorStateSpace_eq_klLikeOnConeInteriorStateSpace
    (s t : OrthantConeInteriorStateSpace (α := α)) :
    generalizedKLOnConeInteriorStateSpace (α := α) s t
      =
    klLikeOnConeInteriorStateSpace (α := α) s t := by
  let q := coneInteriorStateSpaceToProjectiveClass (α := α) s
  let r := coneInteriorStateSpaceToProjectiveClass (α := α) t
  have hs :
      projectiveClassToConeInteriorStateSpace (α := α) q = s := by
    simpa [q] using
      (coneInteriorStateSpaceToProjectiveClass_apply (α := α) s)
  have ht :
      projectiveClassToConeInteriorStateSpace (α := α) r = t := by
    simpa [r] using
      (coneInteriorStateSpaceToProjectiveClass_apply (α := α) t)
  calc
    generalizedKLOnConeInteriorStateSpace (α := α) s t
        =
      generalizedKLOnConeInteriorStateSpace (α := α)
        (projectiveClassToConeInteriorStateSpace (α := α) q)
        (projectiveClassToConeInteriorStateSpace (α := α) r) := by
          simp [hs, ht]
    _ = generalizedKLOnProj (α := α) q r := by
          simpa using
            generalizedKLOnConeInteriorStateSpace_projectiveClass (α := α) q r
    _ = klLikeOnProj (α := α) q r := by
          simpa using generalizedKLOnProj_eq_klLikeOnProj (α := α) q r
    _ =
      klLikeOnConeInteriorStateSpace (α := α)
        (projectiveClassToConeInteriorStateSpace (α := α) q)
        (projectiveClassToConeInteriorStateSpace (α := α) r) := by
          symm
          simpa using klLikeOnConeInteriorStateSpace_projectiveClass (α := α) q r
    _ = klLikeOnConeInteriorStateSpace (α := α) s t := by
          simp [hs, ht]

/-- Cone-facing faithful nonnegativity for generalized KL. -/
lemma generalizedKLOnConeInteriorStateSpace_nonneg
    (s t : OrthantConeInteriorStateSpace (α := α)) :
    0 ≤ generalizedKLOnConeInteriorStateSpace (α := α) s t := by
  unfold generalizedKLOnConeInteriorStateSpace
  exact PositiveMeasure.generalizedKL_nonneg _ _

/-- Cone-facing faithful nonnegativity for KL-like divergence. -/
lemma klLikeOnConeInteriorStateSpace_nonneg
    (s t : OrthantConeInteriorStateSpace (α := α)) :
    0 ≤ klLikeOnConeInteriorStateSpace (α := α) s t := by
  have h := generalizedKLOnConeInteriorStateSpace_nonneg (α := α) s t
  simpa [generalizedKLOnConeInteriorStateSpace_eq_klLikeOnConeInteriorStateSpace
    (α := α) (s := s) (t := t)] using h

end ConeFacingKL

end InfoGeometry.Projective

namespace InfoGeometry.PositiveMeasure

section ConeFacingKLWrappers

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Backward-compatible wrapper for projective KL-like divergence. -/
noncomputable abbrev klLikeOnProj
    (q r : Proj (α := α)) : ℝ :=
  InfoGeometry.Projective.klLikeOnProj (α := α) q r

/-- Backward-compatible wrapper for projective generalized KL. -/
noncomputable abbrev generalizedKLOnProj
    (q r : Proj (α := α)) : ℝ :=
  InfoGeometry.Projective.generalizedKLOnProj (α := α) q r

/-- Backward-compatible wrapper for cone-facing KL-like divergence. -/
noncomputable abbrev klLikeOnConeInteriorStateSpace
    (s t : InfoGeometry.Projective.ConeInteriorStateSpace
      ((InfoGeometry.Projective.positiveOrthant (α := α)).cone)) : ℝ :=
  InfoGeometry.Projective.klLikeOnConeInteriorStateSpace (α := α) s t

/-- Backward-compatible wrapper for cone-facing generalized KL. -/
noncomputable abbrev generalizedKLOnConeInteriorStateSpace
    (s t : InfoGeometry.Projective.ConeInteriorStateSpace
      ((InfoGeometry.Projective.positiveOrthant (α := α)).cone)) : ℝ :=
  InfoGeometry.Projective.generalizedKLOnConeInteriorStateSpace (α := α) s t

@[simp] lemma klLikeOnProj_mk
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    klLikeOnProj (α := α) (Quotient.mk _ μ) (Quotient.mk _ ν)
      =
    klLike (α := α)
      (normalize (α := α) (R := ℝ) μ)
      (normalize (α := α) (R := ℝ) ν) := by
  simpa [klLikeOnProj] using
    (InfoGeometry.Projective.klLikeOnProj_mk (α := α) μ ν)

@[simp] lemma generalizedKLOnProj_mk
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    generalizedKLOnProj (α := α) (Quotient.mk _ μ) (Quotient.mk _ ν)
      =
    generalizedKL (α := α)
      (normalize (α := α) (R := ℝ) μ)
      (normalize (α := α) (R := ℝ) ν) := by
  simpa [generalizedKLOnProj] using
    (InfoGeometry.Projective.generalizedKLOnProj_mk (α := α) μ ν)

@[simp] lemma generalizedKLOnProj_eq_klLikeOnProj
    (q r : Proj (α := α)) :
    generalizedKLOnProj (α := α) q r = klLikeOnProj (α := α) q r := by
  simpa [generalizedKLOnProj, klLikeOnProj] using
    (InfoGeometry.Projective.generalizedKLOnProj_eq_klLikeOnProj (α := α) q r)

end ConeFacingKLWrappers

end InfoGeometry.PositiveMeasure