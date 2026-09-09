import InfoGeometry.Dynamics.ChiralHodgeAdjointBridge
import InfoGeometry.Singular.MoorePenrose

/-!
# Moore--Penrose inverse for a closed-range chiral Hodge Laplacian

This is the Hilbert-space bridge from the Hodge owner to the repository's
canonical Moore--Penrose construction.  It deliberately assumes only closed
range; no spectral gap or finite-dimensionality is asserted here.
-/

namespace InfoGeometry.Dynamics

open InfoGeometry.Singular.MoorePenrose

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def chiralHodgeMoorePenroseInverse
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) : E →L[ℝ] E :=
  moorePenroseInverse H.laplacian hClosedRange

theorem chiralHodge_laplacian_self_adjoint
    (H : ChiralHodgeAdjointData (E := E)) :
    ContinuousLinearMap.adjoint H.laplacian = H.laplacian := by
  unfold ChiralHodgeAdjointData.laplacian
  rw [map_add ContinuousLinearMap.adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    H.adjoint_eq]
  have hdelta : ContinuousLinearMap.adjoint H.delta = H.d := by
    rw [← H.adjoint_eq, ContinuousLinearMap.adjoint_adjoint]
  rw [hdelta]

theorem chiralHodge_laplacian_isStarNormal
    (H : ChiralHodgeAdjointData (E := E)) :
    IsStarNormal H.laplacian := by
  rw [ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint]
  intro x
  rw [chiralHodge_laplacian_self_adjoint H]

theorem chiralHodge_laplacian_range_orthogonal_eq_kernel
    (H : ChiralHodgeAdjointData (E := E)) :
    H.laplacian.rangeᗮ = H.laplacian.ker := by
  exact ContinuousLinearMap.IsStarNormal.orthogonal_range
    (chiralHodge_laplacian_isStarNormal H)

theorem chiralHodgeMoorePenroseInverse_spec
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    IsMoorePenroseInverseCLM H.laplacian
      (chiralHodgeMoorePenroseInverse H hClosedRange) := by
  exact isMoorePenroseInverse_moorePenroseInverse H.laplacian hClosedRange

theorem chiralHodgeMoorePenrose_range_projector_idempotent
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    (H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)).comp
        (H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)) =
      H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange) := by
  have h := chiralHodgeMoorePenroseInverse_spec H hClosedRange
  have h_id := congrArg
    (fun T : E →L[ℝ] E =>
      T.comp (chiralHodgeMoorePenroseInverse H hClosedRange)) h.1
  simpa [ContinuousLinearMap.comp_assoc] using h_id

theorem chiralHodgeMoorePenrose_range_projector_self_adjoint
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    star (H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)) =
      H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange) := by
  have h := chiralHodgeMoorePenroseInverse_spec H hClosedRange
  exact h.2.2.1

theorem chiralHodgeMoorePenrose_range_projector_range_eq_laplacian_range
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    LinearMap.range
        (H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)).toLinearMap =
      LinearMap.range H.laplacian.toLinearMap := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨chiralHodgeMoorePenroseInverse H hClosedRange x, rfl⟩
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨H.laplacian x, ?_⟩
    have h := chiralHodgeMoorePenroseInverse_spec H hClosedRange
    have h_id := congrArg
      (fun T : E →L[ℝ] E => T x) h.1
    simpa [ContinuousLinearMap.comp_apply] using h_id

theorem chiralHodgeMoorePenrose_range_projector_apply_laplacian
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E))
    (x : E) :
    H.laplacian (chiralHodgeMoorePenroseInverse H hClosedRange (H.laplacian x)) =
      H.laplacian x := by
  have h := chiralHodgeMoorePenroseInverse_spec H hClosedRange
  have h_id := congrArg (fun T : E →L[ℝ] E => T x) h.1
  simpa [ContinuousLinearMap.comp_apply] using h_id

theorem chiralHodgeMoorePenrose_range_projector_ker_eq_laplacian_ker
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    LinearMap.ker
        (H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)).toLinearMap =
      LinearMap.ker H.laplacian.toLinearMap := by
  rw [show H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange) =
      (H.laplacian.range).starProjection by
    exact moorePenroseInverse_range_projector_eq_starProjection
      H.laplacian hClosedRange]
  rw [Submodule.ker_starProjection]
  exact chiralHodge_laplacian_range_orthogonal_eq_kernel H

noncomputable def chiralHodgeHarmonicProjector
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E -
    H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)

theorem chiralHodgeHarmonicProjector_range_eq_laplacian_ker
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    LinearMap.range (chiralHodgeHarmonicProjector H hClosedRange).toLinearMap =
      LinearMap.ker H.laplacian.toLinearMap := by
  let P := H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)
  have hP : IsIdempotentElem P.toLinearMap := by
    change (P.comp P).toLinearMap = P.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap
      (chiralHodgeMoorePenrose_range_projector_idempotent H hClosedRange)
  have hker : LinearMap.ker P.toLinearMap =
      LinearMap.range (LinearMap.id - P.toLinearMap) :=
    LinearMap.IsIdempotentElem.ker_eq_range hP
  change LinearMap.range (LinearMap.id - P.toLinearMap) =
    LinearMap.ker H.laplacian.toLinearMap
  rw [← hker]
  simpa [P] using
    chiralHodgeMoorePenrose_range_projector_ker_eq_laplacian_ker H hClosedRange

/-- The canonical Moore--Penrose inverse vanishes on the harmonic kernel. -/
theorem chiralHodgeMoorePenroseInverse_apply_of_laplacian_mem_ker
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E))
    {x : E} (hx : H.laplacian x = 0) :
    chiralHodgeMoorePenroseInverse H hClosedRange x = 0 := by
  rw [show chiralHodgeMoorePenroseInverse H hClosedRange =
      ((H.laplacian.ker)ᗮ).subtypeL.comp
        ((mpEquiv H.laplacian hClosedRange).symm.toContinuousLinearMap.comp
          (Submodule.orthogonalProjection H.laplacian.range)) by
    rfl]
  have hx_orth : x ∈ (H.laplacian.range)ᗮ := by
    rw [show (H.laplacian.range)ᗮ = H.laplacian.ker by
      exact chiralHodge_laplacian_range_orthogonal_eq_kernel H]
    change H.laplacian x = 0
    exact hx
  have hproj : Submodule.orthogonalProjection H.laplacian.range x = 0 := by
    exact Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hx_orth
  simp [hproj]

/-- The canonical Green inverse takes values in the regular orthogonal sector. -/
theorem chiralHodgeMoorePenroseInverse_range_le_ker_laplacian_orthogonal
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    LinearMap.range
        (chiralHodgeMoorePenroseInverse H hClosedRange).toLinearMap ≤
      (LinearMap.ker H.laplacian.toLinearMap)ᗮ := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  change (chiralHodgeMoorePenroseInverse H hClosedRange x) ∈
    (LinearMap.ker H.laplacian.toLinearMap)ᗮ
  rw [show chiralHodgeMoorePenroseInverse H hClosedRange =
      ((H.laplacian.ker)ᗮ).subtypeL.comp
        ((mpEquiv H.laplacian hClosedRange).symm.toContinuousLinearMap.comp
          (Submodule.orthogonalProjection H.laplacian.range)) by
    rfl]
  simpa [ContinuousLinearMap.comp_apply] using
    (mpEquiv H.laplacian hClosedRange).symm
      (Submodule.orthogonalProjection H.laplacian.range x).property

/-- The harmonic projector is the identity on harmonic vectors. -/
theorem chiralHodgeHarmonicProjector_apply_of_laplacian_mem_ker
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E))
    {x : E} (hx : H.laplacian x = 0) :
    chiralHodgeHarmonicProjector H hClosedRange x = x := by
  unfold chiralHodgeHarmonicProjector
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,
    chiralHodgeMoorePenroseInverse_apply_of_laplacian_mem_ker H hClosedRange hx,
    map_zero, sub_zero]

/-- The harmonic projector is idempotent. -/
theorem chiralHodgeHarmonicProjector_idempotent
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    (chiralHodgeHarmonicProjector H hClosedRange).comp
        (chiralHodgeHarmonicProjector H hClosedRange) =
      chiralHodgeHarmonicProjector H hClosedRange := by
  let P := H.laplacian.comp (chiralHodgeMoorePenroseInverse H hClosedRange)
  have hP : P.comp P = P := by
    exact chiralHodgeMoorePenrose_range_projector_idempotent H hClosedRange
  change (ContinuousLinearMap.id ℝ E - P).comp
      (ContinuousLinearMap.id ℝ E - P) = ContinuousLinearMap.id ℝ E - P
  ext x
  change x - P x - P (x - P x) = x - P x
  rw [map_sub]
  have hPx : P (P x) = P x := congrArg (fun T : E →L[ℝ] E => T x) hP
  rw [hPx]
  abel

/-- The harmonic projector annihilates the Laplacian range. -/
theorem chiralHodgeHarmonicProjector_comp_laplacian
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    (chiralHodgeHarmonicProjector H hClosedRange).comp H.laplacian = 0 := by
  ext x
  unfold chiralHodgeHarmonicProjector
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    chiralHodgeMoorePenrose_range_projector_apply_laplacian H hClosedRange x,
    sub_self, ContinuousLinearMap.zero_apply]

/-- The Laplacian annihilates the harmonic projector from the left. -/
theorem chiralHodgeLaplacian_comp_harmonicProjector
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    H.laplacian.comp (chiralHodgeHarmonicProjector H hClosedRange) = 0 := by
  ext x
  have hx : chiralHodgeHarmonicProjector H hClosedRange x ∈
      LinearMap.ker H.laplacian.toLinearMap := by
    rw [← chiralHodgeHarmonicProjector_range_eq_laplacian_ker H hClosedRange]
    exact ⟨x, rfl⟩
  change H.laplacian (chiralHodgeHarmonicProjector H hClosedRange x) = 0
  exact hx

/-- The harmonic projector is self-adjoint, hence orthogonal. -/
theorem chiralHodgeHarmonicProjector_self_adjoint
    (H : ChiralHodgeAdjointData (E := E))
    (hClosedRange : IsClosed (H.laplacian.range : Set E)) :
    star (chiralHodgeHarmonicProjector H hClosedRange) =
      chiralHodgeHarmonicProjector H hClosedRange := by
  unfold chiralHodgeHarmonicProjector
  rw [star_sub]
  have hP := chiralHodgeMoorePenrose_range_projector_self_adjoint H hClosedRange
  rw [ContinuousLinearMap.star_eq_adjoint] at hP
  change ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ E) -
      ContinuousLinearMap.adjoint (H.laplacian.comp
        (chiralHodgeMoorePenroseInverse H hClosedRange)) =
    ContinuousLinearMap.id ℝ E - H.laplacian.comp
      (chiralHodgeMoorePenroseInverse H hClosedRange)
  rw [ContinuousLinearMap.adjoint_id, hP]

end
end InfoGeometry.Dynamics
