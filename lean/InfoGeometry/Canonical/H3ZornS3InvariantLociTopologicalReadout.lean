import InfoGeometry.Canonical.H3ZornS3JordanTopologicalReadout
import InfoGeometry.Canonical.H3ZornS3JordanEqualizerTopologicalReadout

/-!
# Closed invariant loci for the native S₃ operations

The residual maps for the adjoint quadratic map and the cross product are
already owned by the S₃/Jordan readout.  This module records their intrinsic
topological equalizers.  The equalizers are closed because the residual maps
are continuous, and they are the whole carrier because the corresponding
algebraic preservation laws hold for every element of `S3Perm`.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

def S3CrossProductEqualizer (σ : S3Perm) :
    Set (H3Zorn ℝ × H3Zorn ℝ) :=
  {p | S3CrossProductResidual σ p = 0}

theorem isClosed_S3CrossProductEqualizer (σ : S3Perm) :
    IsClosed (S3CrossProductEqualizer σ) := by
  change IsClosed ((S3CrossProductResidual σ) ⁻¹' ({0} : Set (H3Zorn ℝ)))
  exact isClosed_singleton.preimage (continuous_S3CrossProductResidual σ)

theorem S3CrossProductResidual_eq_zero (σ : S3Perm)
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3CrossProductResidual σ p = 0 := by
  unfold S3CrossProductResidual
  rw [S3OnH3Zorn_preserve_crossProduct_of_adjoint σ
    (S3OnH3Zorn_preserve_adjointQuad σ)]
  exact sub_self _

theorem S3CrossProductEqualizer_eq_univ (σ : S3Perm) :
    S3CrossProductEqualizer σ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact S3CrossProductResidual_eq_zero σ p

def S3AdjointEqualizer (σ : S3Perm) : Set (H3Zorn ℝ) :=
  {X | S3AdjointResidual σ X = 0}

theorem isClosed_S3AdjointEqualizer (σ : S3Perm) :
    IsClosed (S3AdjointEqualizer σ) := by
  change IsClosed ((S3AdjointResidual σ) ⁻¹' ({0} : Set (H3Zorn ℝ)))
  exact isClosed_singleton.preimage (continuous_S3AdjointResidual σ)

theorem S3AdjointResidual_eq_zero (σ : S3Perm) (X : H3Zorn ℝ) :
    S3AdjointResidual σ X = 0 := by
  unfold S3AdjointResidual
  rw [S3OnH3Zorn_preserve_adjointQuad]
  exact sub_self _

theorem S3AdjointEqualizer_eq_univ (σ : S3Perm) :
    S3AdjointEqualizer σ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro X
  exact S3AdjointResidual_eq_zero σ X

theorem S3OnH3ZornHomeomorph_normCubic_level_eq
    (σ : S3Perm) (r : ℝ) :
    S3OnH3ZornHomeomorph σ ''
        {X : H3Zorn ℝ | H3Zorn.normCubic X = r} =
      {X : H3Zorn ℝ | H3Zorn.normCubic X = r} := by
  apply Set.Subset.antisymm
  · rintro Y ⟨X, hX, rfl⟩
    change H3Zorn.normCubic (S3OnH3Zorn σ X) = r
    rw [S3OnH3Zorn_preserve_normCubic]
    exact hX
  · intro Y hY
    refine ⟨S3OnH3Zorn (S3Perm.inverse σ) Y, ?_, ?_⟩
    · change H3Zorn.normCubic (S3OnH3Zorn (S3Perm.inverse σ) Y) = r
      rw [S3OnH3Zorn_preserve_normCubic]
      exact hY
    · change S3OnH3Zorn σ (S3OnH3Zorn (S3Perm.inverse σ) Y) = Y
      exact S3OnH3Zorn_inverse_right σ Y

end InfoGeometry.Canonical
