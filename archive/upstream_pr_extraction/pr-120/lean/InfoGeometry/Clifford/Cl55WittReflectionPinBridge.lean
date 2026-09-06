import InfoGeometry.Clifford.Cl55RealSplitPinVectorReflection
import InfoGeometry.Clifford.Cl55WittReflectionAlignment
import InfoGeometry.Clifford.Cl55RealSplitPinReflectionImage

namespace InfoGeometry.Clifford.Clifford55

/-!
# Generic quadratic reflections in the real split-Pin image

Over `ℝ`, every anisotropic normal can be rescaled to norm `+1` or `-1`.
This owner transports the corresponding normalized split-Pin action back to
the generic quadratic reflection API.
-/

theorem quadraticReflection_mem_realSplitPin_image
    (v : V55) (hv : Q55 v ≠ 0) :
    orthogonalGroup55FromIsometry (quadraticReflectionIsometry v hv) ∈
      Subgroup.map realSplitPinOrthogonalAction ⊤ := by
  rcases exists_normalized_scalar v hv with ⟨c, hc, hnorm⟩
  have hcv : Q55 (c • v) ≠ 0 := by
    rcases hnorm with hnorm | hnorm
    · rw [hnorm]
      norm_num
    · rw [hnorm]
      norm_num
  have hunit : IsUnit (Q55 (c • v)) := by
    rcases hnorm with hnorm | hnorm
    · rw [hnorm]
      exact ⟨1, by simp⟩
    · rw [hnorm]
      exact ⟨-1, by simp⟩
  let g : realSplitPin55 :=
    ⟨normalizedVectorUnit (c • v) hunit,
      normalizedVectorUnit_mem_realSplitPin (c • v) hnorm hunit⟩
  have hg : realSplitPinOrthogonalAction g =
      orthogonalGroup55FromIsometry (quadraticReflectionIsometry v hv) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change realSplitPinTwistedAction g x = quadraticReflection v hv x
    apply ι55_injective
    calc
      ι55 (realSplitPinTwistedAction g x) =
          ι55 (normalizedVectorReflection (c • v) hunit x) :=
        normalizedVector_action_apply_ι (c • v) x hnorm hunit g.property
      _ = ι55 (quadraticReflection (c • v) hcv x) := by
        have hreflection :=
          normalizedVectorReflection_eq_quadraticReflection
            (c • v) hnorm hunit
        simpa using congrArg (fun f => ι55 (f x)) hreflection
      _ = ι55 (quadraticReflection v hv x) := by
        have hscale := quadraticReflection_smul c hc v hv
        simpa using congrArg (fun f => ι55 (f x)) hscale
  refine ⟨g, trivial, ?_⟩
  exact hg

theorem quadraticReflectionSubgroup_le_realSplitPin_image :
    quadraticReflectionSubgroup ≤
      Subgroup.map realSplitPinOrthogonalAction ⊤ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, rfl⟩
  exact quadraticReflection_mem_realSplitPin_image v hv

theorem realSplitPinImage_eq_quadraticReflectionSubgroup :
    Subgroup.map realSplitPinOrthogonalAction ⊤ =
      quadraticReflectionSubgroup := by
  apply le_antisymm
  · rw [realSplitPinImage_eq_normalizedVectorReflectionSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    rcases hu with ⟨v, hv, huv⟩
    have hmem : u ∈ normalizedVectorUnitSet := ⟨v, hv, huv⟩
    have hunit : IsUnit (Q55 v) := by
      rcases hv with hv | hv
      · rw [hv]
        exact ⟨1, by simp⟩
      · rw [hv]
        exact ⟨-1, by simp⟩
    let g : realSplitPin55 :=
      ⟨u, Subgroup.subset_closure hmem⟩
    let gcanon : realSplitPin55 :=
      ⟨normalizedVectorUnit v hunit,
        normalizedVectorUnit_mem_realSplitPin v hv hunit⟩
    have hgc : g = gcanon := by
      apply Subtype.ext
      apply Units.ext
      calc
        (u : Cl55) = ι55 v := huv.symm
        _ = (normalizedVectorUnit v hunit : Cl55) :=
          (normalizedVectorUnit_coe v hunit).symm
    have hg : realSplitPinOrthogonalAction g ∈
        quadraticReflectionSubgroup := by
      rw [hgc]
      exact normalizedVectorAction_mem_quadraticReflectionSubgroup_of_norm v hv
    simpa [g, huv] using hg
  · exact quadraticReflectionSubgroup_le_realSplitPin_image

end InfoGeometry.Clifford.Clifford55
