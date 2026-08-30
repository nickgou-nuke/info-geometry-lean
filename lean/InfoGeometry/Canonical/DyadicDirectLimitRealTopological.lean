import InfoGeometry.Canonical.RealUHFProjectionRankRationalIntervalDensity
import InfoGeometry.Canonical.DyadicDirectLimitTopology

/-!
# Topological readout of the dyadic direct limit

The algebraic quotient `DyadicDirectLimit` is transported to its dyadic
rational model and then to the real line.  This owner proves the dense
readout and its finite-stage formula; it does not assert a completion or a
C*-algebraic identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.DyadicDirectLimitRealTopological

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFProjectionRankRationalIntervalDensity

def dyadicDirectLimitRealReadout : DyadicDirectLimit → ℝ :=
  fun x => ((dyadicDirectLimitEquiv x : DyadicRational) : ℚ)

def dyadicRationalRealEmbedding : DyadicRational → ℝ :=
  fun q => (q : ℚ)

theorem dyadicRationalRealEmbedding_isEmbedding :
    Topology.IsEmbedding dyadicRationalRealEmbedding := by
  simpa [dyadicRationalRealEmbedding, Function.comp_def] using
    (Rat.isDenseEmbedding_coe_real.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : DyadicRational → ℚ)))

def dyadicRationalRealEmbeddingAddHom : DyadicRational →+ ℝ where
  toFun := dyadicRationalRealEmbedding
  map_zero' := by
    simp [dyadicRationalRealEmbedding]
  map_add' x y := by
    simp only [dyadicRationalRealEmbedding]
    norm_num

theorem continuous_dyadicRationalRealEmbedding :
    Continuous dyadicRationalRealEmbedding := by
  exact (continuous_induced_dom :
    Continuous (fun q : ℚ => (q : ℝ))).comp continuous_subtype_val

theorem dyadicRationalRealEmbedding_isometry :
    Isometry dyadicRationalRealEmbedding := by
  intro x y
  rw [edist_dist, edist_dist]
  congr 1

theorem uniformContinuous_dyadicRationalRealEmbedding :
    UniformContinuous dyadicRationalRealEmbedding := by
  exact uniformContinuous_of_continuousAt_zero
    dyadicRationalRealEmbeddingAddHom
    continuous_dyadicRationalRealEmbedding.continuousAt

noncomputable def dyadicRationalCompletionRealExtension :
    UniformSpace.Completion DyadicRational → ℝ :=
  UniformSpace.Completion.extension dyadicRationalRealEmbedding

theorem dyadicRationalCompletionRealExtension_coe
    (q : DyadicRational) :
    dyadicRationalCompletionRealExtension (q : UniformSpace.Completion DyadicRational) =
      dyadicRationalRealEmbedding q := by
  exact UniformSpace.Completion.extension_coe
    uniformContinuous_dyadicRationalRealEmbedding q

theorem denseRange_dyadicRationalRealEmbedding :
    DenseRange dyadicRationalRealEmbedding := by
  rw [DenseRange]
  have hset :
      Set.range (fun q : DyadicRational => ((q : ℚ) : ℝ)) =
        (Rat.cast : ℚ → ℝ) '' (dyadicRational : Set ℚ) := by
    ext q
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.property, rfl⟩
    · intro hq
      rcases hq with ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  change Dense (Set.range (fun q : DyadicRational => ((q : ℚ) : ℝ)))
  rw [hset]
  exact dense_dyadic_cast

theorem denseRange_dyadicRationalCompletionRealExtension :
    DenseRange dyadicRationalCompletionRealExtension := by
  rw [DenseRange]
  apply Dense.mono (s₁ := Set.range dyadicRationalRealEmbedding)
  · rintro y ⟨q, rfl⟩
    refine ⟨(q : UniformSpace.Completion DyadicRational), ?_⟩
    exact dyadicRationalCompletionRealExtension_coe q
  · exact denseRange_dyadicRationalRealEmbedding

theorem dyadicRationalCompletionRealExtension_isometry :
    Isometry dyadicRationalCompletionRealExtension := by
  exact Isometry.completion_extension
    dyadicRationalRealEmbedding_isometry

theorem dyadicRationalCompletionRealExtension_surjective :
    Function.Surjective dyadicRationalCompletionRealExtension := by
  have hclosed :
      IsClosed (Set.range dyadicRationalCompletionRealExtension) :=
    (dyadicRationalCompletionRealExtension_isometry.isClosedEmbedding).isClosed_range
  have hdense := denseRange_dyadicRationalCompletionRealExtension
  have hclosure :
      closure (Set.range dyadicRationalCompletionRealExtension) = Set.univ :=
    dense_iff_closure_eq.mp hdense
  have hrange : Set.range dyadicRationalCompletionRealExtension = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _) ?_
    intro y
    intro hy
    exact hclosed.closure_subset (by
      rw [hclosure]
      exact hy)
  intro y
  change y ∈ Set.range dyadicRationalCompletionRealExtension
  rw [hrange]
  exact Set.mem_univ y

noncomputable def dyadicRationalCompletionRealEquiv :
    UniformSpace.Completion DyadicRational ≃ ℝ :=
  Equiv.ofBijective dyadicRationalCompletionRealExtension
    ⟨dyadicRationalCompletionRealExtension_isometry.injective,
      dyadicRationalCompletionRealExtension_surjective⟩

theorem dyadicRationalCompletionRealEquiv_symm_isometry :
    Isometry dyadicRationalCompletionRealEquiv.symm := by
  intro x y
  calc
    edist (dyadicRationalCompletionRealEquiv.symm x)
        (dyadicRationalCompletionRealEquiv.symm y) =
        edist (dyadicRationalCompletionRealExtension
          (dyadicRationalCompletionRealEquiv.symm x))
          (dyadicRationalCompletionRealExtension
            (dyadicRationalCompletionRealEquiv.symm y)) := by
          exact (dyadicRationalCompletionRealExtension_isometry _ _).symm
    _ = edist x y := by
      change edist
          (dyadicRationalCompletionRealEquiv
            (dyadicRationalCompletionRealEquiv.symm x))
          (dyadicRationalCompletionRealEquiv
            (dyadicRationalCompletionRealEquiv.symm y)) = edist x y
      rw [dyadicRationalCompletionRealEquiv.apply_symm_apply,
        dyadicRationalCompletionRealEquiv.apply_symm_apply]

noncomputable def dyadicRationalCompletionRealHomeomorph :
    UniformSpace.Completion DyadicRational ≃ₜ ℝ :=
  { toEquiv := dyadicRationalCompletionRealEquiv
    continuous_toFun := UniformSpace.Completion.continuous_extension
    continuous_invFun := dyadicRationalCompletionRealEquiv_symm_isometry.continuous }

theorem dyadicDirectLimitRealReadout_isEmbedding :
    Topology.IsEmbedding dyadicDirectLimitRealReadout := by
  have h := dyadicRationalRealEmbedding_isEmbedding.comp
    dyadicDirectLimitHomeomorph.isEmbedding
  simpa [dyadicRationalRealEmbedding, dyadicDirectLimitRealReadout,
    Function.comp_def, dyadicDirectLimitHomeomorph_apply] using h

noncomputable def dyadicDirectLimitRealReadoutHomeomorph :
    DyadicDirectLimit ≃ₜ Set.range dyadicDirectLimitRealReadout :=
  dyadicDirectLimitRealReadout_isEmbedding.toHomeomorph

def dyadicDirectLimitRealReadoutAddHom : DyadicDirectLimit →+ ℝ where
  toFun := dyadicDirectLimitRealReadout
  map_zero' := by
    simp [dyadicDirectLimitRealReadout]
  map_add' x y := by
    simp only [dyadicDirectLimitRealReadout]
    rw [dyadicDirectLimitEquiv_add]
    norm_num

@[simp] theorem dyadicDirectLimitRealReadoutAddHom_apply
    (x : DyadicDirectLimit) :
    dyadicDirectLimitRealReadoutAddHom x =
      dyadicDirectLimitRealReadout x := rfl

theorem dyadicDirectLimitRealReadout_add
    (x y : DyadicDirectLimit) :
    dyadicDirectLimitRealReadout (x + y) =
      dyadicDirectLimitRealReadout x + dyadicDirectLimitRealReadout y := by
  exact dyadicDirectLimitRealReadoutAddHom.map_add x y

theorem dyadicDirectLimitRealReadout_neg
    (x : DyadicDirectLimit) :
    dyadicDirectLimitRealReadout (-x) =
      -dyadicDirectLimitRealReadout x := by
  exact dyadicDirectLimitRealReadoutAddHom.map_neg x

theorem continuous_dyadicDirectLimitRealReadout :
    Continuous dyadicDirectLimitRealReadout := by
  have hrat : Continuous (fun q : DyadicRational => (q : ℝ)) := by
    exact (continuous_induced_dom :
      Continuous (fun q : ℚ => (q : ℝ))).comp continuous_subtype_val
  exact hrat.comp continuous_dyadicDirectLimitEquiv

def dyadicDirectLimitRealReadoutTopCatHom :
    TopCat.of DyadicDirectLimit ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := dyadicDirectLimitRealReadout
      continuous_toFun := continuous_dyadicDirectLimitRealReadout }

@[simp] theorem dyadicDirectLimitRealReadoutTopCatHom_apply
    (x : DyadicDirectLimit) :
    dyadicDirectLimitRealReadoutTopCatHom x =
      dyadicDirectLimitRealReadout x := rfl

theorem dyadicDirectLimitRealReadout_stage
    (n : ℕ) (z : ℤ) :
    dyadicDirectLimitRealReadout (dyadicStage n z) =
      ((dyadicStageMap n z : DyadicRational) : ℚ) := by
  rfl

theorem dyadicDirectLimitRealReadout_range :
    Set.range dyadicDirectLimitRealReadout =
      (Rat.cast : ℚ → ℝ) '' (dyadicRational : Set ℚ) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(dyadicDirectLimitEquiv x : DyadicRational),
      (dyadicDirectLimitEquiv x).property, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨dyadicDirectLimitEquiv.symm ⟨q, hq⟩, ?_⟩
    simp [dyadicDirectLimitRealReadout]

theorem denseRange_dyadicDirectLimitRealReadout :
    DenseRange dyadicDirectLimitRealReadout := by
  rw [DenseRange, dyadicDirectLimitRealReadout_range]
  exact dense_dyadic_cast

theorem closure_range_dyadicDirectLimitRealReadout :
    closure (Set.range dyadicDirectLimitRealReadout) =
      Set.univ := by
  exact dense_iff_closure_eq.mp
    denseRange_dyadicDirectLimitRealReadout

end InfoGeometry.Canonical.DyadicDirectLimitRealTopological
