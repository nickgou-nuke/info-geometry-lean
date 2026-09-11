import InfoGeometry.Canonical.SE2SouriauNoncompact
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SE2SouriauAffineAction

/-!
# Translation-subgroup orbits in the affine chart

The pure `x`-translation one-parameter subgroup has horizontal-line orbits in
`Point2`.  This is the noncompact affine counterpart of the compact rotation
quadratic-level orbits.
-/

namespace InfoGeometry.Canonical.SE2SouriauCocycle

def translationAffineOrbitMap (v : Point2) :
    ℝ → Point2 := fun x => affinePointAction (translationLine x) v

theorem continuous_translationAffineOrbitMap (v : Point2) :
    Continuous (translationAffineOrbitMap v) := by
  unfold translationAffineOrbitMap
  exact continuous_affinePointAction.comp
    (continuous_translationLine.prodMk continuous_const)

def translationAffineOrbit (v : Point2) : Set Point2 :=
  Set.range (translationAffineOrbitMap v)

theorem isConnected_translationAffineOrbit (v : Point2) :
    IsConnected (translationAffineOrbit v) := by
  unfold translationAffineOrbit
  rw [← Set.image_univ]
  exact isConnected_univ.image (translationAffineOrbitMap v)
    (continuous_translationAffineOrbitMap v).continuousOn

theorem isPathConnected_translationAffineOrbit (v : Point2) :
    IsPathConnected (translationAffineOrbit v) := by
  unfold translationAffineOrbit
  rw [← Set.image_univ]
  exact isPathConnected_univ.image (continuous_translationAffineOrbitMap v)

abbrev TranslationAffineOrbitCarrier (v : Point2) :=
  {w : Point2 // w ∈ translationAffineOrbit v}

def horizontalAffineLine (v : Point2) : Set Point2 :=
  {w | w.2 = v.2}

def translationOrbitHeight : Point2 → ℝ := Prod.snd

theorem continuous_translationOrbitHeight :
    Continuous translationOrbitHeight := by
  exact continuous_snd

abbrev HorizontalAffineLineCarrier (v : Point2) :=
  {w : Point2 // w ∈ horizontalAffineLine v}

theorem translationAffineOrbitMap_formula (v : Point2) (x : ℝ) :
    translationAffineOrbitMap v x = (v.1 + x, v.2) := by
  ext <;> dsimp [translationAffineOrbitMap, affinePointAction,
    translationLine]
  · ring
  · ring

theorem translationOrbitHeight_translation_invariant
    (x : ℝ) (v : Point2) :
    translationOrbitHeight (affinePointAction (translationLine x) v) =
      translationOrbitHeight v := by
  change translationOrbitHeight (translationAffineOrbitMap v x) =
    translationOrbitHeight v
  rw [translationAffineOrbitMap_formula]
  rfl

theorem translationAffineOrbitMap_add (v : Point2) (x y : ℝ) :
    translationAffineOrbitMap v (x + y) =
      affinePointAction (translationLine x) (translationAffineOrbitMap v y) := by
  unfold translationAffineOrbitMap
  rw [← affinePointAction_mul, ← translationLine_add]

theorem translationAffineOrbit_image_action (v : Point2) (x : ℝ) :
    affinePointAction (translationLine x) '' translationAffineOrbit v =
      translationAffineOrbit v := by
  ext w
  constructor
  · rintro ⟨u, ⟨y, rfl⟩, rfl⟩
    refine ⟨x + y, ?_⟩
    exact translationAffineOrbitMap_add v x y
  · rintro ⟨y, rfl⟩
    refine ⟨translationAffineOrbitMap v (y - x), ⟨y - x, rfl⟩, ?_⟩
    rw [← translationAffineOrbitMap_add]
    ring_nf

theorem translationAffineOrbitMap_injective (v : Point2) :
    Function.Injective (translationAffineOrbitMap v) := by
  intro x y hxy
  have hfirst := congrArg Prod.fst hxy
  simpa [translationAffineOrbitMap_formula] using add_left_cancel hfirst

theorem isEmbedding_translationAffineOrbitMap (v : Point2) :
    Topology.IsEmbedding (translationAffineOrbitMap v) := by
  have hleft : Function.LeftInverse
      (fun w : Point2 => w.1 - v.1) (translationAffineOrbitMap v) := by
    intro x
    change (translationAffineOrbitMap v x).1 - v.1 = x
    rw [translationAffineOrbitMap_formula]
    ring
  exact hleft.isEmbedding (continuous_fst.sub continuous_const)
    (continuous_translationAffineOrbitMap v)

def translationAffineOrbitHomeomorph (v : Point2) :
    ℝ ≃ₜ TranslationAffineOrbitCarrier v where
  toFun := fun x =>
    ⟨translationAffineOrbitMap v x, ⟨x, rfl⟩⟩
  invFun := fun w => w.1.1 - v.1
  left_inv := by
    intro x
    change (translationAffineOrbitMap v x).1 - v.1 = x
    rw [translationAffineOrbitMap_formula]
    ring
  right_inv := by
    intro w
    dsimp
    apply Subtype.ext
    change translationAffineOrbitMap v (w.1.1 - v.1) = w.1
    rw [translationAffineOrbitMap_formula]
    apply Prod.ext
    · ring
    · have hw : w.1.2 = v.2 := by
        rcases w.2 with ⟨x, hx⟩
        have hsnd := congrArg Prod.snd hx
        rw [translationAffineOrbitMap_formula] at hsnd
        exact hsnd.symm
      exact hw.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_translationAffineOrbitMap v
  continuous_invFun := by
    exact (continuous_fst.comp continuous_subtype_val).sub continuous_const

theorem pathConnectedSpace_translationAffineOrbitCarrier (v : Point2) :
    PathConnectedSpace (TranslationAffineOrbitCarrier v) := by
  exact (translationAffineOrbitHomeomorph v).surjective.pathConnectedSpace
    (translationAffineOrbitHomeomorph v).continuous_toFun

theorem translationAffineOrbit_eq_horizontalAffineLine (v : Point2) :
    translationAffineOrbit v = horizontalAffineLine v := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    rw [translationAffineOrbitMap_formula]
    rfl
  · intro hw
    refine ⟨w.1 - v.1, ?_⟩
    rw [translationAffineOrbitMap_formula]
    dsimp [horizontalAffineLine] at hw
    ext <;> ring_nf
    exact hw.symm

theorem translationAffineOrbit_eq_height_fiber (v : Point2) :
    translationAffineOrbit v =
      translationOrbitHeight ⁻¹' ({v.2} : Set ℝ) := by
  rw [translationAffineOrbit_eq_horizontalAffineLine]
  ext w
  constructor
  · intro hw
    change w.2 = v.2 at hw
    change translationOrbitHeight w ∈ ({v.2} : Set ℝ)
    exact Set.mem_singleton_iff.mpr hw
  · intro hw
    change translationOrbitHeight w ∈ ({v.2} : Set ℝ) at hw
    exact Set.mem_singleton_iff.mp hw

theorem translationAffineOrbit_eq_iff_height_eq (v w : Point2) :
    translationAffineOrbit v = translationAffineOrbit w ↔ v.2 = w.2 := by
  constructor
  · intro horbit
    have hv : v ∈ translationAffineOrbit v := by
      exact ⟨0, by rw [translationAffineOrbitMap_formula]; ext <;> ring⟩
    have hv' : v ∈ translationAffineOrbit w := by
      rw [← horbit]
      exact hv
    rw [translationAffineOrbit_eq_horizontalAffineLine] at hv'
    exact hv'
  · intro hheight
    rw [translationAffineOrbit_eq_height_fiber,
      translationAffineOrbit_eq_height_fiber, hheight]

theorem translationOrbitHeight_surjective :
    Function.Surjective translationOrbitHeight := by
  intro y
  exact ⟨(0, y), rfl⟩

def translationOrbitSetoid : Setoid Point2 where
  r v w := v.2 = w.2
  iseqv := {
    refl := by intro v; rfl
    symm := by intro v w h; exact h.symm
    trans := by intro u v w huv hvw; exact huv.trans hvw }

def translationOrbitQuotientHeight :
    Quotient translationOrbitSetoid → ℝ :=
  Quotient.lift translationOrbitHeight (by
    intro v w h
    exact h)

theorem translationOrbitQuotientHeight_mk (v : Point2) :
    translationOrbitQuotientHeight (Quotient.mk'' v) = v.2 := rfl

theorem translationOrbitQuotientHeight_comp_mk :
    translationOrbitQuotientHeight ∘ Quotient.mk'' = translationOrbitHeight := by
  rfl

theorem translationOrbitQuotientHeight_surjective :
    Function.Surjective translationOrbitQuotientHeight := by
  intro y
  refine ⟨Quotient.mk'' (0, y), ?_⟩
  rfl

theorem translationOrbitQuotientHeight_injective :
    Function.Injective translationOrbitQuotientHeight := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h v =>
    induction q₂ using Quotient.inductionOn with
    | h w =>
      apply Quotient.sound
      exact h

def translationOrbitQuotientHeightEquiv :
    Quotient translationOrbitSetoid ≃ ℝ where
  toFun := translationOrbitQuotientHeight
  invFun := fun y => Quotient.mk'' (0, y)
  left_inv := by
    intro q
    apply translationOrbitQuotientHeight_injective
    rfl
  right_inv := by
    intro y
    rfl

theorem continuous_translationOrbitQuotientHeight :
    Continuous translationOrbitQuotientHeight := by
  apply Continuous.quotient_lift continuous_translationOrbitHeight

noncomputable def translationOrbitQuotientHomeomorph :
    Quotient translationOrbitSetoid ≃ₜ ℝ where
  toFun := translationOrbitQuotientHeight
  invFun := fun y => Quotient.mk'' (0, y)
  left_inv := by
    intro q
    apply translationOrbitQuotientHeight_injective
    rfl
  right_inv := by
    intro y
    rfl
  continuous_toFun := continuous_translationOrbitQuotientHeight
  continuous_invFun := by
    letI : Setoid Point2 := translationOrbitSetoid
    change Continuous (Quotient.mk' ∘ fun y : ℝ => (0, y))
    exact continuous_quotient_mk'.comp (by fun_prop)

theorem isClosedMap_translationOrbitQuotientHeight :
    IsClosedMap translationOrbitQuotientHeight := by
  exact translationOrbitQuotientHomeomorph.isClosedMap

theorem isOpenMap_translationOrbitQuotientHeight :
    IsOpenMap translationOrbitQuotientHeight := by
  exact translationOrbitQuotientHomeomorph.isOpenMap

theorem isProperMap_translationOrbitQuotientHeight :
    IsProperMap translationOrbitQuotientHeight := by
  exact translationOrbitQuotientHomeomorph.isProperMap

theorem isQuotientMap_translationOrbitQuotientHeight :
    Topology.IsQuotientMap translationOrbitQuotientHeight := by
  exact translationOrbitQuotientHomeomorph.isQuotientMap

theorem t2Space_translationOrbitQuotient :
    T2Space (Quotient translationOrbitSetoid) := by
  exact translationOrbitQuotientHomeomorph.symm.t2Space

theorem secondCountableTopology_translationOrbitQuotient :
    SecondCountableTopology (Quotient translationOrbitSetoid) := by
  exact translationOrbitQuotientHomeomorph.secondCountableTopology

theorem locallyCompactSpace_translationOrbitQuotient :
    LocallyCompactSpace (Quotient translationOrbitSetoid) := by
  exact translationOrbitQuotientHomeomorph.isClosedEmbedding.locallyCompactSpace

theorem pathConnectedSpace_translationOrbitQuotient :
    PathConnectedSpace (Quotient translationOrbitSetoid) := by
  exact translationOrbitQuotientHomeomorph.symm.surjective.pathConnectedSpace
    translationOrbitQuotientHomeomorph.symm.continuous_toFun

theorem translationOrbitSetoid_rel_iff_orbit_eq (v w : Point2) :
    translationOrbitSetoid.r v w ↔
      translationAffineOrbit v = translationAffineOrbit w := by
  simpa [translationOrbitSetoid] using
    (translationAffineOrbit_eq_iff_height_eq v w).symm

def translationOrbitQuotientAction (x : ℝ) :
    Quotient translationOrbitSetoid → Quotient translationOrbitSetoid :=
  Quotient.lift
    (fun v => Quotient.mk'' (affinePointAction (translationLine x) v))
    (by
      intro v w h
      apply Quotient.sound
      change translationOrbitHeight
          (affinePointAction (translationLine x) v) =
        translationOrbitHeight
          (affinePointAction (translationLine x) w)
      rw [translationOrbitHeight_translation_invariant,
        translationOrbitHeight_translation_invariant]
      exact h)

theorem translationOrbitQuotientAction_mk (x : ℝ) (v : Point2) :
    translationOrbitQuotientAction x (Quotient.mk'' v) =
      Quotient.mk'' (affinePointAction (translationLine x) v) := rfl

theorem translationOrbitQuotientAction_zero
    (q : Quotient translationOrbitSetoid) :
    translationOrbitQuotientAction 0 q = q := by
  induction q using Quotient.inductionOn with
  | h v =>
      rw [translationOrbitQuotientAction_mk, translationLine_zero,
        affinePointAction_one]

theorem translationOrbitQuotientAction_add
    (x y : ℝ) (q : Quotient translationOrbitSetoid) :
    translationOrbitQuotientAction (x + y) q =
      translationOrbitQuotientAction x
        (translationOrbitQuotientAction y q) := by
  induction q using Quotient.inductionOn with
  | h v =>
      rw [translationOrbitQuotientAction_mk,
        translationOrbitQuotientAction_mk,
        translationOrbitQuotientAction_mk, ← affinePointAction_mul,
        ← translationLine_add]

instance : AddAction ℝ (Quotient translationOrbitSetoid) where
  vadd := translationOrbitQuotientAction
  zero_vadd := translationOrbitQuotientAction_zero
  add_vadd := translationOrbitQuotientAction_add

theorem continuous_translationOrbitQuotientAction_fixed (x : ℝ) :
    Continuous (translationOrbitQuotientAction x) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_affinePointAction_fixed (translationLine x))

theorem translationOrbitQuotientHeight_action_invariant
    (x : ℝ) (q : Quotient translationOrbitSetoid) :
    translationOrbitQuotientHeight
        (translationOrbitQuotientAction x q) =
      translationOrbitQuotientHeight q := by
  induction q using Quotient.inductionOn with
  | h v =>
      rw [translationOrbitQuotientAction_mk,
        translationOrbitQuotientHeight_mk,
        translationOrbitQuotientHeight_mk]
      exact translationOrbitHeight_translation_invariant x v

theorem translationOrbitQuotientAction_eq_id
    (x : ℝ) (q : Quotient translationOrbitSetoid) :
    translationOrbitQuotientAction x q = q := by
  apply translationOrbitQuotientHeight_injective
  exact translationOrbitQuotientHeight_action_invariant x q

theorem continuous_translationOrbitQuotientAction_joint :
    Continuous (fun p : ℝ × Quotient translationOrbitSetoid =>
      translationOrbitQuotientAction p.1 p.2) := by
  apply continuous_snd.congr
  intro p
  exact (translationOrbitQuotientAction_eq_id p.1 p.2).symm

theorem isOpenMap_translationOrbitHeight :
    IsOpenMap translationOrbitHeight := by
  simpa [translationOrbitHeight] using
    (isOpenMap_snd : IsOpenMap (Prod.snd : Point2 → ℝ))

theorem translationOrbitHeight_isQuotientMap :
    Topology.IsQuotientMap translationOrbitHeight := by
  exact isOpenMap_translationOrbitHeight.isQuotientMap
    continuous_translationOrbitHeight translationOrbitHeight_surjective

theorem translationAffineOrbit_eq_or_disjoint (v w : Point2) :
    translationAffineOrbit v = translationAffineOrbit w ∨
      Disjoint (translationAffineOrbit v) (translationAffineOrbit w) := by
  by_cases hheight : v.2 = w.2
  · exact Or.inl ((translationAffineOrbit_eq_iff_height_eq v w).mpr hheight)
  · right
    rw [Set.disjoint_left]
    intro z hzv hzw
    have hvz : z.2 = v.2 := by
      rw [translationAffineOrbit_eq_horizontalAffineLine] at hzv
      exact hzv
    have hwz : z.2 = w.2 := by
      rw [translationAffineOrbit_eq_horizontalAffineLine] at hzw
      exact hzw
    exact hheight (hvz.symm.trans hwz)

theorem isClosed_horizontalAffineLine (v : Point2) :
    IsClosed (horizontalAffineLine v) := by
  unfold horizontalAffineLine
  exact isClosed_eq (by fun_prop) continuous_const

def horizontalAffineLineHomeomorph (v : Point2) :
    ℝ ≃ₜ HorizontalAffineLineCarrier v where
  toFun := fun x =>
    ⟨(v.1 + x, v.2), by
      change (v.1 + x, v.2).2 = v.2
      rfl⟩
  invFun := fun w => w.1.1 - v.1
  left_inv := by
    intro x
    dsimp
    ring
  right_inv := by
    intro w
    apply Subtype.ext
    change (v.1 + (w.1.1 - v.1), v.2) = w.1
    ext
    · ring
    · have hw : w.1.2 = v.2 := by
        change w.1.2 = v.2
        exact w.property
      exact hw.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    exact (continuous_fst.comp continuous_subtype_val).sub continuous_const

theorem isClosed_translationAffineOrbit (v : Point2) :
    IsClosed (translationAffineOrbit v) := by
  rw [translationAffineOrbit_eq_horizontalAffineLine]
  exact isClosed_horizontalAffineLine v

theorem isClosedEmbedding_translationAffineOrbitCarrier_subtypeVal (v : Point2) :
    Topology.IsClosedEmbedding
      ((↑) : TranslationAffineOrbitCarrier v → Point2) := by
  exact Topology.IsClosedEmbedding.subtypeVal (isClosed_translationAffineOrbit v)

theorem isProperMap_translationAffineOrbitCarrier_subtypeVal (v : Point2) :
    IsProperMap (((↑) : TranslationAffineOrbitCarrier v → Point2)) := by
  exact (isClosedEmbedding_translationAffineOrbitCarrier_subtypeVal v).isProperMap

theorem isClosedMap_translationAffineOrbitCarrier_subtypeVal (v : Point2) :
    IsClosedMap (((↑) : TranslationAffineOrbitCarrier v → Point2)) := by
  exact (isClosedEmbedding_translationAffineOrbitCarrier_subtypeVal v).isClosedMap

theorem isClosed_translationOrbitSetoid_relation :
    IsClosed {p : Point2 × Point2 | translationOrbitSetoid.r p.1 p.2} := by
  change IsClosed {p : Point2 × Point2 | p.1.2 = p.2.2}
  exact isClosed_eq (continuous_snd.comp continuous_fst)
    (continuous_snd.comp continuous_snd)

theorem not_isCompact_translationAffineOrbit (v : Point2) :
    ¬ IsCompact (translationAffineOrbit v) := by
  intro hcompact
  have hbounded := hcompact.isBounded
  rw [isBounded_iff_forall_norm_le] at hbounded
  rcases hbounded with ⟨C, hC⟩
  let x : ℝ := C + |v.1| + |v.2| + 1
  have hxmem : (v.1 + x, v.2) ∈ translationAffineOrbit v := by
    rw [translationAffineOrbit_eq_horizontalAffineLine]
    dsimp [horizontalAffineLine]
  have hv_mem : v ∈ translationAffineOrbit v := by
    refine ⟨0, ?_⟩
    rw [translationAffineOrbitMap_formula]
    ext <;> ring
  have hC_nonneg : 0 ≤ C := by
    have hC0 := hC v hv_mem
    exact le_trans (norm_nonneg _) hC0
  have hnorm := hC (v.1 + x, v.2) hxmem
  rw [Prod.norm_def] at hnorm
  have hfirst : ‖v.1 + x‖ ≤ C := le_trans (le_max_left _ _) hnorm
  rw [Real.norm_eq_abs] at hfirst
  have hnonneg : 0 ≤ v.1 + x := by
    dsimp [x]
    nlinarith [neg_abs_le v.1, abs_nonneg v.2, hC_nonneg]
  rw [abs_of_nonneg hnonneg] at hfirst
  dsimp [x] at hfirst
  nlinarith [abs_nonneg v.1, abs_nonneg v.2, neg_abs_le v.1]

theorem isClosedEmbedding_translationAffineOrbitMap (v : Point2) :
    Topology.IsClosedEmbedding (translationAffineOrbitMap v) := by
  exact ⟨isEmbedding_translationAffineOrbitMap v, by
    simpa [translationAffineOrbit] using isClosed_translationAffineOrbit v⟩

theorem isProperMap_translationAffineOrbitMap (v : Point2) :
    IsProperMap (translationAffineOrbitMap v) := by
  exact (isClosedEmbedding_translationAffineOrbitMap v).isProperMap

end InfoGeometry.Canonical.SE2SouriauCocycle
