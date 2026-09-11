import InfoGeometry.Canonical.SE2SouriauCompactOrbit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SE2SouriauAffineAction

/-!
# Compact rotational affine orbits

The full `SE(2)` carrier is non-compact because of translations.  Its compact
rotation carrier nevertheless acts continuously on `Point2`, and every orbit
of that restricted action is compact.
-/

namespace SE2Souriau.CompactRotation

open SE2Souriau
open InfoGeometry.Canonical.SE2SouriauCocycle

def rotationCarrierInclusion (g : RotationCarrier) : SE2RotationCarrier :=
  ⟨(g.1.1, g.1.2, 0, 0), by
    change g.1.1 ^ 2 + g.1.2 ^ 2 = 1
    exact g.2⟩

theorem rotationCarrierInclusion_one :
    rotationCarrierInclusion (1 : RotationCarrier) =
      (1 : SE2RotationCarrier) := by
  apply Subtype.ext
  change (1, 0, 0, 0) = se2ParameterIdentity
  rfl

theorem rotationCarrierInclusion_mul (g h : RotationCarrier) :
    rotationCarrierInclusion (g * h) =
      rotationCarrierInclusion g * rotationCarrierInclusion h := by
  apply Subtype.ext
  change
    (g.1.1 * h.1.1 - g.1.2 * h.1.2,
      g.1.2 * h.1.1 + g.1.1 * h.1.2, 0, 0) =
      se2ParameterProduct g.1.1 g.1.2 0 0 h.1.1 h.1.2 0 0
  dsimp [se2ParameterProduct]
  ring

def rotationCarrierInclusionHom :
    RotationCarrier →* SE2RotationCarrier where
  toFun := rotationCarrierInclusion
  map_one' := rotationCarrierInclusion_one
  map_mul' := rotationCarrierInclusion_mul

theorem continuous_rotationCarrierInclusion :
    Continuous rotationCarrierInclusion := by
  unfold rotationCarrierInclusion
  apply Continuous.subtype_mk
  fun_prop

def rotationCarrierInclusionContinuousMonoidHom :
    RotationCarrier →ₜ* SE2RotationCarrier where
  toMonoidHom := rotationCarrierInclusionHom
  continuous_toFun := continuous_rotationCarrierInclusion

theorem rotationCarrierInclusion_injective :
    Function.Injective rotationCarrierInclusion := by
  intro g h hEq
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : SE2Parameters => q.1) (congrArg Subtype.val hEq)
  · exact congrArg (fun q : SE2Parameters => q.2.1)
      (congrArg Subtype.val hEq)

def rotationCarrierInclusionLocus : Set SE2RotationCarrier :=
  {g | g.1.2.2.1 = 0 ∧ g.1.2.2.2 = 0}

theorem rotationCarrierInclusion_range_eq_locus :
    Set.range rotationCarrierInclusion = rotationCarrierInclusionLocus := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    simp [rotationCarrierInclusion, rotationCarrierInclusionLocus]
  · intro hg
    let r : RotationCarrier :=
      ⟨(g.1.1, g.1.2.1), by
        change g.1.1 ^ 2 + g.1.2.1 ^ 2 = 1
        exact g.2⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change (r.1.1, r.1.2, 0, 0) = g.1
    ext
    · rfl
    · rfl
    · exact hg.1.symm
    · exact hg.2.symm

def rotationCarrierInclusionReadout
    (g : rotationCarrierInclusionLocus) : RotationCarrier :=
  ⟨(g.1.1.1, g.1.1.2.1), g.1.2⟩

theorem continuous_rotationCarrierInclusionReadout :
    Continuous rotationCarrierInclusionReadout := by
  unfold rotationCarrierInclusionReadout
  apply Continuous.subtype_mk
  fun_prop

def rotationCarrierInclusionLocusHomeomorph :
    RotationCarrier ≃ₜ rotationCarrierInclusionLocus where
  toFun := fun g =>
    ⟨rotationCarrierInclusion g, by
      rw [← rotationCarrierInclusion_range_eq_locus]
      exact ⟨g, rfl⟩⟩
  invFun := rotationCarrierInclusionReadout
  left_inv := by
    intro g
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    change rotationCarrierInclusion
        (rotationCarrierInclusionReadout g) = g.1
    apply Subtype.ext
    change (g.1.1.1, g.1.1.2.1, 0, 0) = g.1.1
    ext
    · rfl
    · rfl
    · exact g.2.1.symm
    · exact g.2.2.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_rotationCarrierInclusion
  continuous_invFun := continuous_rotationCarrierInclusionReadout

theorem isClosed_rotationCarrierInclusion_range :
    IsClosed (Set.range rotationCarrierInclusion) := by
  rw [← Set.image_univ]
  exact (isCompact_univ.image continuous_rotationCarrierInclusion).isClosed

theorem isClosedEmbedding_rotationCarrierInclusion :
    Topology.IsClosedEmbedding rotationCarrierInclusion := by
  refine ⟨?_, isClosed_rotationCarrierInclusion_range⟩
  change Topology.IsEmbedding
    ((fun g : rotationCarrierInclusionLocus => g.1) ∘
      rotationCarrierInclusionLocusHomeomorph)
  exact Topology.IsEmbedding.subtypeVal.comp
    rotationCarrierInclusionLocusHomeomorph.isEmbedding

def rotationAffinePointAction (g : RotationCarrier) (v : Point2) : Point2 :=
  rotationAction g.1.1 g.1.2 v

theorem affinePointAction_rotationCarrierInclusion
    (g : RotationCarrier) (v : Point2) :
    affinePointAction (rotationCarrierInclusion g) v =
      rotationAffinePointAction g v := by
  ext <;> dsimp [affinePointAction, rotationAffinePointAction,
    rotationCarrierInclusion, rotationAction]
  <;> ring

def pointQuadratic (v : Point2) : ℝ := v.1 ^ 2 + v.2 ^ 2

theorem continuous_pointQuadratic : Continuous pointQuadratic := by
  unfold pointQuadratic
  fun_prop

def pointQuadraticLevel (r : ℝ) : Set Point2 :=
  {v | pointQuadratic v = r}

theorem nonempty_pointQuadraticLevel
    (r : ℝ) (hr : 0 ≤ r) :
    (pointQuadraticLevel r).Nonempty := by
  refine ⟨(Real.sqrt r, 0), ?_⟩
  simp [pointQuadraticLevel, pointQuadratic, Real.sq_sqrt hr]

theorem pointQuadraticLevel_eq_empty_of_neg
    (r : ℝ) (hr : r < 0) :
    pointQuadraticLevel r = ∅ := by
  ext v
  constructor
  · intro hv
    change pointQuadratic v = r at hv
    have hnonneg : 0 ≤ pointQuadratic v := by
      dsimp [pointQuadratic]
      positivity
    exfalso
    linarith
  · intro hv
    simp at hv

theorem pointQuadraticLevel_nonempty_iff (r : ℝ) :
    (pointQuadraticLevel r).Nonempty ↔ 0 ≤ r := by
  constructor
  · rintro ⟨v, hv⟩
    change pointQuadratic v = r at hv
    have hnonneg : 0 ≤ pointQuadratic v := by
      dsimp [pointQuadratic]
      positivity
    linarith
  · exact nonempty_pointQuadraticLevel r

theorem isClosed_pointQuadraticLevel (r : ℝ) :
    IsClosed (pointQuadraticLevel r) := by
  unfold pointQuadraticLevel
  exact isClosed_singleton.preimage continuous_pointQuadratic

theorem isBounded_pointQuadraticLevel
    (r : ℝ) (hr : 0 ≤ r) :
    Bornology.IsBounded (pointQuadraticLevel r) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨r + 1, ?_⟩
  intro p hp
  change p.1 ^ 2 + p.2 ^ 2 = r at hp
  rw [Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs, abs_le]
    have hc : p.1 ^ 2 ≤ r := by
      nlinarith [sq_nonneg p.2]
    constructor <;>
      nlinarith [sq_nonneg (p.1 - (r + 1)),
        sq_nonneg (p.1 + (r + 1))]
  · rw [Real.norm_eq_abs, abs_le]
    have hc : p.2 ^ 2 ≤ r := by
      nlinarith [sq_nonneg p.1]
    constructor <;>
      nlinarith [sq_nonneg (p.2 - (r + 1)),
        sq_nonneg (p.2 + (r + 1))]

theorem isCompact_pointQuadraticLevel
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact (pointQuadraticLevel r) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  exact ⟨isClosed_pointQuadraticLevel r,
    isBounded_pointQuadraticLevel r hr⟩

theorem isCompact_pointQuadraticLevel_all (r : ℝ) :
    IsCompact (pointQuadraticLevel r) := by
  by_cases hr : 0 ≤ r
  · exact isCompact_pointQuadraticLevel r hr
  · rw [pointQuadraticLevel_eq_empty_of_neg r (lt_of_not_ge hr)]
    exact isCompact_empty

theorem rotationAffinePointAction_preserves_quadratic
    (g : RotationCarrier) (v : Point2) :
    pointQuadratic (rotationAffinePointAction g v) = pointQuadratic v := by
  have hg : g.1.1 ^ 2 + g.1.2 ^ 2 = 1 := by
    exact g.2
  dsimp [pointQuadratic, rotationAffinePointAction, rotationAction]
  nlinarith [sq_nonneg (g.1.1 * v.1 - g.1.2 * v.2),
    sq_nonneg (g.1.2 * v.1 + g.1.1 * v.2)]

theorem rotationAffinePointAction_one (v : Point2) :
    rotationAffinePointAction (1 : RotationCarrier) v = v := by
  change rotationAffinePointAction rotationIdentity v = v
  ext <;> dsimp [rotationAffinePointAction, rotationIdentity,
    rotationAction] <;> ring

theorem rotationAffinePointAction_mul
    (g h : RotationCarrier) (v : Point2) :
    rotationAffinePointAction (g * h) v =
      rotationAffinePointAction g (rotationAffinePointAction h v) := by
  change rotationAffinePointAction (rotationProduct g h) v =
    rotationAffinePointAction g (rotationAffinePointAction h v)
  ext <;> dsimp [rotationAffinePointAction, rotationProduct,
    rotationAction] <;> ring

instance : MulAction RotationCarrier Point2 where
  smul := rotationAffinePointAction
  one_smul := rotationAffinePointAction_one
  mul_smul := rotationAffinePointAction_mul

theorem continuous_rotationAffinePointAction :
    Continuous (fun p : RotationCarrier × Point2 => p.1 • p.2) := by
  change Continuous (fun p : RotationCarrier × Point2 =>
    rotationAction p.1.1.1 p.1.1.2 p.2)
  unfold rotationAction
  fun_prop

instance : ContinuousSMul RotationCarrier Point2 where
  continuous_smul := continuous_rotationAffinePointAction

def rotationAffineOrbitMap (v : Point2) :
    RotationCarrier → Point2 := fun g => g • v

theorem continuous_rotationAffineOrbitMap (v : Point2) :
    Continuous (rotationAffineOrbitMap v) := by
  unfold rotationAffineOrbitMap
  simpa only [Function.comp_apply] using
    continuous_rotationAffinePointAction.comp
      (continuous_id.prodMk continuous_const)

def rotationAffineOrbit (v : Point2) : Set Point2 :=
  Set.range (rotationAffineOrbitMap v)

theorem rotationAffineOrbit_as_included_affineOrbit (v : Point2) :
    Set.range (fun g : RotationCarrier =>
      affinePointAction (rotationCarrierInclusion g) v) =
      rotationAffineOrbit v := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    change rotationAffinePointAction g v =
      affinePointAction (rotationCarrierInclusion g) v
    exact (affinePointAction_rotationCarrierInclusion g v).symm
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change affinePointAction (rotationCarrierInclusion g) v = x
    rw [affinePointAction_rotationCarrierInclusion]
    exact hg

theorem rotationAffineOrbit_subset_quadratic_level (v : Point2) :
    rotationAffineOrbit v ⊆ {w | pointQuadratic w = pointQuadratic v} := by
  rintro w ⟨g, rfl⟩
  exact rotationAffinePointAction_preserves_quadratic g v

theorem rotationAffineOrbit_subset_pointQuadraticLevel (v : Point2) :
    rotationAffineOrbit v ⊆ pointQuadraticLevel (pointQuadratic v) := by
  exact rotationAffineOrbit_subset_quadratic_level v

theorem rotationAffineOrbit_eq_pointQuadraticLevel_of_pos
    (v : Point2) (hv : 0 < pointQuadratic v) :
    rotationAffineOrbit v = pointQuadraticLevel (pointQuadratic v) := by
  apply Set.Subset.antisymm
  · exact rotationAffineOrbit_subset_pointQuadraticLevel v
  · intro w hw
    let r : ℝ := pointQuadratic v
    let c : ℝ := (v.1 * w.1 + v.2 * w.2) / r
    let s : ℝ := (v.1 * w.2 - v.2 * w.1) / r
    have hr : r ≠ 0 := by
      dsimp [r]
      exact ne_of_gt hv
    have hw' : pointQuadratic w = r := by
      exact hw
    have hdotcross :
        (v.1 * w.1 + v.2 * w.2) ^ 2 +
            (v.1 * w.2 - v.2 * w.1) ^ 2 =
          pointQuadratic v * pointQuadratic w := by
      dsimp [pointQuadratic]
      ring
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp [c, s]
      rw [div_pow, div_pow, ← add_div, hdotcross, hw']
      dsimp [r]
      field_simp
    let g : RotationCarrier :=
      ⟨(c, s), by simpa [rotationCircle] using hcs⟩
    have hfirst : rotationAffinePointAction g v = w := by
      ext <;> dsimp [rotationAffinePointAction, rotationAction, g, c, s, r]
      · field_simp [hr]
        dsimp [pointQuadratic]
        ring
      · field_simp [hr]
        dsimp [pointQuadratic]
        ring
    exact ⟨g, hfirst⟩

theorem rotationAffineOrbit_eq_pointQuadraticLevel (v : Point2) :
    rotationAffineOrbit v = pointQuadraticLevel (pointQuadratic v) := by
  by_cases hv : 0 < pointQuadratic v
  · exact rotationAffineOrbit_eq_pointQuadraticLevel_of_pos v hv
  · have hnonneg : 0 ≤ pointQuadratic v := by
      dsimp [pointQuadratic]
      positivity
    have hzero : pointQuadratic v = 0 := le_antisymm (le_of_not_gt hv) hnonneg
    have hv0 : v = (0, 0) := by
      ext <;> dsimp [pointQuadratic] at hzero ⊢
      · nlinarith [sq_nonneg v.2]
      · nlinarith [sq_nonneg v.1]
    subst v
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      change pointQuadratic (rotationAffinePointAction g (0, 0)) =
        pointQuadratic (0, 0)
      exact rotationAffinePointAction_preserves_quadratic g (0, 0)
    · intro hw
      have hwzero : w = (0, 0) := by
        change pointQuadratic w = pointQuadratic (0, 0) at hw
        dsimp [pointQuadratic] at hw
        ext <;> nlinarith [sq_nonneg w.1, sq_nonneg w.2]
      subst w
      exact ⟨1, rotationAffinePointAction_one (0, 0)⟩

theorem rotationAffineOrbit_eq_iff_pointQuadratic_eq
    (v w : Point2) :
    rotationAffineOrbit v = rotationAffineOrbit w ↔
      pointQuadratic v = pointQuadratic w := by
  constructor
  · intro horbit
    have hv : v ∈ rotationAffineOrbit v := by
      exact ⟨1, rotationAffinePointAction_one v⟩
    have hv' : v ∈ rotationAffineOrbit w := by
      rw [← horbit]
      exact hv
    exact rotationAffineOrbit_subset_pointQuadraticLevel w hv'
  · intro hquad
    rw [rotationAffineOrbit_eq_pointQuadraticLevel,
      rotationAffineOrbit_eq_pointQuadraticLevel, hquad]

def rotationOrbitSetoid : Setoid Point2 where
  r v w := pointQuadratic v = pointQuadratic w
  iseqv := {
    refl := by intro v; rfl
    symm := by intro v w h; exact h.symm
    trans := by intro u v w huv hvw; exact huv.trans hvw }

theorem rotationOrbitSetoid_rel_iff_orbit_eq (v w : Point2) :
    rotationOrbitSetoid.r v w ↔
      rotationAffineOrbit v = rotationAffineOrbit w := by
  simpa [rotationOrbitSetoid] using
    (rotationAffineOrbit_eq_iff_pointQuadratic_eq v w).symm

theorem rotationOrbitSetoid_action_compat
    (g : RotationCarrier) (v w : Point2) :
    rotationOrbitSetoid.r v w →
      rotationOrbitSetoid.r
        (rotationAffinePointAction g v)
        (rotationAffinePointAction g w) := by
  intro h
  change pointQuadratic (rotationAffinePointAction g v) =
    pointQuadratic (rotationAffinePointAction g w)
  rw [rotationAffinePointAction_preserves_quadratic,
    rotationAffinePointAction_preserves_quadratic]
  exact h

def rotationOrbitQuotientAction (g : RotationCarrier) :
    Quotient rotationOrbitSetoid → Quotient rotationOrbitSetoid :=
  Quotient.lift (fun v => Quotient.mk'' (rotationAffinePointAction g v))
    (by
      intro v w h
      apply Quotient.sound
      exact rotationOrbitSetoid_action_compat g v w h)

theorem rotationOrbitQuotientAction_mk (g : RotationCarrier) (v : Point2) :
    rotationOrbitQuotientAction g (Quotient.mk'' v) =
      Quotient.mk'' (rotationAffinePointAction g v) := rfl

theorem rotationOrbitQuotientAction_one (q : Quotient rotationOrbitSetoid) :
    rotationOrbitQuotientAction (1 : RotationCarrier) q = q := by
  induction q using Quotient.inductionOn with
  | h v =>
      rw [rotationOrbitQuotientAction_mk, rotationAffinePointAction_one]

theorem rotationOrbitQuotientAction_mul
    (g h : RotationCarrier) (q : Quotient rotationOrbitSetoid) :
    rotationOrbitQuotientAction (g * h) q =
      rotationOrbitQuotientAction g (rotationOrbitQuotientAction h q) := by
  induction q using Quotient.inductionOn with
  | h v =>
      rw [rotationOrbitQuotientAction_mk, rotationOrbitQuotientAction_mk,
        rotationOrbitQuotientAction_mk, rotationAffinePointAction_mul]

instance : MulAction RotationCarrier (Quotient rotationOrbitSetoid) where
  smul := rotationOrbitQuotientAction
  one_smul := rotationOrbitQuotientAction_one
  mul_smul := rotationOrbitQuotientAction_mul

theorem continuous_rotationOrbitQuotientAction_fixed
    (g : RotationCarrier) :
    Continuous (rotationOrbitQuotientAction g) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_rotationAffinePointAction.comp
      (continuous_const.prodMk continuous_id))

def rotationOrbitQuotientRadius :
    Quotient rotationOrbitSetoid → Set.Ici (0 : ℝ) :=
  Quotient.lift (fun v => ⟨pointQuadratic v, by
    dsimp [pointQuadratic]
    exact add_nonneg (sq_nonneg v.1) (sq_nonneg v.2)⟩) (by
      intro v w h
      apply Subtype.ext
      exact h)

theorem rotationOrbitQuotientRadius_mk (v : Point2) :
    rotationOrbitQuotientRadius (Quotient.mk'' v) =
      ⟨pointQuadratic v, by
        dsimp [pointQuadratic]
        exact add_nonneg (sq_nonneg v.1) (sq_nonneg v.2)⟩ := rfl

theorem rotationOrbitQuotientRadius_comp_mk :
    rotationOrbitQuotientRadius ∘ Quotient.mk'' =
      fun v => ⟨pointQuadratic v, by
        dsimp [pointQuadratic]
        exact add_nonneg (sq_nonneg v.1) (sq_nonneg v.2)⟩ := by
  rfl

theorem rotationOrbitQuotientRadius_injective :
    Function.Injective rotationOrbitQuotientRadius := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h v =>
    induction q₂ using Quotient.inductionOn with
    | h w =>
      apply Quotient.sound
      exact congrArg Subtype.val h

theorem rotationOrbitQuotientRadius_surjective :
    Function.Surjective rotationOrbitQuotientRadius := by
  intro r
  refine ⟨Quotient.mk'' (Real.sqrt r, 0), ?_⟩
  apply Subtype.ext
  dsimp [rotationOrbitQuotientRadius, pointQuadratic]
  simpa [pointQuadratic] using Real.sq_sqrt r.2

noncomputable def rotationOrbitQuotientRadiusEquiv :
    Quotient rotationOrbitSetoid ≃ Set.Ici (0 : ℝ) where
  toFun := rotationOrbitQuotientRadius
  invFun := fun r => Quotient.mk'' (Real.sqrt r, 0)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      dsimp [rotationOrbitQuotientRadius, pointQuadratic]
      change (Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) ^ 2 + 0 ^ 2 =
        v.1 ^ 2 + v.2 ^ 2
      simpa using Real.sq_sqrt (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2))
  right_inv := by
    intro r
    apply Subtype.ext
    dsimp [rotationOrbitQuotientRadius, pointQuadratic]
    simpa [pointQuadratic] using Real.sq_sqrt r.2

theorem continuous_rotationOrbitQuotientRadius :
    Continuous rotationOrbitQuotientRadius := by
  apply Continuous.quotient_lift
  apply Continuous.subtype_mk
  exact continuous_pointQuadratic

noncomputable def rotationOrbitQuotientRadiusHomeomorph :
    Quotient rotationOrbitSetoid ≃ₜ Set.Ici (0 : ℝ) where
  toFun := rotationOrbitQuotientRadius
  invFun := fun r => Quotient.mk'' (Real.sqrt r, 0)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      dsimp [rotationOrbitQuotientRadius, pointQuadratic]
      change (Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) ^ 2 + 0 ^ 2 =
        v.1 ^ 2 + v.2 ^ 2
      simpa using Real.sq_sqrt (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2))
  right_inv := by
    intro r
    apply Subtype.ext
    dsimp [rotationOrbitQuotientRadius, pointQuadratic]
    simpa [pointQuadratic] using Real.sq_sqrt r.2
  continuous_toFun := continuous_rotationOrbitQuotientRadius
  continuous_invFun := by
    apply continuous_quotient_mk'.comp
    apply Continuous.prodMk
    · exact Real.continuous_sqrt.comp continuous_subtype_val
    · exact continuous_const

theorem isCompact_rotationAffineOrbit (v : Point2) :
    IsCompact (rotationAffineOrbit v) := by
  unfold rotationAffineOrbit
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_rotationAffineOrbitMap v)

theorem nonempty_rotationAffineOrbit (v : Point2) :
    (rotationAffineOrbit v).Nonempty := by
  exact ⟨v, ⟨1, one_smul RotationCarrier v⟩⟩

abbrev QuadraticLevelCarrier (r : ℝ) :=
  {v : Point2 // v ∈ pointQuadraticLevel r}

theorem nonempty_quadraticLevelCarrier
    (r : ℝ) (hr : 0 ≤ r) : Nonempty (QuadraticLevelCarrier r) := by
  rcases nonempty_pointQuadraticLevel r hr with ⟨v, hv⟩
  exact ⟨⟨v, hv⟩⟩

def rotationQuadraticAction
    {r : ℝ} (g : RotationCarrier) (v : QuadraticLevelCarrier r) :
    QuadraticLevelCarrier r :=
  ⟨rotationAffinePointAction g v.1, by
    change pointQuadratic (rotationAffinePointAction g v.1) = r
    rw [rotationAffinePointAction_preserves_quadratic]
    exact v.2⟩

theorem rotationQuadraticAction_one
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    rotationQuadraticAction (1 : RotationCarrier) v = v := by
  apply Subtype.ext
  exact rotationAffinePointAction_one v.1

theorem rotationQuadraticAction_mul
    {r : ℝ} (g h : RotationCarrier) (v : QuadraticLevelCarrier r) :
    rotationQuadraticAction (g * h) v =
      rotationQuadraticAction g (rotationQuadraticAction h v) := by
  apply Subtype.ext
  exact rotationAffinePointAction_mul g h v.1

instance {r : ℝ} : MulAction RotationCarrier (QuadraticLevelCarrier r) where
  smul := rotationQuadraticAction
  one_smul := rotationQuadraticAction_one
  mul_smul := rotationQuadraticAction_mul

theorem continuous_rotationQuadraticAction
    {r : ℝ} :
    Continuous (fun p : RotationCarrier × QuadraticLevelCarrier r =>
      p.1 • p.2) := by
  apply Continuous.subtype_mk
  exact continuous_rotationAffinePointAction.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

instance {r : ℝ} : ContinuousSMul RotationCarrier (QuadraticLevelCarrier r) where
  continuous_smul := continuous_rotationQuadraticAction

theorem continuous_rotationQuadraticAction_fixed
    {r : ℝ} (g : RotationCarrier) :
    Continuous (rotationQuadraticAction (r := r) g) := by
  simpa only [Function.comp_apply] using
    continuous_rotationQuadraticAction.comp (continuous_const.prodMk continuous_id)

def rotationQuadraticActionHomeomorph
  {r : ℝ} (g : RotationCarrier) :
    QuadraticLevelCarrier r ≃ₜ QuadraticLevelCarrier r where
  toFun := rotationQuadraticAction (r := r) g
  invFun := rotationQuadraticAction (r := r) g⁻¹
  left_inv := by
    intro v
    apply Subtype.ext
    rw [← rotationQuadraticAction_mul, inv_mul_cancel, rotationQuadraticAction_one]
  right_inv := by
    intro v
    apply Subtype.ext
    rw [← rotationQuadraticAction_mul, mul_inv_cancel, rotationQuadraticAction_one]
  continuous_toFun := continuous_rotationQuadraticAction_fixed g
  continuous_invFun := continuous_rotationQuadraticAction_fixed g⁻¹

theorem isCompact_quadraticLevelCarrier
    (r : ℝ) (hr : 0 ≤ r) : IsCompact (Set.univ : Set (QuadraticLevelCarrier r)) := by
  rw [Subtype.isCompact_iff]
  simpa using isCompact_pointQuadraticLevel r hr

theorem isCompact_quadraticLevelCarrier_all (r : ℝ) :
    IsCompact (Set.univ : Set (QuadraticLevelCarrier r)) := by
  rw [Subtype.isCompact_iff]
  simpa using isCompact_pointQuadraticLevel_all r

def rotationQuadraticOrbitMap
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    RotationCarrier → QuadraticLevelCarrier r := fun g => g • v

theorem rotationQuadraticOrbitMap_injective_of_pos
    {r : ℝ} (hr : 0 < r) (v : QuadraticLevelCarrier r) :
    Function.Injective (rotationQuadraticOrbitMap v) := by
  intro g h gh
  have hval := congrArg Subtype.val gh
  change rotationAffinePointAction g v.1 =
      rotationAffinePointAction h v.1 at hval
  have hx := congrArg Prod.fst hval
  have hy := congrArg Prod.snd hval
  dsimp [rotationAffinePointAction,
    InfoGeometry.Canonical.SE2SouriauCocycle.rotationAction] at hx hy
  have hv : 0 < v.1.1 ^ 2 + v.1.2 ^ 2 := by
    have hv' : v.1.1 ^ 2 + v.1.2 ^ 2 = r := v.2
    linarith
  let A : ℝ := g.1.1 - h.1.1
  let B : ℝ := g.1.2 - h.1.2
  have hx0 : A * v.1.1 - B * v.1.2 = 0 := by
    dsimp [A, B]
    linarith [hx]
  have hy0 : B * v.1.1 + A * v.1.2 = 0 := by
    dsimp [A, B]
    linarith [hy]
  have hAprod : A ^ 2 * (v.1.1 ^ 2 + v.1.2 ^ 2) = 0 := by
    calc
      A ^ 2 * (v.1.1 ^ 2 + v.1.2 ^ 2) =
          A * v.1.1 * (A * v.1.1 - B * v.1.2) +
            A * v.1.2 * (B * v.1.1 + A * v.1.2) := by ring
      _ = 0 := by rw [hx0, hy0]; ring
  have hBprod : B ^ 2 * (v.1.1 ^ 2 + v.1.2 ^ 2) = 0 := by
    calc
      B ^ 2 * (v.1.1 ^ 2 + v.1.2 ^ 2) =
          (-B * v.1.2) * (A * v.1.1 - B * v.1.2) +
            B * v.1.1 * (B * v.1.1 + A * v.1.2) := by ring
      _ = 0 := by rw [hx0, hy0]; ring
  have hA_sq : A ^ 2 = 0 := by
    rcases mul_eq_zero.mp hAprod with hzero | hzero
    · exact hzero
    · exfalso
      nlinarith
  have hB_sq : B ^ 2 = 0 := by
    rcases mul_eq_zero.mp hBprod with hzero | hzero
    · exact hzero
    · exfalso
      nlinarith
  have hA : A = 0 := by nlinarith [hA_sq]
  have hB : B = 0 := by nlinarith [hB_sq]
  apply Subtype.ext
  apply Prod.ext
  · dsimp [A] at hA
    linarith
  · dsimp [B] at hB
    linarith

theorem rotationQuadraticOrbit_stabilizer_eq_bot_of_pos
    {r : ℝ} (hr : 0 < r) (v : QuadraticLevelCarrier r) :
    MulAction.stabilizer RotationCarrier v = ⊥ := by
  ext g
  constructor
  · intro hg
    have hfix : g • v = v := MulAction.mem_stabilizer_iff.mp hg
    have hmap : rotationQuadraticOrbitMap v g =
        rotationQuadraticOrbitMap v 1 := by
      simpa [rotationQuadraticOrbitMap] using hfix
    have hge : g = (1 : RotationCarrier) :=
      rotationQuadraticOrbitMap_injective_of_pos hr v hmap
    simpa [hge]
  · intro hg
    have hge : g = (1 : RotationCarrier) := by simpa using hg
    subst g
    exact MulAction.mem_stabilizer_iff.mpr (one_smul RotationCarrier v)

theorem continuous_rotationQuadraticOrbitMap
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    Continuous (rotationQuadraticOrbitMap v) := by
  unfold rotationQuadraticOrbitMap
  simpa only [Function.comp_apply] using
      continuous_rotationQuadraticAction.comp
      (continuous_id.prodMk continuous_const)

theorem isClosedEmbedding_rotationQuadraticOrbitMap_of_pos
    {r : ℝ} (hr : 0 < r) (v : QuadraticLevelCarrier r) :
    Topology.IsClosedEmbedding (rotationQuadraticOrbitMap v) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_rotationQuadraticOrbitMap v)
    (rotationQuadraticOrbitMap_injective_of_pos hr v)
    (Continuous.isClosedMap (continuous_rotationQuadraticOrbitMap v))

def rotationQuadraticOrbitContinuousMap
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    C(RotationCarrier, QuadraticLevelCarrier r) :=
  { toFun := rotationQuadraticOrbitMap v
    continuous_toFun := continuous_rotationQuadraticOrbitMap v }

theorem rotationQuadraticOrbitContinuousMap_apply
    {r : ℝ} (v : QuadraticLevelCarrier r) (g : RotationCarrier) :
    rotationQuadraticOrbitContinuousMap v g = rotationQuadraticOrbitMap v g := rfl

theorem rotationQuadraticOrbitMap_mul
    {r : ℝ} (v : QuadraticLevelCarrier r)
    (g h : RotationCarrier) :
    rotationQuadraticOrbitMap v (g * h) =
      rotationQuadraticOrbitMap (rotationQuadraticOrbitMap v h) g := by
  simp [rotationQuadraticOrbitMap, mul_smul]

def rotationQuadraticOrbit
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    Set (QuadraticLevelCarrier r) :=
  Set.range (rotationQuadraticOrbitMap v)

theorem rotationQuadraticOrbitMap_eq_self_of_zero
    {r : ℝ} (hr : r = 0) (v : QuadraticLevelCarrier r)
    (g : RotationCarrier) :
    rotationQuadraticOrbitMap v g = v := by
  have hv : pointQuadratic v.1 = 0 := by simpa [hr] using v.2
  have hv0 : v.1 = (0, 0) := by
    ext <;> dsimp [pointQuadratic] at hv ⊢
    · nlinarith [sq_nonneg v.1.2]
    · nlinarith [sq_nonneg v.1.1]
  apply Subtype.ext
  change rotationAffinePointAction g v.1 = v.1
  rw [hv0]
  ext <;>
    dsimp [rotationAffinePointAction,
      InfoGeometry.Canonical.SE2SouriauCocycle.rotationAction] <;>
    ring

theorem rotationQuadraticOrbit_eq_singleton_of_zero
    {r : ℝ} (hr : r = 0) (v : QuadraticLevelCarrier r) :
    rotationQuadraticOrbit v = {v} := by
  apply Set.Subset.antisymm
  · rintro w ⟨g, rfl⟩
    apply Set.mem_singleton_iff.mpr
    exact rotationQuadraticOrbitMap_eq_self_of_zero hr v g
  · intro w hw
    have hweq : w = v := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨1, by simp [rotationQuadraticOrbitMap]⟩

theorem rotationQuadraticOrbit_stabilizer_eq_top_of_zero
    {r : ℝ} (hr : r = 0) (v : QuadraticLevelCarrier r) :
    MulAction.stabilizer RotationCarrier v = ⊤ := by
  ext g
  constructor
  · intro _
    simp
  · intro _
    exact MulAction.mem_stabilizer_iff.mpr
      (rotationQuadraticOrbitMap_eq_self_of_zero hr v g)

theorem rotationQuadraticOrbit_coe_image
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    Set.image (fun x : QuadraticLevelCarrier r => x.1)
        (rotationQuadraticOrbit v) =
      rotationAffineOrbit v.1 := by
  ext x
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨rotationQuadraticAction g v, ⟨g, rfl⟩, ?_⟩
    rfl

theorem rotationQuadraticOrbit_eq_univ_of_pos
    {r : ℝ} (hr : 0 < r) (v : QuadraticLevelCarrier r) :
    rotationQuadraticOrbit v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  have hvlevel : pointQuadratic v.1 = r := v.2
  have hvpos : 0 < pointQuadratic v.1 := by
    rw [hvlevel]
    exact hr
  have horbit : rotationAffineOrbit v.1 = pointQuadraticLevel r := by
    calc
      rotationAffineOrbit v.1 = pointQuadraticLevel (pointQuadratic v.1) :=
        rotationAffineOrbit_eq_pointQuadraticLevel_of_pos v.1 hvpos
      _ = pointQuadraticLevel r := by rw [hvlevel]
  have hw_aff : w.1 ∈ rotationAffineOrbit v.1 := by
    rw [horbit]
    exact w.2
  rcases hw_aff with ⟨g, hg⟩
  have htyped : rotationQuadraticAction g v = w := by
    apply Subtype.ext
    exact hg
  exact ⟨g, htyped⟩

noncomputable def rotationQuadraticOrbitHomeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (v : QuadraticLevelCarrier r) :
    RotationCarrier ≃ₜ QuadraticLevelCarrier r := by
  have himage : (rotationQuadraticOrbitMap v) '' (Set.univ : Set RotationCarrier) =
      (Set.univ : Set (QuadraticLevelCarrier r)) := by
    rw [Set.image_univ, Set.range_eq_univ]
    exact Set.range_eq_univ.mp (rotationQuadraticOrbit_eq_univ_of_pos hr v)
  exact (Homeomorph.Set.univ RotationCarrier).symm.trans
    ((isClosedEmbedding_rotationQuadraticOrbitMap_of_pos hr v).homeomorphImage Set.univ)
    |>.trans (Homeomorph.setCongr himage)
    |>.trans (Homeomorph.Set.univ (QuadraticLevelCarrier r))

theorem rotationQuadraticOrbitHomeomorph_of_pos_apply
    {r : ℝ} (hr : 0 < r) (v : QuadraticLevelCarrier r) (g : RotationCarrier) :
    rotationQuadraticOrbitHomeomorph_of_pos hr v g = rotationQuadraticOrbitMap v g := by
  rfl

theorem isCompact_rotationQuadraticOrbit
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    IsCompact (rotationQuadraticOrbit v) := by
  unfold rotationQuadraticOrbit
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_rotationQuadraticOrbitMap v)

theorem isClosed_rotationQuadraticOrbit
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    IsClosed (rotationQuadraticOrbit v) := by
  exact (isCompact_rotationQuadraticOrbit v).isClosed

theorem nonempty_rotationQuadraticOrbit
    {r : ℝ} (v : QuadraticLevelCarrier r) :
    (rotationQuadraticOrbit v).Nonempty := by
  exact ⟨v, ⟨1, one_smul RotationCarrier v⟩⟩

end SE2Souriau.CompactRotation
