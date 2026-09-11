import InfoGeometry.Canonical.SE2SouriauCoadjointOrbit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Group.Basic

namespace SE2Souriau.CompactRotation

open SE2Souriau SE2Souriau.SE2Vector

theorem isClosedEmbedding_casimirFiber_subtypeVal
    {r : ℝ} :
    Topology.IsClosedEmbedding
      ((↑) : CasimirFiberCarrier r → (ℝ × ℝ × ℝ)) := by
  exact Topology.IsClosedEmbedding.subtypeVal (isClosed_casimirFiber r)

theorem isClosedMap_casimirFiber_subtypeVal
    {r : ℝ} :
    IsClosedMap (((↑) : CasimirFiberCarrier r → (ℝ × ℝ × ℝ))) := by
  exact (isClosedEmbedding_casimirFiber_subtypeVal (r := r)).isClosedMap

theorem locallyCompactSpace_casimirFiber
    {r : ℝ} : LocallyCompactSpace (CasimirFiberCarrier r) := by
  exact (isClosedEmbedding_casimirFiber_subtypeVal (r := r)).locallyCompactSpace

def rotationCircle : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 = 1}

theorem isClosed_rotationCircle : IsClosed rotationCircle := by
  unfold rotationCircle
  exact isClosed_singleton.preimage (by fun_prop)

theorem isBounded_rotationCircle : Bornology.IsBounded rotationCircle := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro p hp
  change p.1 ^ 2 + p.2 ^ 2 = 1 at hp
  rw [Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs, abs_le]
    have hc : p.1 ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg p.2]
    constructor <;>
      nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
  · rw [Real.norm_eq_abs, abs_le]
    have hc : p.2 ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg p.1]
    constructor <;>
      nlinarith [sq_nonneg (p.2 - 1), sq_nonneg (p.2 + 1)]

theorem isCompact_rotationCircle : IsCompact rotationCircle := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  exact ⟨isClosed_rotationCircle, isBounded_rotationCircle⟩

abbrev RotationCarrier := {p : ℝ × ℝ // p ∈ rotationCircle}

def rotationProduct (g h : RotationCarrier) : RotationCarrier :=
  ⟨(g.1.1 * h.1.1 - g.1.2 * h.1.2,
      g.1.2 * h.1.1 + g.1.1 * h.1.2), by
    change (g.1.1 * h.1.1 - g.1.2 * h.1.2) ^ 2 +
      (g.1.2 * h.1.1 + g.1.1 * h.1.2) ^ 2 = 1
    calc
      _ = (g.1.1 ^ 2 + g.1.2 ^ 2) * (h.1.1 ^ 2 + h.1.2 ^ 2) := by ring
      _ = 1 := by
        rw [g.2, h.2]
        norm_num⟩

def rotationIdentity : RotationCarrier :=
  ⟨(1, 0), by norm_num [rotationCircle]⟩

def rotationInverse (g : RotationCarrier) : RotationCarrier :=
  ⟨(g.1.1, -g.1.2), by
    change g.1.1 ^ 2 + (-g.1.2) ^ 2 = 1
    have hg : g.1.1 ^ 2 + g.1.2 ^ 2 = 1 := by
      exact g.2
    simpa using hg⟩

theorem rotationProduct_assoc (g h k : RotationCarrier) :
    rotationProduct (rotationProduct g h) k =
      rotationProduct g (rotationProduct h k) := by
  apply Subtype.ext
  ext <;> dsimp [rotationProduct] <;> ring

theorem rotationProduct_identity_left (g : RotationCarrier) :
    rotationProduct rotationIdentity g = g := by
  apply Subtype.ext
  ext <;> dsimp [rotationProduct, rotationIdentity] <;> ring

theorem rotationProduct_identity_right (g : RotationCarrier) :
    rotationProduct g rotationIdentity = g := by
  apply Subtype.ext
  ext <;> dsimp [rotationProduct, rotationIdentity] <;> ring

theorem rotationProduct_inverse_left (g : RotationCarrier) :
    rotationProduct (rotationInverse g) g = rotationIdentity := by
  have hg : g.1.1 ^ 2 + g.1.2 ^ 2 = 1 := by
    exact g.2
  apply Subtype.ext
  ext <;> dsimp [rotationProduct, rotationInverse, rotationIdentity]
  · nlinarith [hg]
  · ring

instance : Group RotationCarrier where
  mul := rotationProduct
  one := rotationIdentity
  inv := rotationInverse
  mul_assoc := rotationProduct_assoc
  one_mul := rotationProduct_identity_left
  mul_one := rotationProduct_identity_right
  inv_mul_cancel := rotationProduct_inverse_left

theorem continuous_rotationProduct :
    Continuous (fun p : RotationCarrier × RotationCarrier =>
      rotationProduct p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : RotationCarrier × RotationCarrier =>
    (p.1.1.1 * p.2.1.1 - p.1.1.2 * p.2.1.2,
      p.1.1.2 * p.2.1.1 + p.1.1.1 * p.2.1.2))
  fun_prop

theorem continuous_rotationInverse :
    Continuous rotationInverse := by
  apply Continuous.subtype_mk
  change Continuous (fun g : RotationCarrier => (g.1.1, -g.1.2))
  fun_prop

instance : ContinuousMul RotationCarrier where
  continuous_mul := continuous_rotationProduct

instance : ContinuousInv RotationCarrier where
  continuous_inv := continuous_rotationInverse

instance : IsTopologicalGroup RotationCarrier := IsTopologicalGroup.mk

instance : CompactSpace RotationCarrier where
  isCompact_univ := by
    rw [Subtype.isCompact_iff]
    simpa [rotationCircle] using isCompact_rotationCircle

def circleToRotationCarrier (z : Circle) : RotationCarrier :=
  ⟨(z.1.re, z.1.im), by
    have hz := z.2
    change (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1 at hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Complex.norm_def] at hz
    have hnorm : Complex.normSq ((z : ℂ)) = 1 := by
      nlinarith [Real.sq_sqrt (Complex.normSq_nonneg (z : ℂ))]
    change (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1
    simpa [pow_two, Complex.normSq_apply] using hnorm⟩

theorem continuous_circleToRotationCarrier :
    Continuous circleToRotationCarrier := by
  apply Continuous.subtype_mk
  change Continuous (fun z : Circle => ((z : ℂ).re, (z : ℂ).im))
  fun_prop

theorem angle_coe_surjective : Function.Surjective ((↑) : ℝ → Real.Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on with
  | h x => exact ⟨x, rfl⟩

instance : PathConnectedSpace Real.Angle :=
  angle_coe_surjective.pathConnectedSpace Real.Angle.continuous_coe

instance : PathConnectedSpace Circle := by
  exact ((AddCircle.homeomorphCircle (T := 2 * Real.pi) (by positivity)).surjective).pathConnectedSpace
    (AddCircle.homeomorphCircle (T := 2 * Real.pi) (by positivity)).continuous_toFun

theorem circleToRotationCarrier_surjective :
    Function.Surjective circleToRotationCarrier := by
  intro g
  let z : Circle :=
    ⟨(g.1.1 : ℂ) + g.1.2 * Complex.I, by
      change (g.1.1 : ℂ) + g.1.2 * Complex.I ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right]
      rw [Complex.norm_def]
      have hnorm :
          Complex.normSq ((g.1.1 : ℂ) + g.1.2 * Complex.I) = 1 := by
        have hg : g.1.1 ^ 2 + g.1.2 ^ 2 = 1 := g.2
        simp [Complex.normSq_apply]
        nlinarith [hg]
      rw [hnorm]
      norm_num⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change ((z : ℂ).re, (z : ℂ).im) = (g.1.1, g.1.2)
  dsimp [z]
  ext <;> simp

theorem pathConnectedSpace_rotationCarrier : PathConnectedSpace RotationCarrier := by
  exact circleToRotationCarrier_surjective.pathConnectedSpace
    continuous_circleToRotationCarrier

instance : PathConnectedSpace RotationCarrier := pathConnectedSpace_rotationCarrier

def rotationMomentumAction
    {r : ℝ} (g : RotationCarrier) (q : CasimirFiberCarrier r) :
    CasimirFiberCarrier r :=
  momentumRotationFiber g.1.1 g.1.2 r g.2 q

theorem rotationMomentumAction_one
    {r : ℝ} (q : CasimirFiberCarrier r) :
    rotationMomentumAction (1 : RotationCarrier) q = q := by
  exact se2CarrierMomentumAction_one q

theorem rotationMomentumAction_mul
    {r : ℝ} (g h : RotationCarrier) (q : CasimirFiberCarrier r) :
    rotationMomentumAction (g * h) q =
      rotationMomentumAction g (rotationMomentumAction h q) := by
  apply Subtype.ext
  change momentumRotationCoordinates
      (g.1.1 * h.1.1 - g.1.2 * h.1.2)
      (g.1.2 * h.1.1 + g.1.1 * h.1.2) q.1 =
    momentumRotationCoordinates g.1.1 g.1.2
      (momentumRotationCoordinates h.1.1 h.1.2 q.1)
  rw [momentumRotationCoordinates_comp]

instance {r : ℝ} : MulAction RotationCarrier (CasimirFiberCarrier r) where
  smul := rotationMomentumAction
  one_smul := rotationMomentumAction_one
  mul_smul := rotationMomentumAction_mul

theorem continuous_rotationMomentumAction
    {r : ℝ} :
    Continuous (fun p : RotationCarrier × CasimirFiberCarrier r =>
      p.1 • p.2) := by
  apply Continuous.subtype_mk
  have hmap : Continuous (fun x : RotationCarrier × CasimirFiberCarrier r =>
      (x.1.1.1, x.1.1.2, x.2.1)) := by
    fun_prop
  simpa only [Function.comp_apply] using
    continuous_momentumRotationCoordinates.comp hmap

def rotationOrbitMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    RotationCarrier → CasimirFiberCarrier r := fun g => g • q

theorem continuous_rotationOrbitMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (rotationOrbitMap q) := by
  unfold rotationOrbitMap
  simpa only [Function.comp_apply] using
    continuous_rotationMomentumAction.comp (continuous_id.prodMk continuous_const)

theorem rotationOrbitMap_injective_of_pos
  {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Function.Injective (rotationOrbitMap q) := by
  intro g h hgh
  have hgh' := hgh
  change g • q = h • q at hgh'
  change rotationMomentumAction g q = rotationMomentumAction h q at hgh'
  dsimp [rotationMomentumAction, momentumRotationFiber] at hgh'
  have hcoords := congrArg
      (fun u : CasimirFiberCarrier r => u.1) hgh'
  have hp1 := congrArg (fun u : ℝ × ℝ × ℝ => u.2.1) hcoords
  have hp2 := congrArg (fun u : ℝ × ℝ × ℝ => u.2.2) hcoords
  dsimp [momentumRotationCoordinates] at hp1 hp2
  have hq : q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = r := by
    exact q.2
  have hdc : (g.1.1 - h.1.1) * r = 0 := by
    linear_combination
      q.1.2.1 * hp1 + q.1.2.2 * hp2 -
        (g.1.1 - h.1.1) * hq
  have hds : (g.1.2 - h.1.2) * r = 0 := by
    linear_combination
      -q.1.2.2 * hp1 + q.1.2.1 * hp2 -
        (g.1.2 - h.1.2) * hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hgc : g.1.1 = h.1.1 := by
    rcases mul_eq_zero.mp hdc with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hr0 hzero)
  have hgs : g.1.2 = h.1.2 := by
    rcases mul_eq_zero.mp hds with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hr0 hzero)
  apply Subtype.ext
  exact Prod.ext hgc hgs

def rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Set (CasimirFiberCarrier r) := Set.range (rotationOrbitMap q)

theorem isClosedEmbedding_rotationOrbitMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsClosedEmbedding (rotationOrbitMap q) := by
  exact (continuous_rotationOrbitMap q).isClosedEmbedding
    (rotationOrbitMap_injective_of_pos hr q)

theorem isClosedMap_rotationOrbitMap_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsClosedMap (rotationOrbitMap q) := by
  exact (isClosedEmbedding_rotationOrbitMap_of_pos hr q).isClosedMap

theorem isProperMap_rotationOrbitMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsProperMap (rotationOrbitMap q) := by
  exact (continuous_rotationOrbitMap q).isProperMap

abbrev RotationOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :=
  {w : CasimirFiberCarrier r // w ∈ rotationOrbit q}

def rotationOrbitMapCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    RotationCarrier → RotationOrbitCarrier q := fun g =>
      ⟨rotationOrbitMap q g, ⟨g, rfl⟩⟩

theorem rotationOrbitMapCarrier_surjective
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Function.Surjective (rotationOrbitMapCarrier q) := by
  intro w
  rcases w.2 with ⟨g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem continuous_rotationOrbitMapCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (rotationOrbitMapCarrier q) := by
  apply Continuous.subtype_mk
  exact continuous_rotationOrbitMap q

theorem pathConnectedSpace_rotationOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    PathConnectedSpace (RotationOrbitCarrier q) := by
  exact (rotationOrbitMapCarrier_surjective q).pathConnectedSpace
    (continuous_rotationOrbitMapCarrier q)

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    PathConnectedSpace (RotationOrbitCarrier q) :=
  pathConnectedSpace_rotationOrbitCarrier q

theorem rotationOrbitMapCarrier_injective_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Function.Injective (rotationOrbitMapCarrier q) := by
  intro g h hgh
  apply rotationOrbitMap_injective_of_pos hr q
  exact congrArg Subtype.val hgh

def rotationOrbitCarrierAction
    {r : ℝ} (q : CasimirFiberCarrier r) (g : RotationCarrier)
    (w : RotationOrbitCarrier q) : RotationOrbitCarrier q :=
  ⟨g • w.1, by
    rcases w.2 with ⟨h, hh⟩
    refine ⟨g * h, ?_⟩
    dsimp [rotationOrbitMap]
    rw [mul_smul]
    change h • q = w.1 at hh
    rw [hh]⟩

theorem rotationOrbitCarrierAction_one
    {r : ℝ} (q : CasimirFiberCarrier r)
    (w : RotationOrbitCarrier q) :
    rotationOrbitCarrierAction q (1 : RotationCarrier) w = w := by
  apply Subtype.ext
  simp [rotationOrbitCarrierAction]

theorem rotationOrbitCarrierAction_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : RotationCarrier) (w : RotationOrbitCarrier q) :
    rotationOrbitCarrierAction q (g * h) w =
    rotationOrbitCarrierAction q g
        (rotationOrbitCarrierAction q h w) := by
  apply Subtype.ext
  change (g * h) • w.1 = g • (h • w.1)
  rw [mul_smul]

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    MulAction RotationCarrier (RotationOrbitCarrier q) where
  smul := rotationOrbitCarrierAction q
  one_smul := rotationOrbitCarrierAction_one q
  mul_smul := rotationOrbitCarrierAction_mul q

theorem continuous_rotationOrbitCarrierAction
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (fun p : RotationCarrier × RotationOrbitCarrier q =>
      p.1 • p.2) := by
  apply Continuous.subtype_mk
  exact continuous_rotationMomentumAction.comp
    (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    ContinuousSMul RotationCarrier (RotationOrbitCarrier q) where
  continuous_smul := continuous_rotationOrbitCarrierAction q

theorem continuous_rotationOrbitCarrierAction_fixed
    {r : ℝ} (q : CasimirFiberCarrier r) (g : RotationCarrier) :
    Continuous (rotationOrbitCarrierAction q g) := by
  simpa only [Function.comp_apply] using
    (continuous_rotationOrbitCarrierAction q).comp
      (continuous_const.prodMk continuous_id)

def rotationOrbitCarrierActionHomeomorph
    {r : ℝ} (q : CasimirFiberCarrier r) (g : RotationCarrier) :
    RotationOrbitCarrier q ≃ₜ RotationOrbitCarrier q where
  toFun := rotationOrbitCarrierAction q g
  invFun := rotationOrbitCarrierAction q g⁻¹
  left_inv := by
    intro w
    apply Subtype.ext
    change g⁻¹ • (g • w.1) = w.1
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv := by
    intro w
    apply Subtype.ext
    change g • (g⁻¹ • w.1) = w.1
    rw [← mul_smul, mul_inv_cancel, one_smul]
  continuous_toFun := continuous_rotationOrbitCarrierAction_fixed q g
  continuous_invFun := continuous_rotationOrbitCarrierAction_fixed q g⁻¹

theorem rotationOrbitMapCarrier_mul
    {r : ℝ} (q : CasimirFiberCarrier r)
    (g h : RotationCarrier) :
    rotationOrbitMapCarrier q (g * h) =
      g • rotationOrbitMapCarrier q h := by
  apply Subtype.ext
  change (g * h) • q = g • (h • q)
  rw [mul_smul]

noncomputable def rotationOrbitHomeomorph_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    RotationCarrier ≃ₜ RotationOrbitCarrier q := by
  have himage : (rotationOrbitMapCarrier q) '' (Set.univ : Set RotationCarrier) =
      (Set.univ : Set (RotationOrbitCarrier q)) := by
    rw [Set.image_univ]
    apply Set.eq_univ_of_forall
    intro w
    rcases w.2 with ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  exact (Homeomorph.Set.univ RotationCarrier).symm.trans
    (((continuous_rotationOrbitMapCarrier q).isClosedEmbedding
      (rotationOrbitMapCarrier_injective_of_pos hr q)).homeomorphImage
        (Set.univ : Set RotationCarrier))
    |>.trans (Homeomorph.setCongr himage)
    |>.trans (Homeomorph.Set.univ (RotationOrbitCarrier q))

theorem isClosedMap_rotationOrbitMapCarrier_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    IsClosedMap (rotationOrbitMapCarrier q) := by
  exact (continuous_rotationOrbitMapCarrier q).isClosedEmbedding
    (rotationOrbitMapCarrier_injective_of_pos hr q) |>.isClosedMap

theorem isProperMap_rotationOrbitMapCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsProperMap (rotationOrbitMapCarrier q) := by
  exact (continuous_rotationOrbitMapCarrier q).isProperMap

theorem isQuotientMap_rotationOrbitMapCarrier_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    Topology.IsQuotientMap (rotationOrbitMapCarrier q) := by
  exact (isClosedMap_rotationOrbitMapCarrier_of_pos hr q).isQuotientMap
    (continuous_rotationOrbitMapCarrier q)
    (rotationOrbitMapCarrier_surjective q)

def rotationMomentumLevel
    {r : ℝ} (j : ℝ) : Set (CasimirFiberCarrier r) :=
  {q | q.1.1 = j}

theorem rotationOrbit_eq_rotationMomentumLevel_of_pos
    {r : ℝ} (hr : 0 < r) (q : CasimirFiberCarrier r) :
    rotationOrbit q = rotationMomentumLevel q.1.1 := by
  apply Set.Subset.antisymm
  · rintro w ⟨g, rfl⟩
    change (momentumRotationCoordinates g.1.1 g.1.2 q.1).1 = q.1.1
    rfl
  · intro w hw
    change w.1.1 = q.1.1 at hw
    let c : ℝ :=
      (q.1.2.1 * w.1.2.1 + q.1.2.2 * w.1.2.2) / r
    let s : ℝ :=
      (q.1.2.1 * w.1.2.2 - q.1.2.2 * w.1.2.1) / r
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hq : q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = r := by
      exact q.2
    have hwlevel : w.1.2.1 ^ 2 + w.1.2.2 ^ 2 = r := by
      exact w.2
    have hdotcross :
        (q.1.2.1 * w.1.2.1 + q.1.2.2 * w.1.2.2) ^ 2 +
            (q.1.2.1 * w.1.2.2 - q.1.2.2 * w.1.2.1) ^ 2 =
          (q.1.2.1 ^ 2 + q.1.2.2 ^ 2) *
            (w.1.2.1 ^ 2 + w.1.2.2 ^ 2) := by
      ring
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp [c, s]
      rw [div_pow, div_pow, ← add_div, hdotcross, hq, hwlevel]
      field_simp
    let g : RotationCarrier :=
      ⟨(c, s), by simpa [rotationCircle] using hcs⟩
    have hfirst : momentumRotationCoordinates c s q.1 = w.1 := by
      ext
      · exact hw.symm
      · dsimp [momentumRotationCoordinates, c, s]
        field_simp [hr0]
        linear_combination w.1.2.1 * hq
      · dsimp [momentumRotationCoordinates, c, s]
        field_simp [hr0]
        linear_combination w.1.2.2 * hq
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hfirst

theorem rotationOrbit_eq_iff_j_eq_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    rotationOrbit q = rotationOrbit w ↔ q.1.1 = w.1.1 := by
  constructor
  · intro horbit
    have hqmem : q ∈ rotationOrbit q := by
      exact ⟨1, rotationMomentumAction_one q⟩
    have hqmem' : q ∈ rotationOrbit w := by
      rw [← horbit]
      exact hqmem
    rcases hqmem' with ⟨g, hg⟩
    change rotationMomentumAction g w = q at hg
    dsimp [rotationMomentumAction, momentumRotationFiber] at hg
    have hgj := congrArg (fun u : CasimirFiberCarrier r => u.1.1) hg
    change (momentumRotationCoordinates g.1.1 g.1.2 w.1).1 = q.1.1 at hgj
    simpa [momentumRotationCoordinates] using hgj.symm
  · intro hj
    rw [rotationOrbit_eq_rotationMomentumLevel_of_pos hr q,
      rotationOrbit_eq_rotationMomentumLevel_of_pos hr w]
    ext u
    constructor <;> intro hu
    · change u.1.1 = q.1.1 at hu
      change u.1.1 = w.1.1
      exact hu.trans hj
    · change u.1.1 = w.1.1 at hu
      change u.1.1 = q.1.1
      exact hu.trans hj.symm

theorem rotationOrbit_eq_or_disjoint_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    rotationOrbit q = rotationOrbit w ∨
      Disjoint (rotationOrbit q) (rotationOrbit w) := by
  by_cases hj : q.1.1 = w.1.1
  · exact Or.inl ((rotationOrbit_eq_iff_j_eq_of_pos hr q w).mpr hj)
  · right
    rw [Set.disjoint_left]
    intro z hzq hzw
    rcases hzq with ⟨g, hg⟩
    rcases hzw with ⟨h, hh⟩
    change rotationMomentumAction g q = z at hg
    change rotationMomentumAction h w = z at hh
    dsimp [rotationMomentumAction, momentumRotationFiber] at hg hh
    have hgj := congrArg (fun u : CasimirFiberCarrier r => u.1.1) hg
    have hhj := congrArg (fun u : CasimirFiberCarrier r => u.1.1) hh
    change q.1.1 = z.1.1 at hgj
    change w.1.1 = z.1.1 at hhj
    exact hj (hgj.trans hhj.symm)

theorem rotationMomentumAction_eq_self_of_zero
    (g : RotationCarrier) (q : CasimirFiberCarrier 0) :
    g • q = q := by
  have hq : q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 0 := by
    exact q.2
  have hp1 : q.1.2.1 = 0 := by
    nlinarith [sq_nonneg q.1.2.1, sq_nonneg q.1.2.2]
  have hp2 : q.1.2.2 = 0 := by
    nlinarith [sq_nonneg q.1.2.1, sq_nonneg q.1.2.2]
  apply Subtype.ext
  change momentumRotationCoordinates g.1.1 g.1.2 q.1 = q.1
  ext
  · rfl
  · dsimp [momentumRotationCoordinates]
    rw [hp1, hp2]
    ring
  · dsimp [momentumRotationCoordinates]
    rw [hp1, hp2]
    ring

theorem rotationOrbit_eq_singleton_of_zero
    (q : CasimirFiberCarrier 0) :
    rotationOrbit q = ({q} : Set (CasimirFiberCarrier 0)) := by
  ext w
  constructor
  · rintro ⟨g, hg⟩
    change rotationMomentumAction g q = w at hg
    change g • q = w at hg
    rw [rotationMomentumAction_eq_self_of_zero] at hg
    exact Set.mem_singleton_iff.mpr hg.symm
  · intro hw
    have hwq : w = q := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨1, rotationMomentumAction_one q⟩

theorem rotationOrbit_eq_iff_j_eq_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) (q w : CasimirFiberCarrier r) :
    rotationOrbit q = rotationOrbit w ↔ q.1.1 = w.1.1 := by
  rcases hr.eq_or_lt with rfl | hrpos
  · rw [rotationOrbit_eq_singleton_of_zero,
      rotationOrbit_eq_singleton_of_zero]
    constructor
    · intro h
      have hqw : q = w := by
        apply Set.mem_singleton_iff.mp
        rw [← h]
        exact Set.mem_singleton q
      exact congrArg (fun x : CasimirFiberCarrier 0 => x.1.1) hqw
    · intro hj
      have hq : q.1.2.1 = 0 := by
        have hzero := q.2
        change q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 0 at hzero
        nlinarith [sq_nonneg q.1.2.1, sq_nonneg q.1.2.2]
      have hw : w.1.2.1 = 0 := by
        have hzero := w.2
        change w.1.2.1 ^ 2 + w.1.2.2 ^ 2 = 0 at hzero
        nlinarith [sq_nonneg w.1.2.1, sq_nonneg w.1.2.2]
      have hq2 : q.1.2.2 = 0 := by
        have hzero := q.2
        change q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 0 at hzero
        nlinarith [sq_nonneg q.1.2.1, sq_nonneg q.1.2.2]
      have hw2 : w.1.2.2 = 0 := by
        have hzero := w.2
        change w.1.2.1 ^ 2 + w.1.2.2 ^ 2 = 0 at hzero
        nlinarith [sq_nonneg w.1.2.1, sq_nonneg w.1.2.2]
      have hqw : q = w := by
        apply Subtype.ext
        ext
        · exact hj
        · exact hq.trans hw.symm
        · exact hq2.trans hw2.symm
      exact congrArg (fun x => ({x} : Set (CasimirFiberCarrier 0))) hqw
  · exact rotationOrbit_eq_iff_j_eq_of_pos hrpos q w

theorem rotationOrbit_eq_or_disjoint_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) (q w : CasimirFiberCarrier r) :
    rotationOrbit q = rotationOrbit w ∨
      Disjoint (rotationOrbit q) (rotationOrbit w) := by
  rcases hr.eq_or_lt with rfl | hrpos
  · by_cases hj : q.1.1 = w.1.1
    · exact Or.inl
        ((rotationOrbit_eq_iff_j_eq_of_nonneg (le_refl 0) q w).mpr hj)
    · right
      rw [Set.disjoint_left, rotationOrbit_eq_singleton_of_zero,
        rotationOrbit_eq_singleton_of_zero]
      intro z hzq hzw
      have hzq' : z = q := Set.mem_singleton_iff.mp hzq
      have hzw' : z = w := Set.mem_singleton_iff.mp hzw
      exact hj (by rw [← hzq', ← hzw'])
  · exact rotationOrbit_eq_or_disjoint_of_pos hrpos q w

def coadjointRotationOrbitSetoid
    {r : ℝ} : Setoid (CasimirFiberCarrier r) where
  r v w := v.1.1 = w.1.1
  iseqv := {
    refl := by intro v; rfl
    symm := by intro v w h; exact h.symm
    trans := by intro u v w huv hvw; exact huv.trans hvw }

theorem isClosed_coadjointRotationOrbitSetoid_relation
    {r : ℝ} :
    IsClosed {p : CasimirFiberCarrier r × CasimirFiberCarrier r |
      coadjointRotationOrbitSetoid.r p.1 p.2} := by
  change IsClosed {p : CasimirFiberCarrier r × CasimirFiberCarrier r |
    p.1.1.1 = p.2.1.1}
  apply isClosed_eq
  · exact continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)

theorem coadjointRotationOrbitSetoid_rel_iff_orbit_eq_of_pos
    {r : ℝ} (hr : 0 < r) (q w : CasimirFiberCarrier r) :
    coadjointRotationOrbitSetoid.r q w ↔
      rotationOrbit q = rotationOrbit w := by
  exact (rotationOrbit_eq_iff_j_eq_of_pos hr q w).symm

theorem coadjointRotationOrbitSetoid_rel_iff_orbit_eq_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) (q w : CasimirFiberCarrier r) :
    coadjointRotationOrbitSetoid.r q w ↔
      rotationOrbit q = rotationOrbit w := by
  exact (rotationOrbit_eq_iff_j_eq_of_nonneg hr q w).symm

def coadjointRotationOrbitQuotientJ
    {r : ℝ} : Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ :=
  Quotient.lift (fun q : CasimirFiberCarrier r => q.1.1) (by
    intro q w h
    exact h)

theorem coadjointRotationOrbitQuotientJ_mk
    {r : ℝ} (q : CasimirFiberCarrier r) :
    coadjointRotationOrbitQuotientJ (r := r) (Quotient.mk'' q) = q.1.1 := rfl

theorem continuous_coadjointRotationOrbitQuotientJ
    {r : ℝ} :
    Continuous (coadjointRotationOrbitQuotientJ (r := r) :
      Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  apply Continuous.quotient_lift
  exact continuous_fst.comp continuous_subtype_val

theorem coadjointRotationOrbitQuotientJ_injective
    {r : ℝ} :
    Function.Injective (coadjointRotationOrbitQuotientJ (r := r) :
      Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h q₁ =>
    induction q₂ using Quotient.inductionOn with
    | h q₂ =>
      apply Quotient.sound
      exact h

noncomputable def coadjointRotationRepresentative
    {r : ℝ} (hr : 0 ≤ r) (j : ℝ) : CasimirFiberCarrier r :=
  ⟨(j, Real.sqrt r, 0), by
    change (Real.sqrt r) ^ 2 + 0 ^ 2 = r
    simpa using Real.sq_sqrt hr⟩

noncomputable def casimirFiberCylinderParam
    {r : ℝ} (hr : 0 ≤ r) :
    ℝ × RotationCarrier → CasimirFiberCarrier r :=
  fun p => p.2 • coadjointRotationRepresentative hr p.1

theorem continuous_casimirFiberCylinderParam
    {r : ℝ} (hr : 0 ≤ r) :
    Continuous (casimirFiberCylinderParam hr) := by
  have hrep : Continuous (fun j : ℝ => coadjointRotationRepresentative hr j) := by
    unfold coadjointRotationRepresentative
    fun_prop
  have hp : Continuous (fun p : ℝ × RotationCarrier =>
      (p.2, coadjointRotationRepresentative hr p.1)) := by
    exact continuous_snd.prodMk (hrep.comp continuous_fst)
  exact continuous_rotationMomentumAction.comp hp

theorem casimirFiberCylinderParam_surjective
    {r : ℝ} (hr : 0 ≤ r) :
    Function.Surjective (casimirFiberCylinderParam hr) := by
  intro q
  let q₀ := coadjointRotationRepresentative hr q.1.1
  have hOrbit : rotationOrbit q₀ = rotationOrbit q := by
    apply (rotationOrbit_eq_iff_j_eq_of_nonneg hr q₀ q).2
    rfl
  have hqmem : q ∈ rotationOrbit q := by
    exact ⟨1, rotationMomentumAction_one q⟩
  have hqmem₀ : q ∈ rotationOrbit q₀ := by
    rw [hOrbit]
    exact hqmem
  rcases hqmem₀ with ⟨g, hg⟩
  refine ⟨(q.1.1, g), ?_⟩
  change rotationMomentumAction g q₀ = q
  exact hg

theorem pathConnectedSpace_casimirFiber
    {r : ℝ} (hr : 0 ≤ r) : PathConnectedSpace (CasimirFiberCarrier r) := by
  letI : PathConnectedSpace (ℝ × RotationCarrier) := by
    rw [pathConnectedSpace_iff]
    constructor
    · exact ⟨(0, 1)⟩
    · intro x y
      have hx : Joined x.1 y.1 := by
        exact (pathConnectedSpace_iff ℝ).mp inferInstance |>.2 x.1 y.1
      have hy : Joined x.2 y.2 := by
        exact (pathConnectedSpace_iff RotationCarrier).mp inferInstance |>.2 x.2 y.2
      exact ⟨(Joined.somePath hx).prod (Joined.somePath hy)⟩
  exact (casimirFiberCylinderParam_surjective hr).pathConnectedSpace
    (continuous_casimirFiberCylinderParam hr)

theorem isPathConnected_casimirFiber_univ
    {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (Set.univ : Set (CasimirFiberCarrier r)) := by
  letI := pathConnectedSpace_casimirFiber hr
  exact isPathConnected_univ

theorem isConnected_casimirFiber_univ
    {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (Set.univ : Set (CasimirFiberCarrier r)) :=
  (isPathConnected_casimirFiber_univ hr).isConnected

theorem noncompact_casimirFiber_univ
    {r : ℝ} (hr : 0 ≤ r) :
    ¬ IsCompact (Set.univ : Set (CasimirFiberCarrier r)) := by
  intro hcompact
  let f : CasimirFiberCarrier r → ℝ := fun q => q.1.1
  have hf : Continuous f :=
    continuous_fst.comp continuous_subtype_val
  have himage : f '' (Set.univ : Set (CasimirFiberCarrier r)) = Set.univ := by
    rw [Set.image_univ]
    apply Set.eq_univ_of_forall
    intro j
    exact ⟨coadjointRotationRepresentative hr j, rfl⟩
  have hc : IsCompact (f '' (Set.univ : Set (CasimirFiberCarrier r))) :=
    hcompact.image hf
  rw [himage] at hc
  exact (noncompact_univ ℝ) hc

theorem coadjointRotationOrbitQuotientJ_surjective
    {r : ℝ} (hr : 0 ≤ r) :
    Function.Surjective (coadjointRotationOrbitQuotientJ (r := r) :
      Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  intro j
  refine ⟨Quotient.mk'' (coadjointRotationRepresentative hr j), ?_⟩
  rfl

noncomputable def coadjointRotationOrbitQuotientJHomeomorph
    {r : ℝ} (hr : 0 ≤ r) :
    Quotient (coadjointRotationOrbitSetoid (r := r)) ≃ₜ ℝ where
  toFun := coadjointRotationOrbitQuotientJ (r := r)
  invFun := fun j => Quotient.mk'' (coadjointRotationRepresentative hr j)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      apply Quotient.sound
      rfl
  right_inv := by
    intro j
    rfl
  continuous_toFun := continuous_coadjointRotationOrbitQuotientJ (r := r)
  continuous_invFun := by
    apply continuous_quotient_mk'.comp
    unfold coadjointRotationRepresentative
    fun_prop

theorem isClosedMap_coadjointRotationOrbitQuotientJ
    {r : ℝ} (hr : 0 ≤ r) :
    IsClosedMap
      (coadjointRotationOrbitQuotientJ (r := r) :
        Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.isClosedMap

theorem isOpenMap_coadjointRotationOrbitQuotientJ
    {r : ℝ} (hr : 0 ≤ r) :
    IsOpenMap
      (coadjointRotationOrbitQuotientJ (r := r) :
        Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.isOpenMap

theorem isProperMap_coadjointRotationOrbitQuotientJ
    {r : ℝ} (hr : 0 ≤ r) :
    IsProperMap
      (coadjointRotationOrbitQuotientJ (r := r) :
        Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.isProperMap

theorem isQuotientMap_coadjointRotationOrbitQuotientJ
    {r : ℝ} (hr : 0 ≤ r) :
    Topology.IsQuotientMap
      (coadjointRotationOrbitQuotientJ (r := r) :
        Quotient (coadjointRotationOrbitSetoid (r := r)) → ℝ) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.isQuotientMap

theorem t2Space_coadjointRotationOrbitQuotient
    {r : ℝ} (hr : 0 ≤ r) :
    T2Space (Quotient (coadjointRotationOrbitSetoid (r := r))) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.symm.t2Space

theorem secondCountableTopology_coadjointRotationOrbitQuotient
    {r : ℝ} (hr : 0 ≤ r) :
    SecondCountableTopology (Quotient (coadjointRotationOrbitSetoid (r := r))) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.secondCountableTopology

theorem locallyCompactSpace_coadjointRotationOrbitQuotient
    {r : ℝ} (hr : 0 ≤ r) :
    LocallyCompactSpace (Quotient (coadjointRotationOrbitSetoid (r := r))) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.isClosedEmbedding.locallyCompactSpace

theorem pathConnectedSpace_coadjointRotationOrbitQuotient
    {r : ℝ} (hr : 0 ≤ r) :
    PathConnectedSpace (Quotient (coadjointRotationOrbitSetoid (r := r))) := by
  let h := coadjointRotationOrbitQuotientJHomeomorph hr
  exact h.symm.surjective.pathConnectedSpace h.symm.continuous_toFun

theorem isPathConnected_coadjointRotationOrbitQuotient_univ
    {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected
      (Set.univ : Set (Quotient (coadjointRotationOrbitSetoid (r := r)))) := by
  letI := pathConnectedSpace_coadjointRotationOrbitQuotient hr
  exact isPathConnected_univ

theorem isConnected_coadjointRotationOrbitQuotient_univ
    {r : ℝ} (hr : 0 ≤ r) :
    IsConnected
      (Set.univ : Set (Quotient (coadjointRotationOrbitSetoid (r := r)))) :=
  (isPathConnected_coadjointRotationOrbitQuotient_univ hr).isConnected

noncomputable def coadjointRotationOrbitQuotientJSection
    {r : ℝ} (hr : 0 ≤ r) :
    C(ℝ, Quotient (coadjointRotationOrbitSetoid (r := r))) :=
  { toFun := fun j => Quotient.mk'' (coadjointRotationRepresentative hr j)
    continuous_toFun := by
      apply continuous_quotient_mk'.comp
      unfold coadjointRotationRepresentative
      fun_prop }

theorem coadjointRotationOrbitQuotientJSection_apply
    {r : ℝ} (hr : 0 ≤ r) (j : ℝ) :
    coadjointRotationOrbitQuotientJSection hr j =
      Quotient.mk'' (coadjointRotationRepresentative hr j) := rfl

def coadjointRotationOrbitQuotientJContinuousMap
    {r : ℝ} :
    C(Quotient (coadjointRotationOrbitSetoid (r := r)), ℝ) :=
  { toFun := coadjointRotationOrbitQuotientJ
    continuous_toFun := continuous_coadjointRotationOrbitQuotientJ }

theorem coadjointRotationOrbitQuotientJ_comp_section
    {r : ℝ} (hr : 0 ≤ r) :
    (coadjointRotationOrbitQuotientJContinuousMap (r := r)).comp
        (coadjointRotationOrbitQuotientJSection hr) =
      ContinuousMap.id ℝ := by
  apply ContinuousMap.ext
  intro j
  rw [ContinuousMap.comp_apply, ContinuousMap.id_apply,
    coadjointRotationOrbitQuotientJSection_apply]
  change coadjointRotationOrbitQuotientJ (r := r)
      (Quotient.mk'' (coadjointRotationRepresentative hr j)) = j
  rw [coadjointRotationOrbitQuotientJ_mk]
  rfl

def coadjointRotationOrbitQuotientAction
    {r : ℝ} (g : RotationCarrier) :
    Quotient (coadjointRotationOrbitSetoid (r := r)) →
      Quotient (coadjointRotationOrbitSetoid (r := r)) :=
  Quotient.lift (fun q => Quotient.mk'' (g • q)) (by
    intro q w h
    apply Quotient.sound
    change (g • q).1.1 = (g • w).1.1
    simpa [rotationMomentumAction, momentumRotationFiber,
      momentumRotationCoordinates] using h)

theorem coadjointRotationOrbitQuotientAction_mk
    {r : ℝ} (g : RotationCarrier) (q : CasimirFiberCarrier r) :
    coadjointRotationOrbitQuotientAction g (Quotient.mk'' q) =
      Quotient.mk'' (g • q) := rfl

theorem coadjointRotationOrbitQuotientAction_one
    {r : ℝ} (q : Quotient (coadjointRotationOrbitSetoid (r := r))) :
    coadjointRotationOrbitQuotientAction (1 : RotationCarrier) q = q := by
  induction q using Quotient.inductionOn with
  | h q =>
      rw [coadjointRotationOrbitQuotientAction_mk, one_smul]

theorem coadjointRotationOrbitQuotientAction_mul
    {r : ℝ} (g h : RotationCarrier)
    (q : Quotient (coadjointRotationOrbitSetoid (r := r))) :
    coadjointRotationOrbitQuotientAction (g * h) q =
      coadjointRotationOrbitQuotientAction g
        (coadjointRotationOrbitQuotientAction h q) := by
  induction q using Quotient.inductionOn with
  | h q =>
      rw [coadjointRotationOrbitQuotientAction_mk,
        coadjointRotationOrbitQuotientAction_mk,
        coadjointRotationOrbitQuotientAction_mk, mul_smul]

instance {r : ℝ} : MulAction RotationCarrier
    (Quotient (coadjointRotationOrbitSetoid (r := r))) where
  smul := coadjointRotationOrbitQuotientAction
  one_smul := coadjointRotationOrbitQuotientAction_one
  mul_smul := coadjointRotationOrbitQuotientAction_mul

theorem continuous_coadjointRotationOrbitQuotientAction_fixed
    {r : ℝ} (g : RotationCarrier) :
    Continuous (coadjointRotationOrbitQuotientAction (r := r) g) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_rotationMomentumAction.comp
      (continuous_const.prodMk continuous_id))

theorem coadjointRotationOrbitQuotientAction_eq_id
    {r : ℝ} (g : RotationCarrier)
    (q : Quotient (coadjointRotationOrbitSetoid (r := r))) :
    coadjointRotationOrbitQuotientAction g q = q := by
  induction q using Quotient.inductionOn with
  | h q =>
      apply Quotient.sound
      rfl

theorem continuous_coadjointRotationOrbitQuotientAction_joint
    {r : ℝ} :
    Continuous (fun p : RotationCarrier ×
      Quotient (coadjointRotationOrbitSetoid (r := r)) =>
        coadjointRotationOrbitQuotientAction p.1 p.2) := by
  apply continuous_snd.congr
  intro p
  exact (coadjointRotationOrbitQuotientAction_eq_id p.1 p.2).symm

theorem isCompact_rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsCompact (rotationOrbit q) := by
  unfold rotationOrbit
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_rotationOrbitMap q)

theorem isCompact_rotationOrbitCarrier
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsCompact (Set.univ : Set (RotationOrbitCarrier q)) := by
  rw [Subtype.isCompact_iff]
  simpa using isCompact_rotationOrbit q

theorem isPathConnected_rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsPathConnected (rotationOrbit q) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact pathConnectedSpace_rotationOrbitCarrier q

theorem isConnected_rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsConnected (rotationOrbit q) :=
  (isPathConnected_rotationOrbit q).isConnected

instance {r : ℝ} (q : CasimirFiberCarrier r) :
    CompactSpace (RotationOrbitCarrier q) where
  isCompact_univ := isCompact_rotationOrbitCarrier q

theorem isClosed_rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsClosed (rotationOrbit q) := by
  exact (isCompact_rotationOrbit q).isClosed

theorem isClosedEmbedding_rotationOrbitCarrier_subtypeVal
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Topology.IsClosedEmbedding
      ((↑) : RotationOrbitCarrier q → CasimirFiberCarrier r) := by
  exact Topology.IsClosedEmbedding.subtypeVal (isClosed_rotationOrbit q)

theorem isClosedMap_rotationOrbitCarrier_subtypeVal
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsClosedMap (((↑) : RotationOrbitCarrier q → CasimirFiberCarrier r)) := by
  exact (isClosedEmbedding_rotationOrbitCarrier_subtypeVal q).isClosedMap

theorem isProperMap_rotationOrbitCarrier_subtypeVal
    {r : ℝ} (q : CasimirFiberCarrier r) :
    IsProperMap (((↑) : RotationOrbitCarrier q → CasimirFiberCarrier r)) := by
  exact continuous_subtype_val.isProperMap

theorem nonempty_rotationOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    (rotationOrbit q).Nonempty := by
  exact ⟨q, ⟨1, rotationMomentumAction_one q⟩⟩

def rotationKKSOrbitReadout
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) (g : RotationCarrier) : ℝ :=
  affineKKSFiberCoordinates m r (g • q) X Y

theorem continuous_rotationKKSOrbitReadout
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) :
    Continuous (rotationKKSOrbitReadout m r q X Y) := by
  unfold rotationKKSOrbitReadout
  have hOrbit : Continuous (fun g : RotationCarrier => g • q) := by
    simpa only [Function.comp_apply] using
      continuous_rotationMomentumAction.comp (continuous_id.prodMk continuous_const)
  simpa only [Function.comp_apply] using
    (continuous_affineKKSFiberCoordinates m r).comp
      (hOrbit.prodMk (continuous_const.prodMk continuous_const))

def rotationKKSOrbitReadoutImage
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) : Set ℝ :=
  Set.range (rotationKKSOrbitReadout m r q X Y)

theorem isCompact_rotationKKSOrbitReadoutImage
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) :
    IsCompact (rotationKKSOrbitReadoutImage m r q X Y) := by
  unfold rotationKKSOrbitReadoutImage
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_rotationKKSOrbitReadout m r q X Y)

theorem isClosed_rotationKKSOrbitReadoutImage
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) :
    IsClosed (rotationKKSOrbitReadoutImage m r q X Y) := by
  exact (isCompact_rotationKKSOrbitReadoutImage m r q X Y).isClosed

theorem nonempty_rotationKKSOrbitReadoutImage
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) :
    (rotationKKSOrbitReadoutImage m r q X Y).Nonempty := by
  refine ⟨rotationKKSOrbitReadout m r q X Y 1, ?_⟩
  exact ⟨1, rfl⟩

def rotationKKSOrbitReadoutContinuousMap
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) : C(RotationCarrier, ℝ) :=
  { toFun := rotationKKSOrbitReadout m r q X Y
    continuous_toFun := continuous_rotationKKSOrbitReadout m r q X Y }

theorem rotationKKSOrbitReadoutContinuousMap_apply
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) (g : RotationCarrier) :
    rotationKKSOrbitReadoutContinuousMap m r q X Y g =
      rotationKKSOrbitReadout m r q X Y g := rfl

theorem rotationKKSOrbitReadoutContinuousMap_range_eq_image
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) :
    Set.range (rotationKKSOrbitReadoutContinuousMap m r q X Y) =
      rotationKKSOrbitReadoutImage m r q X Y := by
  rfl

theorem isCompact_rotationKKSOrbitContinuousMap_range
    (m r : ℝ) (q : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) :
    IsCompact (Set.range (rotationKKSOrbitReadoutContinuousMap m r q X Y)) := by
  rw [← Set.image_univ]
  exact isCompact_univ.image
    (rotationKKSOrbitReadoutContinuousMap m r q X Y).continuous

end SE2Souriau.CompactRotation
