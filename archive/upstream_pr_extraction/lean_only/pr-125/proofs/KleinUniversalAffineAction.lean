import proofs.KleinAffineDeckGroup
import proofs.KleinBrillouinBase
import proofs.KleinBottleOrbitQuotient
import proofs.KleinGlideCovering

/-!
# The integral Klein deck group acting on the affine reciprocal plane

The presented generators act by the genuine glide and transverse period
translation.  Pulling this representation through the certified semidirect
product equivalence gives the universal affine deck action.
-/

noncomputable section
namespace KleinUniversalAffineAction

open Filter Topology
open KleinBrillouinBase KleinPresentedGroup KleinAffineDeckGroup

abbrev SelfHomeomorph := Cover ≃ₜ Cover

instance : One SelfHomeomorph := ⟨Homeomorph.refl Cover⟩
instance : Mul SelfHomeomorph := ⟨fun f g ↦ g.trans f⟩
instance : Inv SelfHomeomorph := ⟨Homeomorph.symm⟩

instance : Group SelfHomeomorph where
  mul_assoc f g h := by apply DFunLike.ext; intro x; rfl
  one_mul f := by apply DFunLike.ext; intro x; rfl
  mul_one f := by apply DFunLike.ext; intro x; rfl
  inv_mul_cancel f := by
    apply DFunLike.ext
    intro x
    exact f.symm_apply_apply x

@[simp] theorem selfHomeomorph_one_apply (k : Cover) :
    (1 : SelfHomeomorph) k = k := rfl

@[simp] theorem selfHomeomorph_mul_apply (f g : SelfHomeomorph) (k : Cover) :
    (f * g) k = f (g k) := rfl

@[simp] theorem selfHomeomorph_inv_apply (f : SelfHomeomorph) (k : Cover) :
    f⁻¹ k = f.symm k := rfl

def glideHomeomorph : Cover ≃ₜ Cover where
  toFun := glide
  invFun := glideInv
  left_inv := glide_left_inverse
  right_inv := glide_right_inverse
  continuous_toFun := by
    exact (continuous_fst.add continuous_const).prodMk continuous_snd.neg
  continuous_invFun := by
    exact (continuous_fst.sub continuous_const).prodMk continuous_snd.neg

def tyHomeomorph : Cover ≃ₜ Cover where
  toFun := ty
  invFun := tyInv
  left_inv k := by apply Prod.ext <;> simp [ty, tyInv]
  right_inv k := by apply Prod.ext <;> simp [ty, tyInv]
  continuous_toFun := by
    exact continuous_fst.prodMk (continuous_snd.add continuous_const)
  continuous_invFun := by
    exact continuous_fst.prodMk (continuous_snd.sub continuous_const)

@[simp] theorem glideHomeomorph_symm_apply (k : Cover) :
    glideHomeomorph.symm k = glideInv k := rfl

@[simp] theorem tyHomeomorph_symm_apply (k : Cover) :
    tyHomeomorph.symm k = tyInv k := rfl

theorem affine_homeomorph_klein_relation :
    glideHomeomorph * tyHomeomorph * glideHomeomorph⁻¹ = tyHomeomorph⁻¹ := by
  apply DFunLike.ext
  intro k
  exact glide_conj_ty k

/-- The presented Klein group acts by affine deck homeomorphisms. -/
def presentedDeckRep : KleinGroup →* SelfHomeomorph :=
  kleinRep glideHomeomorph tyHomeomorph affine_homeomorph_klein_relation

/-- The same action in integral semidirect-product normal forms. -/
def affineDeckRep : AffineKleinGroup →* SelfHomeomorph :=
  presentedDeckRep.comp affineToPresented

instance : SMul AffineKleinGroup Cover where
  smul g k := affineDeckRep g k

instance : MulAction AffineKleinGroup Cover where
  one_smul k := by change affineDeckRep 1 k = k; rw [map_one]; rfl
  mul_smul g h k := by
    change affineDeckRep (g * h) k = affineDeckRep g (affineDeckRep h k)
    rw [map_mul]
    rfl

instance : ContinuousConstSMul AffineKleinGroup Cover where
  continuous_const_smul g := (affineDeckRep g).continuous

@[simp] theorem aGen_smul (k : Cover) : aGen • k = glide k := by
  change presentedDeckRep (affineToPresented aGen) k = glide k
  change presentedDeckRep (toKlein genA) k = glide k
  change kleinRep glideHomeomorph tyHomeomorph affine_homeomorph_klein_relation
      (toKlein genA) k = glide k
  rw [(kleinRep_relator_relation glideHomeomorph tyHomeomorph
    affine_homeomorph_klein_relation).1]
  rfl

@[simp] theorem bGen_smul (k : Cover) : bGen • k = ty k := by
  change presentedDeckRep (affineToPresented bGen) k = ty k
  change presentedDeckRep (toKlein genB) k = ty k
  change kleinRep glideHomeomorph tyHomeomorph affine_homeomorph_klein_relation
      (toKlein genB) k = ty k
  rw [(kleinRep_relator_relation glideHomeomorph tyHomeomorph
    affine_homeomorph_klein_relation).2]
  rfl

theorem tyHomeomorph_zpow_apply (n : ℤ) (k : Cover) :
    (tyHomeomorph ^ n) k = (k.1, k.2 + (n : ℝ) * (2 * Real.pi)) := by
  induction n using Int.induction_on generalizing k with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one]
      change (tyHomeomorph ^ (n : ℤ)) (tyHomeomorph k) = _
      rw [ih]
      change (k.1, (k.2 + 2 * Real.pi) + (n : ℝ) * (2 * Real.pi)) = _
      apply Prod.ext <;> push_cast <;> ring
  | pred n ih =>
      rw [show (-(n : ℤ) - 1) = -(n : ℤ) + (-1) by ring, zpow_add, zpow_neg_one]
      change (tyHomeomorph ^ (-(n : ℤ))) (tyHomeomorph⁻¹ k) = _
      rw [ih]
      rw [selfHomeomorph_inv_apply]
      rw [tyHomeomorph_symm_apply]
      push_cast
      change ((tyInv k).1, (tyInv k).2 + (-(n : ℤ) : ℝ) * (2 * Real.pi)) = _
      change (k.1, (k.2 - 2 * Real.pi) + (-(n : ℤ) : ℝ) * (2 * Real.pi)) = _
      apply Prod.ext <;> push_cast <;> ring

theorem glideHomeomorph_zpow_apply (m : ℤ) (k : Cover) :
    (glideHomeomorph ^ m) k =
      (k.1 + (m : ℝ) * Real.pi, ((-1 : ℝ) ^ m) * k.2) := by
  induction m using Int.induction_on generalizing k with
  | zero => simp
  | succ m ih =>
      rw [zpow_add_one]
      change (glideHomeomorph ^ (m : ℤ)) (glideHomeomorph k) = _
      rw [ih]
      change ((k.1 + Real.pi) + (m : ℝ) * Real.pi,
          ((-1 : ℝ) ^ (m : ℤ)) * (-k.2)) = _
      apply Prod.ext
      · push_cast; ring
      · change ((-1 : ℝ) ^ (m : ℤ)) * (-k.2) =
          ((-1 : ℝ) ^ ((m : ℤ) + 1)) * k.2
        have hz := zpow_add_one₀ (show (-1 : ℝ) ≠ 0 by norm_num) (m : ℤ)
        rw [hz]
        ring
  | pred m ih =>
      rw [show (-(m : ℤ) - 1) = -(m : ℤ) + (-1) by ring,
        zpow_add, zpow_neg_one]
      change (glideHomeomorph ^ (-(m : ℤ))) (glideHomeomorph⁻¹ k) = _
      rw [ih]
      rw [selfHomeomorph_inv_apply]
      rw [glideHomeomorph_symm_apply]
      push_cast
      change ((glideInv k).1 + (-(m : ℤ) : ℝ) * Real.pi,
          ((-1 : ℝ) ^ (-(m : ℤ))) * (glideInv k).2) = _
      change ((k.1 - Real.pi) + (-(m : ℤ) : ℝ) * Real.pi,
          ((-1 : ℝ) ^ (-(m : ℤ))) * (-k.2)) = _
      apply Prod.ext
      · push_cast; ring
      · rw [zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num), zpow_neg_one]
        norm_num

/-- Closed coordinate formula for every affine Klein deck transformation. -/
theorem affine_normal_form_smul (n m : ℤ) (k : Cover) :
    ((⟨Multiplicative.ofAdd n, Multiplicative.ofAdd m⟩ : AffineKleinGroup) • k) =
      (k.1 + (m : ℝ) * Real.pi,
        ((-1 : ℝ) ^ m) * k.2 + (n : ℝ) * (2 * Real.pi)) := by
  change presentedDeckRep
      (affineToPresented ⟨Multiplicative.ofAdd n, Multiplicative.ofAdd m⟩) k = _
  change presentedDeckRep
      (bPowers (Multiplicative.ofAdd n) * aPowers (Multiplicative.ofAdd m)) k = _
  rw [map_mul]
  change (presentedDeckRep ((toKlein genB) ^ n) *
      presentedDeckRep ((toKlein genA) ^ m)) k = _
  rw [map_zpow, map_zpow]
  change ((kleinRep glideHomeomorph tyHomeomorph affine_homeomorph_klein_relation
      (toKlein genB)) ^ n *
    (kleinRep glideHomeomorph tyHomeomorph affine_homeomorph_klein_relation
      (toKlein genA)) ^ m) k = _
  rw [(kleinRep_relator_relation glideHomeomorph tyHomeomorph
    affine_homeomorph_klein_relation).1,
    (kleinRep_relator_relation glideHomeomorph tyHomeomorph
    affine_homeomorph_klein_relation).2]
  change (tyHomeomorph ^ n) ((glideHomeomorph ^ m) k) = _
  rw [glideHomeomorph_zpow_apply, tyHomeomorph_zpow_apply]

/-- The universal-cover projection to the literal Klein orbit quotient. -/
def universalQuotientMap : Cover → KleinBottleOrbitQuotient.KleinBrillouinQuotient :=
  KleinBottleOrbitQuotient.quotientMap ∘ coverToTorus

theorem universalQuotientMap_aGen (k : Cover) :
    universalQuotientMap (aGen • k) = universalQuotientMap k := by
  simp only [universalQuotientMap, Function.comp_apply, aGen_smul, coverToTorus_glide]
  exact KleinBottleOrbitQuotient.quotientMap_glide _

theorem universalQuotientMap_bGen (k : Cover) :
    universalQuotientMap (bGen • k) = universalQuotientMap k := by
  simp only [universalQuotientMap, Function.comp_apply, bGen_smul, coverToTorus_ty]

theorem presentedDeckRep_invariant (g : KleinGroup) (k : Cover) :
    universalQuotientMap (presentedDeckRep g k) = universalQuotientMap k := by
  refine Quotient.inductionOn g ?_
  intro w
  change universalQuotientMap (presentedDeckRep (toKlein w) k) = universalQuotientMap k
  induction w using FreeGroup.induction_on generalizing k with
  | C1 =>
      change universalQuotientMap k = universalQuotientMap k
      rfl
  | of x =>
      cases x
      · change universalQuotientMap (glide k) = universalQuotientMap k
        simpa only [aGen_smul] using universalQuotientMap_aGen k
      · change universalQuotientMap (ty k) = universalQuotientMap k
        simpa only [bGen_smul] using universalQuotientMap_bGen k
  | inv_of x ih =>
      let f := presentedDeckRep (toKlein (FreeGroup.of x))
      have h := ih (f⁻¹ k)
      change universalQuotientMap (f⁻¹ k) = universalQuotientMap k
      rw [← h]
      exact congrArg universalQuotientMap (f.apply_symm_apply k)
  | mul x y hx hy =>
      rw [map_mul]
      rw [map_mul]
      change universalQuotientMap
          (presentedDeckRep (toKlein x) (presentedDeckRep (toKlein y) k)) =
        universalQuotientMap k
      exact (hx _).trans (hy _)

/-- Every integral affine deck transformation preserves the universal
projection to the literal Klein quotient. -/
theorem universalQuotientMap_smul (g : AffineKleinGroup) (k : Cover) :
    universalQuotientMap (g • k) = universalQuotientMap k := by
  exact presentedDeckRep_invariant (affineToPresented g) k

theorem universalQuotientMap_continuous : Continuous universalQuotientMap :=
  KleinBottleOrbitQuotient.quotientMap_continuous.comp <| by
    have hc : Continuous ((↑) : ℝ → MomentumCircle) := continuous_quot_mk
    exact (hc.comp continuous_fst).prodMk (hc.comp continuous_snd)

theorem circle_coe_eq_iff_periods (x y : ℝ) :
    (x : MomentumCircle) = (y : MomentumCircle) ↔
      ∃ n : ℤ, x = y + (n : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    have hz : ((x - y : ℝ) : MomentumCircle) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at hz
    obtain ⟨n, hn⟩ := hz
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul] at hn
    linarith
  · rintro ⟨n, rfl⟩
    rw [AddCircle.coe_add]
    have hp : (((n : ℝ) * (2 * Real.pi) : ℝ) : MomentumCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (2 * Real.pi)).2
      refine ⟨n, ?_⟩
      rw [zsmul_eq_mul]
    rw [hp, add_zero]

theorem coverToTorus_eq_iff_periods (x y : Cover) :
    coverToTorus x = coverToTorus y ↔
      ∃ r s : ℤ,
        x.1 = y.1 + (r : ℝ) * (2 * Real.pi) ∧
        x.2 = y.2 + (s : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    obtain ⟨r, hr⟩ := (circle_coe_eq_iff_periods x.1 y.1).1 h1
    obtain ⟨s, hs⟩ := (circle_coe_eq_iff_periods x.2 y.2).1 h2
    exact ⟨r, s, hr, hs⟩
  · rintro ⟨r, s, hr, hs⟩
    apply Prod.ext
    · exact (circle_coe_eq_iff_periods x.1 y.1).2 ⟨r, hr⟩
    · exact (circle_coe_eq_iff_periods x.2 y.2).2 ⟨s, hs⟩

theorem universalQuotientMap_eq_iff_orbit (x y : Cover) :
    universalQuotientMap x = universalQuotientMap y ↔
      x ∈ MulAction.orbit AffineKleinGroup y := by
  constructor
  · intro h
    change KleinBottleOrbitQuotient.quotientMap (coverToTorus x) =
      KleinBottleOrbitQuotient.quotientMap (coverToTorus y) at h
    rw [KleinBottleOrbitQuotient.quotientMap_eq_iff] at h
    rcases h with hxy | hglide
    · have heq : coverToTorus x = coverToTorus y := hxy.symm
      obtain ⟨r, s, hr, hs⟩ := (coverToTorus_eq_iff_periods x y).1 heq
      let g : AffineKleinGroup :=
        ⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (2 * r)⟩
      refine ⟨g, ?_⟩
      change ((⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (2 * r)⟩ :
        AffineKleinGroup) • y) = x
      rw [affine_normal_form_smul]
      have heven : Even (2 * r) := even_two_mul r
      rw [heven.neg_one_zpow]
      apply Prod.ext
      · dsimp [g]
        push_cast at hr ⊢
        linarith
      · dsimp [g]
        simpa using hs.symm
    · have heq : coverToTorus x = coverToTorus (glide y) := by
        rw [coverToTorus_glide]
        calc
          coverToTorus x = torusGlide (torusGlide (coverToTorus x)) :=
            (torusGlide_involutive _).symm
          _ = torusGlide (coverToTorus y) := congrArg torusGlide hglide.symm
      obtain ⟨r, s, hr, hs⟩ :=
        (coverToTorus_eq_iff_periods x (glide y)).1 heq
      let g : AffineKleinGroup :=
        ⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (2 * r + 1)⟩
      refine ⟨g, ?_⟩
      change ((⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (2 * r + 1)⟩ :
        AffineKleinGroup) • y) = x
      rw [affine_normal_form_smul]
      have hodd : Odd (2 * r + 1) := odd_two_mul_add_one r
      rw [hodd.neg_one_zpow]
      apply Prod.ext
      · dsimp [g, glide] at hr ⊢
        push_cast at hr ⊢
        linarith
      · dsimp [g, glide] at hs ⊢
        simpa [mul_assoc] using hs.symm
  · rintro ⟨g, rfl⟩
    exact universalQuotientMap_smul g y

theorem coverToTorus_isOpenQuotientMap :
    IsOpenQuotientMap coverToTorus := by
  have hc : IsOpenQuotientMap ((↑) : ℝ → MomentumCircle) :=
    { surjective := QuotientAddGroup.mk_surjective
      continuous := (AddCircle.isCoveringMap_coe (2 * Real.pi)).continuous
      isOpenMap := (AddCircle.isCoveringMap_coe (2 * Real.pi)).isOpenMap }
  simpa only [coverToTorus] using hc.prodMap hc

theorem universalQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap universalQuotientMap := by
  exact KleinGlideCovering.quotientMap_isAddQuotientCovering.isOpenQuotientMap.comp
    coverToTorus_isOpenQuotientMap

private theorem int_eq_zero_of_abs_cast_lt_one {z : ℤ}
    (h : |(z : ℝ)| < 1) : z = 0 := by
  by_contra hz
  have hza : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have hzr : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast hza
  linarith

theorem affineDeck_smul_disjoint (k : Cover) :
    ∃ U ∈ nhds k,
      ∀ g : AffineKleinGroup, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  let r : ℝ := Real.pi / 4
  let U : Set Cover := Metric.ball k.1 r ×ˢ Metric.ball k.2 r
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨U, ?_, ?_⟩
  · exact (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
  · intro g hg
    rcases g with ⟨gn, gm⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, Multiplicative.ofAdd n = gn := ⟨gn.toAdd, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, Multiplicative.ofAdd m = gm := ⟨gm.toAdd, rfl⟩
    obtain ⟨_, ⟨p, hpU, rfl⟩, hgpU⟩ := hg
    change ((⟨Multiplicative.ofAdd n, Multiplicative.ofAdd m⟩ :
      AffineKleinGroup) • p) ∈ U at hgpU
    rw [affine_normal_form_smul] at hgpU
    have hp1 : |p.1 - k.1| < r := by simpa [Real.dist_eq] using hpU.1
    have hgp1 : |(p.1 + (m : ℝ) * Real.pi) - k.1| < r := by
      simpa [Real.dist_eq] using hgpU.1
    have hmPi : |(m : ℝ) * Real.pi| < Real.pi / 2 := by
      calc
        |(m : ℝ) * Real.pi| =
            |((p.1 + (m : ℝ) * Real.pi) - k.1) - (p.1 - k.1)| := by ring_nf
        _ ≤ |(p.1 + (m : ℝ) * Real.pi) - k.1| + |p.1 - k.1| := abs_sub _ _
        _ < r + r := add_lt_add hgp1 hp1
        _ = Real.pi / 2 := by dsimp [r]; ring
    have hmabs : |(m : ℝ)| < 1 := by
      rw [abs_mul, abs_of_pos Real.pi_pos] at hmPi
      nlinarith [Real.pi_pos]
    have hm : m = 0 := int_eq_zero_of_abs_cast_lt_one hmabs
    subst m
    have hp2 : |p.2 - k.2| < r := by simpa [Real.dist_eq] using hpU.2
    have hgp2 : |(p.2 + (n : ℝ) * (2 * Real.pi)) - k.2| < r := by
      simpa [Real.dist_eq] using hgpU.2
    have hnPi : |(n : ℝ) * (2 * Real.pi)| < Real.pi / 2 := by
      calc
        |(n : ℝ) * (2 * Real.pi)| =
            |((p.2 + (n : ℝ) * (2 * Real.pi)) - k.2) - (p.2 - k.2)| := by ring_nf
        _ ≤ |(p.2 + (n : ℝ) * (2 * Real.pi)) - k.2| + |p.2 - k.2| := abs_sub _ _
        _ < r + r := add_lt_add hgp2 hp2
        _ = Real.pi / 2 := by dsimp [r]; ring
    have hnabs : |(n : ℝ)| < 1 := by
      rw [abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)] at hnPi
      nlinarith [Real.pi_pos]
    have hn : n = 0 := int_eq_zero_of_abs_cast_lt_one hnabs
    subst n
    rfl

/-- The affine plane is a native universal-candidate quotient covering of the
literal Klein orbit space, with integral Klein deck group. -/
theorem universalQuotientMap_isQuotientCovering :
    IsQuotientCoveringMap universalQuotientMap AffineKleinGroup where
  toIsQuotientMap := universalQuotientMap_isOpenQuotientMap.isQuotientMap
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := fun {e₁ e₂} ↦ universalQuotientMap_eq_iff_orbit e₁ e₂
  disjoint := affineDeck_smul_disjoint

theorem universalQuotientMap_isCovering : IsCoveringMap universalQuotientMap :=
  universalQuotientMap_isQuotientCovering.isCoveringMap

end KleinUniversalAffineAction
end noncomputable section
