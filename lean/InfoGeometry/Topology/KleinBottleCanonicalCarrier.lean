/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.CompactMappingTorusGluing
import InfoGeometry.Topology.KleinBrillouinBase
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Canonical compact mapping-torus carrier for the Klein gluing

The carrier is the compact interval mapping torus of fibre negation.  The
quotient projection and the induced fibre flip are defined by `Quotient.lift`;
no identification with the independent torus-orbit quotient is asserted here.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCanonicalCarrier

open KleinBrillouinBase
open InfoGeometry.Topology.CompactMappingTorus
open CategoryTheory CategoryTheory.Limits

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def fibreNeg : MomentumCircle → MomentumCircle := Neg.neg

abbrev CanonicalKleinBottle : Type :=
  Carrier fibreNeg

def canonicalMk : Base × MomentumCircle → CanonicalKleinBottle :=
  project fibreNeg

@[simp] theorem canonical_endpoint (x : MomentumCircle) :
    canonicalMk (⟨0, by constructor <;> norm_num⟩, x) =
      canonicalMk (⟨1, by constructor <;> norm_num⟩, fibreNeg x) := by
  exact project_endpoint fibreNeg x

private theorem fibreFlip_step_respects {p q : Base × MomentumCircle}
    (h : endpointStep fibreNeg p q) :
    endpointStep fibreNeg (p.1, fibreNeg p.2) (q.1, fibreNeg q.2) := by
  rcases h with h | h
  · left
    exact ⟨h.1, h.2.1, by
      simpa [fibreNeg] using congrArg fibreNeg h.2.2⟩
  · right
    exact ⟨h.1, h.2.1, by
      simpa [fibreNeg] using congrArg fibreNeg h.2.2⟩

private theorem fibreFlip_respects : ∀ {p q : Base × MomentumCircle},
    Relation.EqvGen (endpointStep fibreNeg) p q →
      Relation.EqvGen (endpointStep fibreNeg)
        (p.1, fibreNeg p.2) (q.1, fibreNeg q.2) := by
  intro p q h
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ (fibreFlip_step_respects h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def fibreFlipMap : CanonicalKleinBottle → CanonicalKleinBottle :=
  @Quotient.lift (Base × MomentumCircle) CanonicalKleinBottle
    (endpointSetoid fibreNeg)
    (fun p => @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg)
      (p.1, fibreNeg p.2))
    (by
      intro p q h
      exact Quotient.sound (fibreFlip_respects h))

def canonicalFibreFlip : CanonicalKleinBottle ≃ CanonicalKleinBottle where
  toFun := fibreFlipMap
  invFun := fibreFlipMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg)
      (p.1, fibreNeg (fibreNeg p.2)) = @Quotient.mk _ _ p
    simp [fibreNeg]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg)
      (p.1, fibreNeg (fibreNeg p.2)) = @Quotient.mk _ _ p
    simp [fibreNeg]

@[simp] theorem canonicalFibreFlip_apply (p : Base × MomentumCircle) :
    canonicalFibreFlip (canonicalMk p) = canonicalMk (p.1, fibreNeg p.2) := by
  change fibreFlipMap (project fibreNeg p) = project fibreNeg (p.1, fibreNeg p.2)
  simp [fibreFlipMap, project]

 theorem canonicalFibreFlip_involutive (q : CanonicalKleinBottle) :
    canonicalFibreFlip (canonicalFibreFlip q) = q := by
  exact canonicalFibreFlip.left_inv q

/-! ## A genuine Möbius-band carrier and its boundary pushout -/

abbrev MobiusInterval := Set.Icc (0 : ℝ) 1

def mobiusFlip (x : MobiusInterval) : MobiusInterval :=
  ⟨1 - x.1, by constructor <;> linarith [x.2.1, x.2.2]⟩

theorem mobiusFlip_involutive (x : MobiusInterval) :
    mobiusFlip (mobiusFlip x) = x := by
  apply Subtype.ext
  dsimp [mobiusFlip]
  ring

abbrev MobiusBand := Carrier mobiusFlip

instance mobiusBand_compactSpace : CompactSpace MobiusBand :=
  Quotient.compactSpace

def mobiusBandMk : Base × MobiusInterval → MobiusBand :=
  project mobiusFlip

theorem mobiusBand_endpoint (x : MobiusInterval) :
    mobiusBandMk (⟨0, by constructor <;> norm_num⟩, x) =
      mobiusBandMk (⟨1, by constructor <;> norm_num⟩, mobiusFlip x) := by
  exact project_endpoint mobiusFlip x

def boundaryFlip : Bool → Bool
  | false => true
  | true => false

abbrev MobiusBoundary := Carrier boundaryFlip

instance mobiusBoundary_compactSpace : CompactSpace MobiusBoundary :=
  Quotient.compactSpace

def boundaryEndpoint : Bool → MobiusInterval
  | false => ⟨0, by constructor <;> norm_num⟩
  | true => ⟨1, by constructor <;> norm_num⟩

theorem boundaryEndpoint_flip (b : Bool) :
    boundaryEndpoint (boundaryFlip b) = mobiusFlip (boundaryEndpoint b) := by
  cases b <;> apply Subtype.ext <;>
    simp [boundaryEndpoint, boundaryFlip, mobiusFlip]

private theorem boundaryEndpoint_injective : Function.Injective boundaryEndpoint := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂
  · rfl
  · have hv := congrArg Subtype.val h
    norm_num [boundaryEndpoint] at hv
  · have hv := congrArg Subtype.val h
    norm_num [boundaryEndpoint] at hv
  · rfl

private theorem boundaryToBand_respects {p q : Base × Bool}
    (hpq : Relation.EqvGen (endpointStep boundaryFlip) p q) :
    mobiusBandMk (p.1, boundaryEndpoint p.2) =
      mobiusBandMk (q.1, boundaryEndpoint q.2) := by
  induction hpq with
  | rel p q h =>
      rcases h with h | h
      · apply Quotient.sound
        exact Relation.EqvGen.rel _ _ (Or.inl ⟨h.1, h.2.1, by
          rw [h.2.2]
          exact boundaryEndpoint_flip p.2⟩)
      · apply Quotient.sound
        exact Relation.EqvGen.rel _ _ (Or.inr ⟨h.1, h.2.1, by
          rw [h.2.2]
          exact boundaryEndpoint_flip q.2⟩)
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def boundaryToBand : MobiusBoundary → MobiusBand :=
  @Quotient.lift (Base × Bool) MobiusBand
    (endpointSetoid boundaryFlip)
    (fun p => mobiusBandMk (p.1, boundaryEndpoint p.2))
    (by intro p q hpq; exact boundaryToBand_respects hpq)

theorem boundaryToBand_continuous : Continuous boundaryToBand := by
  apply Continuous.quotient_lift
  · have hboundary : Continuous boundaryEndpoint := continuous_of_discreteTopology
    exact continuous_quotient_mk'.comp
      (continuous_fst.prodMk (hboundary.comp continuous_snd))

/-- The boundary quotient embeds pointwise into the Möbius-band quotient. -/
theorem boundaryToBand_injective : Function.Injective boundaryToBand := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro p q h
  change project mobiusFlip (p.1, boundaryEndpoint p.2) =
    project mobiusFlip (q.1, boundaryEndpoint q.2) at h
  have hrel : Relation.EqvGen (endpointStep mobiusFlip)
      (p.1, boundaryEndpoint p.2) (q.1, boundaryEndpoint q.2) :=
    Quotient.exact h
  rcases (endpointEqvGen_iff mobiusFlip_involutive
      (p.1, boundaryEndpoint p.2) (q.1, boundaryEndpoint q.2)).mp hrel with
    hpq | hpq
  · apply Quotient.sound
    have hp : p = q := by
      have hbase : p.1 = q.1 :=
        congrArg (fun z : Base × MobiusInterval => z.1) hpq
      have hend : boundaryEndpoint p.2 = boundaryEndpoint q.2 :=
        congrArg (fun z : Base × MobiusInterval => z.2) hpq
      exact Prod.ext hbase (boundaryEndpoint_injective hend)
    subst q
    exact Relation.EqvGen.refl _
  · apply Quotient.sound
    apply Relation.EqvGen.rel
    rcases hpq with hpq | hpq
    · left
      refine ⟨hpq.1, hpq.2.1, ?_⟩
      have hmap : boundaryEndpoint q.2 =
          boundaryEndpoint (boundaryFlip p.2) := by
        rw [boundaryEndpoint_flip]
        exact hpq.2.2
      exact boundaryEndpoint_injective hmap
    · right
      refine ⟨hpq.1, hpq.2.1, ?_⟩
      have hmap : boundaryEndpoint p.2 =
          boundaryEndpoint (boundaryFlip q.2) := by
        rw [boundaryEndpoint_flip]
        exact hpq.2.2
      exact boundaryEndpoint_injective hmap

abbrev MobiusBandObj : TopCat := TopCat.of MobiusBand
abbrev MobiusBoundaryObj : TopCat := TopCat.of MobiusBoundary

def boundaryToBandHom : MobiusBoundaryObj ⟶ MobiusBandObj :=
  TopCat.ofHom ⟨boundaryToBand, boundaryToBand_continuous⟩

/-! The double is the native TopCat pushout of the two identical boundary maps. -/

abbrev MobiusGluedObj : TopCat :=
  pushout boundaryToBandHom boundaryToBandHom

def mobiusGluedInl : MobiusBandObj ⟶ MobiusGluedObj :=
  pushout.inl boundaryToBandHom boundaryToBandHom

def mobiusGluedInr : MobiusBandObj ⟶ MobiusGluedObj :=
  pushout.inr boundaryToBandHom boundaryToBandHom

theorem mobiusGlued_boundary_condition :
    boundaryToBandHom ≫ mobiusGluedInl =
      boundaryToBandHom ≫ mobiusGluedInr := by
  exact pushout.condition

theorem mobiusGlued_hom_ext {Y : TopCat}
    (f g : MobiusGluedObj ⟶ Y)
    (h₁ : mobiusGluedInl ≫ f = mobiusGluedInl ≫ g)
    (h₂ : mobiusGluedInr ≫ f = mobiusGluedInr ≫ g) :
    f = g := by
  exact pushout.hom_ext h₁ h₂

theorem mobiusGlued_desc
    {Y : TopCat}
    (left right : MobiusBandObj ⟶ Y)
    (h : boundaryToBandHom ≫ left = boundaryToBandHom ≫ right) :
    mobiusGluedInl ≫ (pushout.desc left right h) = left := by
  exact pushout.inl_desc left right h

theorem mobiusGlued_desc_right
    {Y : TopCat}
    (left right : MobiusBandObj ⟶ Y)
    (h : boundaryToBandHom ≫ left = boundaryToBandHom ≫ right) :
    mobiusGluedInr ≫ (pushout.desc left right h) = right := by
  exact pushout.inr_desc left right h


/-- The left semicircle parametrized by the Möbius interval fibre. -/
def mobiusLeftArc (x : MobiusInterval) : MomentumCircle :=
  ((Real.pi * x.1 + Real.pi / 2 : ℝ) : MomentumCircle)

/-- The complementary semicircle parametrized with the opposite orientation. -/
def mobiusRightArc (x : MobiusInterval) : MomentumCircle :=
  ((Real.pi / 2 - Real.pi * x.1 : ℝ) : MomentumCircle)

theorem mobiusLeftArc_flip (x : MobiusInterval) :
    mobiusLeftArc (mobiusFlip x) = -mobiusLeftArc x := by
  change ((Real.pi * (1 - x.1) + Real.pi / 2 : ℝ) : MomentumCircle) =
    -((Real.pi * x.1 + Real.pi / 2 : ℝ) : MomentumCircle)
  have harg : Real.pi * (1 - x.1) + Real.pi / 2 =
      -(Real.pi * x.1 + Real.pi / 2) + 2 * Real.pi := by ring
  rw [harg, AddCircle.coe_add, two_pi_eq_zero, add_zero, AddCircle.coe_neg]

theorem mobiusRightArc_flip (x : MobiusInterval) :
    mobiusRightArc (mobiusFlip x) = -mobiusRightArc x := by
  change ((Real.pi / 2 - Real.pi * (1 - x.1) : ℝ) : MomentumCircle) =
    -((Real.pi / 2 - Real.pi * x.1 : ℝ) : MomentumCircle)
  have harg : Real.pi / 2 - Real.pi * (1 - x.1) =
      -(Real.pi / 2 - Real.pi * x.1) := by ring
  rw [harg, AddCircle.coe_neg]

theorem mobiusLeftArc_one_eq_right :
    mobiusLeftArc (⟨1, by constructor <;> norm_num⟩ : MobiusInterval) =
      mobiusRightArc (⟨1, by constructor <;> norm_num⟩ : MobiusInterval) := by
  simp only [mobiusLeftArc, mobiusRightArc]
  have harg : Real.pi * 1 + Real.pi / 2 =
      (Real.pi / 2 - Real.pi * 1) + 2 * Real.pi := by ring
  rw [harg, AddCircle.coe_add, two_pi_eq_zero, add_zero]

theorem mobiusLeftArc_injective : Function.Injective mobiusLeftArc := by
  intro x y h
  have hx : Real.pi * x.1 + Real.pi / 2 ∈
      Set.Ico (Real.pi / 2) (Real.pi / 2 + 2 * Real.pi) := by
    constructor
    · have hnonneg := mul_nonneg (le_of_lt Real.pi_pos) x.2.1
      linarith
    · have hmul : Real.pi * x.1 ≤ Real.pi := by
        simpa using mul_le_mul_of_nonneg_left x.2.2 (le_of_lt Real.pi_pos)
      nlinarith [Real.pi_pos, hmul]
  have hy : Real.pi * y.1 + Real.pi / 2 ∈
      Set.Ico (Real.pi / 2) (Real.pi / 2 + 2 * Real.pi) := by
    constructor
    · have hnonneg := mul_nonneg (le_of_lt Real.pi_pos) y.2.1
      linarith
    · have hmul : Real.pi * y.1 ≤ Real.pi := by
        simpa using mul_le_mul_of_nonneg_left y.2.2 (le_of_lt Real.pi_pos)
      nlinarith [Real.pi_pos, hmul]
  have harg : Real.pi * x.1 + Real.pi / 2 =
      Real.pi * y.1 + Real.pi / 2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp (by simpa [mobiusLeftArc] using h)
  apply Subtype.ext
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

theorem mobiusRightArc_injective : Function.Injective mobiusRightArc := by
  intro x y h
  have hx : Real.pi / 2 - Real.pi * x.1 ∈
      Set.Ico (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) := by
    constructor
    · have hmul := mul_le_mul_of_nonneg_left x.2.2 (le_of_lt Real.pi_pos)
      linarith
    · have hnonneg := mul_nonneg (le_of_lt Real.pi_pos) x.2.1
      have hupper : -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
      nlinarith [Real.pi_pos, hnonneg, hupper]
  have hy : Real.pi / 2 - Real.pi * y.1 ∈
      Set.Ico (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) := by
    constructor
    · have hmul := mul_le_mul_of_nonneg_left y.2.2 (le_of_lt Real.pi_pos)
      linarith
    · have hnonneg := mul_nonneg (le_of_lt Real.pi_pos) y.2.1
      have hupper : -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
      nlinarith [Real.pi_pos, hnonneg, hupper]
  have harg : Real.pi / 2 - Real.pi * x.1 =
      Real.pi / 2 - Real.pi * y.1 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp (by simpa [mobiusRightArc] using h)
  apply Subtype.ext
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

theorem mobiusLeftRightArc_eq_iff_boundary (x y : MobiusInterval) :
    mobiusLeftArc x = mobiusRightArc y ↔
      (x = ⟨0, by constructor <;> norm_num⟩ ∧
        y = ⟨0, by constructor <;> norm_num⟩) ∨
      (x = ⟨1, by constructor <;> norm_num⟩ ∧
        y = ⟨1, by constructor <;> norm_num⟩) := by
  constructor
  · intro h
    by_cases hxeq : x.1 = 1
    · let one : MobiusInterval := ⟨1, by constructor <;> norm_num⟩
      have hx : x = one := Subtype.ext hxeq
      subst x
      have hright : mobiusRightArc one = mobiusRightArc y :=
        mobiusLeftArc_one_eq_right.symm.trans h
      have hy : one = y := mobiusRightArc_injective hright
      right
      exact ⟨rfl, hy.symm⟩
    · have hxlt : x.1 < 1 := lt_of_le_of_ne x.2.2 hxeq
      have hupper : -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
      have hxmem : Real.pi * x.1 + Real.pi / 2 ∈
          Set.Ico (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) := by
        constructor
        · have hnonneg := mul_nonneg (le_of_lt Real.pi_pos) x.2.1
          nlinarith [Real.pi_pos, hnonneg]
        · have hmul := mul_lt_mul_of_pos_left hxlt Real.pi_pos
          nlinarith [Real.pi_pos, hmul, hupper]
      have hymem : Real.pi / 2 - Real.pi * y.1 ∈
          Set.Ico (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) := by
        constructor
        · have hmul := mul_le_mul_of_nonneg_left y.2.2 (le_of_lt Real.pi_pos)
          linarith
        · have hnonneg := mul_nonneg (le_of_lt Real.pi_pos) y.2.1
          nlinarith [Real.pi_pos, hnonneg, hupper]
      have harg : Real.pi * x.1 + Real.pi / 2 =
          Real.pi / 2 - Real.pi * y.1 :=
        (AddCircle.coe_eq_coe_iff_of_mem_Ico hxmem hymem).mp
          (by simpa [mobiusLeftArc, mobiusRightArc] using h)
      have hnonnegx := mul_nonneg (le_of_lt Real.pi_pos) x.2.1
      have hnonnegy := mul_nonneg (le_of_lt Real.pi_pos) y.2.1
      have hxterm : Real.pi * x.1 = 0 := by nlinarith [harg, hnonnegx, hnonnegy]
      have hyterm : Real.pi * y.1 = 0 := by nlinarith [harg, hnonnegx, hnonnegy]
      have hxzero : x.1 = 0 := (mul_eq_zero.mp hxterm).resolve_left Real.pi_ne_zero
      have hyzero : y.1 = 0 := (mul_eq_zero.mp hyterm).resolve_left Real.pi_ne_zero
      left
      exact ⟨Subtype.ext hxzero, Subtype.ext hyzero⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [mobiusLeftArc, mobiusRightArc]
    · exact mobiusLeftArc_one_eq_right

theorem mobiusLeftRightArc_eq_flip_iff_boundary (x y : MobiusInterval) :
    mobiusLeftArc x = -mobiusRightArc y ↔
      (x = ⟨0, by constructor <;> norm_num⟩ ∧
        y = ⟨1, by constructor <;> norm_num⟩) ∨
      (x = ⟨1, by constructor <;> norm_num⟩ ∧
        y = ⟨0, by constructor <;> norm_num⟩) := by
  constructor
  · intro h
    have hLR : mobiusLeftArc x = mobiusRightArc (mobiusFlip y) := by
      rw [mobiusRightArc_flip y]
      exact h
    rcases (mobiusLeftRightArc_eq_iff_boundary x (mobiusFlip y)).mp hLR with
      ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left
      constructor
      · exact hx
      · apply Subtype.ext
        have hv : 1 - y.1 = 0 := by
          simpa [mobiusFlip] using congrArg Subtype.val hy
        linarith
    · right
      constructor
      · exact hx
      · apply Subtype.ext
        have hv : 1 - y.1 = 1 := by
          simpa [mobiusFlip] using congrArg Subtype.val hy
        linarith
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · have hyval : y.1 = 1 := congrArg Subtype.val hy
      have hyflip : mobiusFlip y = ⟨0, by constructor <;> norm_num⟩ := by
        apply Subtype.ext
        simp [mobiusFlip, hyval]
      have hLR := (mobiusLeftRightArc_eq_iff_boundary x (mobiusFlip y)).mpr
        (Or.inl ⟨hx, hyflip⟩)
      rw [mobiusRightArc_flip y] at hLR
      exact hLR
    · have hyval : y.1 = 0 := congrArg Subtype.val hy
      have hyflip : mobiusFlip y = ⟨1, by constructor <;> norm_num⟩ := by
        apply Subtype.ext
        simp [mobiusFlip, hyval]
      have hLR := (mobiusLeftRightArc_eq_iff_boundary x (mobiusFlip y)).mpr
        (Or.inr ⟨hx, hyflip⟩)
      rw [mobiusRightArc_flip y] at hLR
      exact hLR

private theorem mobiusBoundary_seam_eq {a c : Base} (b : Bool)
    (h : (a.1 = 0 ∧ c.1 = 1) ∨ (a.1 = 1 ∧ c.1 = 0)) :
    project boundaryFlip (a, b) = project boundaryFlip (c, boundaryFlip b) := by
  apply Quotient.sound
  rcases h with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · exact Relation.EqvGen.rel _ _ (Or.inl ⟨ha, hc, rfl⟩)
  · exact Relation.EqvGen.rel _ _ (Or.inr ⟨ha, hc, by cases b <;> rfl⟩)

private theorem mobiusBoundary_witness_of_seam {a c : Base}
    {x y : MobiusInterval}
    (hbase : (a.1 = 0 ∧ c.1 = 1) ∨ (a.1 = 1 ∧ c.1 = 0))
    (hends :
      (x = ⟨0, by constructor <;> norm_num⟩ ∧
        y = ⟨1, by constructor <;> norm_num⟩) ∨
      (x = ⟨1, by constructor <;> norm_num⟩ ∧
        y = ⟨0, by constructor <;> norm_num⟩)) :
    ∃ z : MobiusBoundary,
      boundaryToBand z = mobiusBandMk (a, x) ∧
        boundaryToBand z = mobiusBandMk (c, y) := by
  rcases hends with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · let z := project boundaryFlip (a, false)
    let z' := project boundaryFlip (c, true)
    have hzz' : z = z' := by
      simpa [z, boundaryFlip] using mobiusBoundary_seam_eq false hbase
    refine ⟨z, ?_, ?_⟩
    · change mobiusBandMk (a, boundaryEndpoint false) = mobiusBandMk (a, x)
      rw [hx]
      simp [boundaryEndpoint]
    · rw [hzz']
      change mobiusBandMk (c, boundaryEndpoint true) = mobiusBandMk (c, y)
      rw [hy]
      simp [boundaryEndpoint]
  · let z := project boundaryFlip (a, true)
    let z' := project boundaryFlip (c, false)
    have hzz' : z = z' := by
      simpa [z, boundaryFlip] using mobiusBoundary_seam_eq true hbase
    refine ⟨z, ?_, ?_⟩
    · change mobiusBandMk (a, boundaryEndpoint true) = mobiusBandMk (a, x)
      rw [hx]
      simp [boundaryEndpoint]
    · rw [hzz']
      change mobiusBandMk (c, boundaryEndpoint false) = mobiusBandMk (c, y)
      rw [hy]
      simp [boundaryEndpoint]

/-- Every circle point lies on at least one of the two parametrized arcs. -/
theorem mobiusArcs_cover (a : MomentumCircle) :
    (∃ x, mobiusLeftArc x = a) ∨ (∃ x, mobiusRightArc x = a) := by
  let r : ℝ := (AddCircle.equivIco (2 * Real.pi) (-Real.pi / 2) a).1
  have hrmem : -Real.pi / 2 ≤
      ((AddCircle.equivIco (2 * Real.pi) (-Real.pi / 2) a).1 : ℝ) ∧
      ((AddCircle.equivIco (2 * Real.pi) (-Real.pi / 2) a).1 : ℝ) <
        -Real.pi / 2 + 2 * Real.pi := by
    simpa only [Set.mem_Ico] using
      (AddCircle.equivIco (2 * Real.pi) (-Real.pi / 2) a).2
  have hupper : -Real.pi / 2 + 2 * Real.pi = 3 * Real.pi / 2 := by ring
  have hr : r ∈ Set.Ico (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    constructor
    · dsimp [r]
      linarith [hrmem.1]
    · dsimp [r]
      rw [← hupper]
      exact hrmem.2
  have hcoe : (r : MomentumCircle) = a := by
    simp [r]
  by_cases h : Real.pi / 2 ≤ r
  · let x : MobiusInterval := ⟨(r - Real.pi / 2) / Real.pi, by
      constructor
      · exact div_nonneg (by linarith [h]) (le_of_lt Real.pi_pos)
      · apply (div_le_one Real.pi_pos).2
        have hr' := hr.2
        linarith⟩
    left
    refine ⟨x, ?_⟩
    change ((Real.pi * x.1 + Real.pi / 2 : ℝ) : MomentumCircle) = a
    rw [← hcoe]
    apply congrArg (fun y : ℝ => (y : MomentumCircle))
    dsimp [x]
    field_simp
    ring
  · right
    let x : MobiusInterval := ⟨(Real.pi / 2 - r) / Real.pi, by
      constructor
      · exact div_nonneg (by linarith [hr.2]) (le_of_lt Real.pi_pos)
      · apply (div_le_one Real.pi_pos).2
        linarith [hr.1]⟩
    refine ⟨x, ?_⟩
    change ((Real.pi / 2 - Real.pi * x.1 : ℝ) : MomentumCircle) = a
    rw [← hcoe]
    apply congrArg (fun y : ℝ => (y : MomentumCircle))
    dsimp [x]
    field_simp
    ring

private theorem mobiusArc_respects_endpointStep
    (arc : MobiusInterval → MomentumCircle)
    (hflip : ∀ x, arc (mobiusFlip x) = -arc x)
    {p q : Base × MobiusInterval} (h : endpointStep mobiusFlip p q) :
    endpointStep fibreNeg (p.1, arc p.2) (q.1, arc q.2) := by
  rcases h with h | h
  · exact Or.inl ⟨h.1, h.2.1, by
      simpa [fibreNeg] using congrArg arc h.2.2 |>.trans (hflip p.2)⟩
  · exact Or.inr ⟨h.1, h.2.1, by
      simpa [fibreNeg] using (congrArg arc h.2.2).trans (hflip q.2)⟩

private theorem mobiusArc_respects
    (arc : MobiusInterval → MomentumCircle)
    (hflip : ∀ x, arc (mobiusFlip x) = -arc x)
    {p q : Base × MobiusInterval}
    (hpq : Relation.EqvGen (endpointStep mobiusFlip) p q) :
    canonicalMk (p.1, arc p.2) = canonicalMk (q.1, arc q.2) := by
  induction hpq with
  | rel p q h =>
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (mobiusArc_respects_endpointStep arc hflip h)
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem mobiusArc_quotient_lift_injective
    (arc : MobiusInterval → MomentumCircle)
    (hflip : ∀ x, arc (mobiusFlip x) = -arc x)
    (hinj : Function.Injective arc)
    (hdesc : ∀ {p q : Base × MobiusInterval},
      Relation.EqvGen (endpointStep mobiusFlip) p q →
        canonicalMk (p.1, arc p.2) = canonicalMk (q.1, arc q.2)) :
    Function.Injective
      (@Quotient.lift (Base × MobiusInterval) CanonicalKleinBottle
        (endpointSetoid mobiusFlip)
        (fun p => canonicalMk (p.1, arc p.2))
        (by intro p q hpq; exact hdesc hpq)) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro p q hxy
  change canonicalMk (p.1, arc p.2) = canonicalMk (q.1, arc q.2) at hxy
  have hrel : Relation.EqvGen (endpointStep fibreNeg)
      (p.1, arc p.2) (q.1, arc q.2) := Quotient.exact hxy
  have hfibre : Function.Involutive fibreNeg := by
    intro z
    simp [fibreNeg]
  rcases (endpointEqvGen_iff hfibre
      (p.1, arc p.2) (q.1, arc q.2)).mp hrel with heq | hstep
  · have hbase : p.1 = q.1 :=
      congrArg (fun z : Base × MomentumCircle => z.1) heq
    have harc : arc p.2 = arc q.2 :=
      congrArg (fun z : Base × MomentumCircle => z.2) heq
    have hfiber : p.2 = q.2 := hinj harc
    apply Quotient.sound
    have hpq : p = q := Prod.ext hbase hfiber
    subst q
    exact Relation.EqvGen.refl _
  · rcases hstep with hstep | hstep
    · have hfiber : q.2 = mobiusFlip p.2 :=
        hinj (hstep.2.2.trans (hflip p.2).symm)
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _
        (Or.inl ⟨hstep.1, hstep.2.1, hfiber⟩)
    · have hfiber : p.2 = mobiusFlip q.2 :=
        hinj (hstep.2.2.trans (hflip q.2).symm)
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _
        (Or.inr ⟨hstep.1, hstep.2.1, hfiber⟩)

private theorem continuous_mobiusLeftArc : Continuous mobiusLeftArc := by
  apply (AddCircle.continuous_mk' (2 * Real.pi)).comp
  exact (continuous_const.mul continuous_subtype_val).add continuous_const

private theorem continuous_mobiusRightArc : Continuous mobiusRightArc := by
  apply (AddCircle.continuous_mk' (2 * Real.pi)).comp
  exact continuous_const.sub (continuous_const.mul continuous_subtype_val)

/-- The left semicircle induces a continuous map from the Möbius-band quotient. -/
def mobiusLeftBandMap : MobiusBand → CanonicalKleinBottle :=
  @Quotient.lift (Base × MobiusInterval) CanonicalKleinBottle
    (endpointSetoid mobiusFlip)
    (fun p => canonicalMk (p.1, mobiusLeftArc p.2))
    (by
      intro p q hpq
      exact mobiusArc_respects mobiusLeftArc mobiusLeftArc_flip hpq)

theorem mobiusLeftBandMap_continuous : Continuous mobiusLeftBandMap := by
  change Continuous (Quotient.lift
    (fun p : Base × MobiusInterval => canonicalMk (p.1, mobiusLeftArc p.2)) _)
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_fst.prodMk (continuous_mobiusLeftArc.comp continuous_snd))

/-- The right semicircle induces a continuous map from the Möbius-band quotient. -/
def mobiusRightBandMap : MobiusBand → CanonicalKleinBottle :=
  @Quotient.lift (Base × MobiusInterval) CanonicalKleinBottle
    (endpointSetoid mobiusFlip)
    (fun p => canonicalMk (p.1, mobiusRightArc p.2))
    (by
      intro p q hpq
      exact mobiusArc_respects mobiusRightArc mobiusRightArc_flip hpq)

theorem mobiusLeftBandMap_injective : Function.Injective mobiusLeftBandMap := by
  exact mobiusArc_quotient_lift_injective mobiusLeftArc mobiusLeftArc_flip
    mobiusLeftArc_injective (mobiusArc_respects mobiusLeftArc mobiusLeftArc_flip)

theorem mobiusRightBandMap_injective : Function.Injective mobiusRightBandMap := by
  exact mobiusArc_quotient_lift_injective mobiusRightArc mobiusRightArc_flip
    mobiusRightArc_injective (mobiusArc_respects mobiusRightArc mobiusRightArc_flip)

private theorem mobiusLeftRightBandMap_eq_boundary_of_eq
    {x y : MobiusBand} (hxy : mobiusLeftBandMap x = mobiusRightBandMap y) :
    ∃ z : MobiusBoundary, boundaryToBand z = x ∧ boundaryToBand z = y := by
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro p q hpq
  change canonicalMk (p.1, mobiusLeftArc p.2) =
    canonicalMk (q.1, mobiusRightArc q.2) at hpq
  have hrel : Relation.EqvGen (endpointStep fibreNeg)
      (p.1, mobiusLeftArc p.2) (q.1, mobiusRightArc q.2) := Quotient.exact hpq
  have hfibre : Function.Involutive fibreNeg := by
    intro z
    simp [fibreNeg]
  rcases (endpointEqvGen_iff hfibre
      (p.1, mobiusLeftArc p.2) (q.1, mobiusRightArc q.2)).mp hrel with
    heq | hstep
  · have hbase : p.1 = q.1 :=
      congrArg (fun z : Base × MomentumCircle => z.1) heq
    have harc : mobiusLeftArc p.2 = mobiusRightArc q.2 :=
      congrArg (fun z : Base × MomentumCircle => z.2) heq
    rcases (mobiusLeftRightArc_eq_iff_boundary p.2 q.2).mp harc with
      ⟨hx, hy⟩ | ⟨hx, hy⟩
    · let z := project boundaryFlip (p.1, false)
      refine ⟨z, ?_, ?_⟩
      · change boundaryToBand (project boundaryFlip (p.1, false)) =
          mobiusBandMk (p.1, p.2)
        change mobiusBandMk (p.1, boundaryEndpoint false) =
          mobiusBandMk (p.1, p.2)
        rw [hx]
        simp [boundaryEndpoint]
      · change boundaryToBand (project boundaryFlip (p.1, false)) =
          mobiusBandMk (q.1, q.2)
        change mobiusBandMk (p.1, boundaryEndpoint false) =
          mobiusBandMk (q.1, q.2)
        rw [hbase, hy]
        simp [boundaryEndpoint]
    · let z := project boundaryFlip (p.1, true)
      refine ⟨z, ?_, ?_⟩
      · change boundaryToBand (project boundaryFlip (p.1, true)) =
          mobiusBandMk (p.1, p.2)
        change mobiusBandMk (p.1, boundaryEndpoint true) =
          mobiusBandMk (p.1, p.2)
        rw [hx]
        simp [boundaryEndpoint]
      · change boundaryToBand (project boundaryFlip (p.1, true)) =
          mobiusBandMk (q.1, q.2)
        change mobiusBandMk (p.1, boundaryEndpoint true) =
          mobiusBandMk (q.1, q.2)
        rw [hbase, hy]
        simp [boundaryEndpoint]
  · rcases hstep with hstep | hstep
    · have harc : mobiusLeftArc p.2 = -mobiusRightArc q.2 := by
        have hright : mobiusRightArc q.2 = -mobiusLeftArc p.2 := by
          simpa [fibreNeg] using hstep.2.2
        calc
          mobiusLeftArc p.2 = -(-mobiusLeftArc p.2) := by simp
          _ = -mobiusRightArc q.2 := by rw [← hright]
      exact mobiusBoundary_witness_of_seam
        (Or.inl ⟨hstep.1, hstep.2.1⟩)
        ((mobiusLeftRightArc_eq_flip_iff_boundary p.2 q.2).mp harc)
    · have harc : mobiusLeftArc p.2 = -mobiusRightArc q.2 := by
        simpa [fibreNeg] using hstep.2.2
      exact mobiusBoundary_witness_of_seam
        (Or.inr ⟨hstep.1, hstep.2.1⟩)
        ((mobiusLeftRightArc_eq_flip_iff_boundary p.2 q.2).mp harc)

theorem mobiusRightBandMap_continuous : Continuous mobiusRightBandMap := by
  change Continuous (Quotient.lift
    (fun p : Base × MobiusInterval => canonicalMk (p.1, mobiusRightArc p.2)) _)
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_fst.prodMk (continuous_mobiusRightArc.comp continuous_snd))

theorem mobiusBandMaps_agree_boundary :
    boundaryToBandHom ≫
        TopCat.ofHom ⟨mobiusLeftBandMap, mobiusLeftBandMap_continuous⟩ =
      boundaryToBandHom ≫
        TopCat.ofHom ⟨mobiusRightBandMap, mobiusRightBandMap_continuous⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro b
  change mobiusLeftBandMap (boundaryToBand b) =
    mobiusRightBandMap (boundaryToBand b)
  refine Quotient.inductionOn b ?_
  intro p
  change canonicalMk (p.1, mobiusLeftArc (boundaryEndpoint p.2)) =
    canonicalMk (p.1, mobiusRightArc (boundaryEndpoint p.2))
  cases p.2
  · simp [boundaryEndpoint, mobiusLeftArc, mobiusRightArc]
  · simpa [boundaryEndpoint] using
      congrArg (fun z => canonicalMk (p.1, z)) mobiusLeftArc_one_eq_right

/-- The two semicircle maps descend uniquely to the native boundary pushout. -/
def mobiusGluedToCanonical : MobiusGluedObj ⟶ TopCat.of CanonicalKleinBottle :=
  pushout.desc
    (TopCat.ofHom ⟨mobiusLeftBandMap, mobiusLeftBandMap_continuous⟩)
    (TopCat.ofHom ⟨mobiusRightBandMap, mobiusRightBandMap_continuous⟩)
    mobiusBandMaps_agree_boundary

@[simp] theorem mobiusGluedInl_comp_mobiusGluedToCanonical :
    mobiusGluedInl ≫ mobiusGluedToCanonical =
      TopCat.ofHom ⟨mobiusLeftBandMap, mobiusLeftBandMap_continuous⟩ := by
  exact pushout.inl_desc _ _ mobiusBandMaps_agree_boundary

@[simp] theorem mobiusGluedInr_comp_mobiusGluedToCanonical :
    mobiusGluedInr ≫ mobiusGluedToCanonical =
      TopCat.ofHom ⟨mobiusRightBandMap, mobiusRightBandMap_continuous⟩ := by
  exact pushout.inr_desc _ _ mobiusBandMaps_agree_boundary

theorem mobiusGluedToCanonical_inl_apply (p : Base × MobiusInterval) :
    mobiusGluedToCanonical.hom
        (mobiusGluedInl.hom (mobiusBandMk p)) =
      canonicalMk (p.1, mobiusLeftArc p.2) := by
  have h := congrArg
    (fun f : MobiusBandObj ⟶ TopCat.of CanonicalKleinBottle =>
      f.hom (mobiusBandMk p)) mobiusGluedInl_comp_mobiusGluedToCanonical
  exact h

theorem mobiusGluedToCanonical_inr_apply (p : Base × MobiusInterval) :
    mobiusGluedToCanonical.hom
        (mobiusGluedInr.hom (mobiusBandMk p)) =
      canonicalMk (p.1, mobiusRightArc p.2) := by
  have h := congrArg
    (fun f : MobiusBandObj ⟶ TopCat.of CanonicalKleinBottle =>
      f.hom (mobiusBandMk p)) mobiusGluedInr_comp_mobiusGluedToCanonical
  exact h

private theorem mobiusGluedToCanonical_inl_stage (x : MobiusBand) :
    mobiusGluedToCanonical.hom (mobiusGluedInl.hom x) = mobiusLeftBandMap x := by
  exact ConcreteCategory.congr_hom
    mobiusGluedInl_comp_mobiusGluedToCanonical x

private theorem mobiusGluedToCanonical_inr_stage (x : MobiusBand) :
    mobiusGluedToCanonical.hom (mobiusGluedInr.hom x) = mobiusRightBandMap x := by
  exact ConcreteCategory.congr_hom
    mobiusGluedInr_comp_mobiusGluedToCanonical x

private theorem mobiusGlued_underlying_isPushout :
    IsPushout ((forget TopCat).map boundaryToBandHom)
      ((forget TopCat).map boundaryToBandHom)
      ((forget TopCat).map mobiusGluedInl)
      ((forget TopCat).map mobiusGluedInr) := by
  exact IsPushout.of_isColimit_cocone
    (isColimitOfPreserves (forget TopCat)
      (pushout.isColimit boundaryToBandHom boundaryToBandHom))

private theorem mobiusGlued_exists_band_rep (x : MobiusGluedObj) :
    (∃ a : MobiusBand, mobiusGluedInl.hom a = x) ∨
      ∃ b : MobiusBand, mobiusGluedInr.hom b = x := by
  exact Types.eq_or_eq_of_isPushout mobiusGlued_underlying_isPushout x

private theorem mobiusGlued_inl_eq_inr_iff (a b : MobiusBand) :
    mobiusGluedInl.hom a = mobiusGluedInr.hom b ↔
      ∃ z : MobiusBoundary, boundaryToBand z = a ∧ boundaryToBand z = b := by
  exact Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    mobiusGlued_underlying_isPushout.isColimit boundaryToBand_injective a b

theorem mobiusGluedToCanonical_injective :
    Function.Injective mobiusGluedToCanonical.hom := by
  intro x y hxy
  rcases mobiusGlued_exists_band_rep x with ⟨a, hax⟩ | ⟨a, hax⟩
  · rcases mobiusGlued_exists_band_rep y with ⟨b, hby⟩ | ⟨b, hby⟩
    · have hab : mobiusLeftBandMap a = mobiusLeftBandMap b := by
        rw [← mobiusGluedToCanonical_inl_stage a,
          ← mobiusGluedToCanonical_inl_stage b, hax, hby]
        exact hxy
      have hab' : a = b := mobiusLeftBandMap_injective hab
      calc
        x = mobiusGluedInl.hom a := hax.symm
        _ = mobiusGluedInl.hom b := congrArg mobiusGluedInl.hom hab'
        _ = y := hby
    · have hab : mobiusLeftBandMap a = mobiusRightBandMap b := by
        rw [← mobiusGluedToCanonical_inl_stage a,
          ← mobiusGluedToCanonical_inr_stage b, hax, hby]
        exact hxy
      obtain ⟨z, haz, hbz⟩ := mobiusLeftRightBandMap_eq_boundary_of_eq hab
      have hpush := (mobiusGlued_inl_eq_inr_iff a b).2 ⟨z, haz, hbz⟩
      calc
        x = mobiusGluedInl.hom a := hax.symm
        _ = mobiusGluedInr.hom b := hpush
        _ = y := hby
  · rcases mobiusGlued_exists_band_rep y with ⟨b, hby⟩ | ⟨b, hby⟩
    · have hab : mobiusRightBandMap a = mobiusLeftBandMap b := by
        rw [← mobiusGluedToCanonical_inr_stage a,
          ← mobiusGluedToCanonical_inl_stage b, hax, hby]
        exact hxy
      obtain ⟨z, hbz, haz⟩ :=
        mobiusLeftRightBandMap_eq_boundary_of_eq hab.symm
      have hpush := (mobiusGlued_inl_eq_inr_iff b a).2 ⟨z, hbz, haz⟩
      calc
        x = mobiusGluedInr.hom a := hax.symm
        _ = mobiusGluedInl.hom b := hpush.symm
        _ = y := hby
    · have hab : mobiusRightBandMap a = mobiusRightBandMap b := by
        rw [← mobiusGluedToCanonical_inr_stage a,
          ← mobiusGluedToCanonical_inr_stage b, hax, hby]
        exact hxy
      have hab' : a = b := mobiusRightBandMap_injective hab
      calc
        x = mobiusGluedInr.hom a := hax.symm
        _ = mobiusGluedInr.hom b := congrArg mobiusGluedInr.hom hab'
        _ = y := hby

theorem mobiusGlued_compactSpace : CompactSpace MobiusGluedObj := by
  let f : MobiusBand ⊕ MobiusBand → MobiusGluedObj :=
    Sum.elim mobiusGluedInl.hom mobiusGluedInr.hom
  have hf : Continuous f := by
    apply continuous_sumElim.mpr
    exact ⟨mobiusGluedInl.hom.continuous, mobiusGluedInr.hom.continuous⟩
  have hsurj : Function.Surjective f := by
    intro x
    rcases mobiusGlued_exists_band_rep x with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨Sum.inl a, ha⟩
    · exact ⟨Sum.inr b, hb⟩
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hsurj]
  exact isCompact_range hf

/-- The map induced by the two semicircles reaches every point of the
canonical mapping-torus Klein bottle. -/
theorem mobiusGluedToCanonical_surjective :
    Function.Surjective mobiusGluedToCanonical.hom := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  rcases mobiusArcs_cover p.2 with ⟨x, hx⟩ | ⟨x, hx⟩
  · refine ⟨mobiusGluedInl.hom (mobiusBandMk (p.1, x)), ?_⟩
    rw [mobiusGluedToCanonical_inl_apply, hx]
    change canonicalMk p = canonicalMk p
    rfl
  · refine ⟨mobiusGluedInr.hom (mobiusBandMk (p.1, x)), ?_⟩
    rw [mobiusGluedToCanonical_inr_apply, hx]
    change canonicalMk p = canonicalMk p
    rfl
end InfoGeometry.Topology.KleinBottleCanonicalCarrier

end noncomputable section
