/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCanonicalCarrier
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section
namespace InfoGeometry.Topology.KleinBottleMappingTorusOrbitBridge

open KleinBrillouinBase
open KleinBottleCanonicalCarrier
open KleinBottleOrbitQuotient
open CompactMappingTorus

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The strip-to-torus representative map before quotienting. -/
def stripToOrbitRepresentative (p : Base × MomentumCircle) :
    BrillouinTorus :=
  (((Real.pi * p.1.1 : ℝ) : MomentumCircle), p.2)

theorem stripToOrbitRepresentative_continuous :
    Continuous stripToOrbitRepresentative := by
  apply Continuous.prodMk
  · apply (AddCircle.continuous_mk' (2 * Real.pi)).comp
    exact continuous_const.mul
      (continuous_subtype_val.comp continuous_fst)
  · exact continuous_snd

theorem stripToOrbitRepresentative_endpointStep
    {p q : Base × MomentumCircle}
    (h : endpointStep fibreNeg p q) :
    quotientMap (stripToOrbitRepresentative p) =
      quotientMap (stripToOrbitRepresentative q) := by
  rcases h with h | h
  · rcases h with ⟨hp, hq, hfiber⟩
    change quotientMap (((Real.pi * p.1.1 : ℝ) : MomentumCircle), p.2) =
      quotientMap (((Real.pi * q.1.1 : ℝ) : MomentumCircle), q.2)
    rw [hp, hq, hfiber]
    norm_num
    change quotientMap ((0 : MomentumCircle), p.2) =
      quotientMap ((Real.pi : MomentumCircle), -p.2)
    simpa [torusGlide] using (quotientMap_glide (0, p.2)).symm
  · rcases h with ⟨hp, hq, hfiber⟩
    change quotientMap (((Real.pi * p.1.1 : ℝ) : MomentumCircle), p.2) =
      quotientMap (((Real.pi * q.1.1 : ℝ) : MomentumCircle), q.2)
    rw [hp, hq, hfiber]
    norm_num
    change quotientMap ((Real.pi : MomentumCircle), -q.2) =
      quotientMap ((0 : MomentumCircle), q.2)
    simpa [torusGlide] using quotientMap_glide (0, q.2)

def canonicalToOrbit : CanonicalKleinBottle → KleinBrillouinQuotient :=
  @Quotient.lift (Base × MomentumCircle) KleinBrillouinQuotient
    (endpointSetoid fibreNeg)
    (fun p => quotientMap (stripToOrbitRepresentative p))
    (by
      intro p q hpq
      induction hpq with
      | rel p q h => exact stripToOrbitRepresentative_endpointStep h
      | refl p => rfl
      | symm p q _ ih => exact ih.symm
      | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem canonicalToOrbit_continuous :
    Continuous canonicalToOrbit := by
  exact continuous_quot_lift
    (by
      intro p q hpq
      induction hpq with
      | rel p q h => exact stripToOrbitRepresentative_endpointStep h
      | refl p => rfl
      | symm p q _ ih => exact ih.symm
      | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
    (quotientMap_continuous.comp stripToOrbitRepresentative_continuous)

theorem canonicalToOrbit_surjective :
    Function.Surjective canonicalToOrbit := by
  intro q
  refine Quotient.inductionOn q ?_
  rintro ⟨a, b⟩
  let r : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 a).1
  have hr : r ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    by simpa [r] using (AddCircle.equivIco (2 * Real.pi) 0 a).2
  have hcoe : (r : MomentumCircle) = a :=
    AddCircle.coe_equivIco
  by_cases h : r ≤ Real.pi
  · let t : Base := ⟨r / Real.pi, by
      constructor
      · have hpi : 0 < Real.pi := Real.pi_pos
        have hr0 : 0 ≤ r := hr.1
        exact div_nonneg hr0 (le_of_lt hpi)
      · have hpi : 0 < Real.pi := Real.pi_pos
        exact (div_le_one hpi).2 h⟩
    refine ⟨canonicalMk (t, b), ?_⟩
    change quotientMap
      ((((Real.pi * (r / Real.pi) : ℝ) : MomentumCircle), b)) = quotientMap (a, b)
    have hreal : Real.pi * (r / Real.pi) = r := by
      field_simp
    rw [hreal, hcoe]
  · have hpi : Real.pi < r := lt_of_not_ge h
    let t : Base := ⟨(r - Real.pi) / Real.pi, by
      constructor
      · exact div_nonneg (by linarith [hpi]) (le_of_lt Real.pi_pos)
      · apply (div_le_one Real.pi_pos).2
        linarith [hr.2]
      ⟩
    refine ⟨canonicalMk (t, -b), ?_⟩
    change quotientMap (stripToOrbitRepresentative (t, -b)) = quotientMap (a, b)
    rw [← quotientMap_glide (a, b)]
    congr 1
    apply Prod.ext
    · dsimp [stripToOrbitRepresentative, t, torusGlide]
      have hreal : Real.pi * ((r - Real.pi) / Real.pi) = r - Real.pi := by
        field_simp
      rw [hreal, sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg]
      rw [hcoe]
      have hpi0 : (Real.pi : MomentumCircle) + Real.pi = 0 :=
        pi_add_pi_eq_zero
      have hneg : (-Real.pi : MomentumCircle) = Real.pi :=
        (eq_neg_of_add_eq_zero_left hpi0).symm
      simp [hneg, add_assoc, hpi0]
    · rfl

private theorem strip_angle_mem_Ico (t : Base) :
    Real.pi * t.1 ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  constructor
  · exact mul_nonneg (le_of_lt Real.pi_pos) t.2.1
  · have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [t.2.2]

private theorem strip_angle_shift_mem_Ico {t : Base} (ht : t.1 < 1) :
    Real.pi * t.1 + Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  constructor
  · have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [t.2.1]
  · have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith

theorem canonicalToOrbit_injective :
    Function.Injective canonicalToOrbit := by
  intro q₁ q₂ hq
  revert q₂ hq
  refine Quotient.inductionOn q₁ ?_
  intro p q₂ hq
  revert hq
  refine Quotient.inductionOn q₂ ?_
  intro q hq
  change @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg) p =
    @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg) q
  change quotientMap (stripToOrbitRepresentative p) =
    quotientMap (stripToOrbitRepresentative q) at hq
  rcases (quotientMap_eq_iff _ _).mp hq with hsame | hglide
  · have hfirst := (congrArg Prod.fst hsame).symm
    have hangle : Real.pi * p.1.1 = Real.pi * q.1.1 := by
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2 * Real.pi) (a := 0)
        (by simpa using strip_angle_mem_Ico p.1)
        (by simpa using strip_angle_mem_Ico q.1)).mp hfirst
    have hbase : p.1 = q.1 := by
      apply Subtype.ext
      nlinarith [Real.pi_pos]
    have hfiber : p.2 = q.2 := (congrArg Prod.snd hsame).symm
    have hpq : p = q := Prod.ext hbase hfiber
    subst hpq
    rfl
  · have hfirst := congrArg Prod.fst hglide
    have hsecond := congrArg Prod.snd hglide
    by_cases hp : p.1.1 = 1
    · have hqzero : Real.pi * q.1.1 = 0 := by
        have hpi0 : (Real.pi : MomentumCircle) + Real.pi = 0 :=
          pi_add_pi_eq_zero
        have hz : ((Real.pi * q.1.1 : ℝ) : MomentumCircle) = 0 := by
          simpa [stripToOrbitRepresentative, torusGlide, hp, hpi0] using hfirst
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2 * Real.pi) (a := 0)
          (by simpa using strip_angle_mem_Ico q.1)
          (by constructor <;> positivity)).mp hz
      have hqbase : q.1.1 = 0 := by
        nlinarith [Real.pi_pos]
      have hstep : endpointStep fibreNeg p q := by
        right
        refine ⟨hp, ?_, ?_⟩
        · exact hqbase
        · simpa [stripToOrbitRepresentative, torusGlide, fibreNeg] using
            (congrArg Neg.neg hsecond).symm
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ hstep
    · have hp_lt : p.1.1 < 1 := lt_of_le_of_ne p.1.2.2 hp
      have hangle : Real.pi * q.1.1 = Real.pi * p.1.1 + Real.pi := by
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2 * Real.pi) (a := 0)
          (by simpa using strip_angle_mem_Ico q.1)
          (by simpa using strip_angle_shift_mem_Ico hp_lt)).mp hfirst
      have hpbase : p.1.1 = 0 := by
        nlinarith [Real.pi_pos, q.1.2.1, q.1.2.2, p.1.2.1]
      have hqbase : q.1.1 = 1 := by
        nlinarith [Real.pi_pos, hangle]
      have hstep : endpointStep fibreNeg p q := by
        left
        refine ⟨?_, ?_, ?_⟩
        · exact hpbase
        · exact hqbase
        · simpa [stripToOrbitRepresentative, torusGlide, fibreNeg] using hsecond
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ hstep

theorem canonicalToOrbit_endpoint (x : MomentumCircle) :
    canonicalToOrbit (canonicalMk (⟨0, by constructor <;> norm_num⟩, x)) =
      canonicalToOrbit
        (canonicalMk (⟨1, by constructor <;> norm_num⟩, fibreNeg x)) := by
  change quotientMap (stripToOrbitRepresentative
      (⟨0, by constructor <;> norm_num⟩, x)) =
    quotientMap (stripToOrbitRepresentative
      (⟨1, by constructor <;> norm_num⟩, fibreNeg x))
  apply stripToOrbitRepresentative_endpointStep
  exact Or.inl ⟨rfl, rfl, rfl⟩

/-! The literal glide quotient is also a finite-group orbit quotient.  This
identification supplies the separation theorem needed to upgrade the
continuous bijection above to a homeomorphism. -/

abbrev finiteGlideGroup := Multiplicative (ZMod 2)

theorem finiteGlideGroup_cases (g : finiteGlideGroup) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  have hv : (Multiplicative.toAdd g).val < 2 := (Multiplicative.toAdd g).isLt
  have hz : (Multiplicative.toAdd g).val = 0 ∨ (Multiplicative.toAdd g).val = 1 := by omega
  rcases hz with hz | hz
  · left
    apply (Multiplicative.toAdd).injective
    apply (ZMod.val_eq_zero _).mp
    exact hz
  · right
    apply (Multiplicative.toAdd).injective
    apply ((ZMod.val_eq_one (by decide) _)).mp
    omega

theorem finiteGlideGroup_one_ne_nontrivial :
    (1 : finiteGlideGroup) ≠ Multiplicative.ofAdd 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  norm_num at h'

theorem finiteGlideGroup_nontrivial_mul_nontrivial :
    Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 = (1 : finiteGlideGroup) := by
  apply (Multiplicative.toAdd).injective
  decide

def finiteGlideAction : finiteGlideGroup → BrillouinTorus → BrillouinTorus := fun g x =>
  if g = Multiplicative.ofAdd 1 then torusGlide x else x

instance : SMul finiteGlideGroup BrillouinTorus := ⟨finiteGlideAction⟩

instance : MulAction finiteGlideGroup BrillouinTorus where
  one_smul x := by
    change finiteGlideAction (1 : finiteGlideGroup) x = x
    simp [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial]
  mul_smul a b x := by
    change finiteGlideAction (a * b) x = finiteGlideAction a (finiteGlideAction b x)
    rcases finiteGlideGroup_cases a with rfl | rfl <;>
      rcases finiteGlideGroup_cases b with rfl | rfl
    · simp [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial]
    · simp [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial]
    · simp [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial]
    · rw [finiteGlideGroup_nontrivial_mul_nontrivial]
      simp [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial]
      rw [torusGlide_involutive]

instance : ContinuousConstSMul finiteGlideGroup BrillouinTorus where
  continuous_const_smul g := by
    rcases finiteGlideGroup_cases g with rfl | rfl
    · change Continuous (fun x : BrillouinTorus => x)
      exact continuous_id
    · change Continuous torusGlide
      exact torusGlide_continuous

abbrev finiteGlideQuotient :=
  Quotient (MulAction.orbitRel finiteGlideGroup BrillouinTorus)

theorem finiteGlideOrbitRel_iff (x y : BrillouinTorus) :
    (MulAction.orbitRel finiteGlideGroup BrillouinTorus) x y ↔ glideSetoid x y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    rcases finiteGlideGroup_cases g with rfl | rfl
    · left
      change finiteGlideAction (1 : finiteGlideGroup) y = x at hg
      simpa [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial] using hg
    · right
      change finiteGlideAction (Multiplicative.ofAdd 1) y = x at hg
      rw [finiteGlideAction, if_pos rfl] at hg
      have h' := congrArg torusGlide hg
      calc
        y = torusGlide (torusGlide y) := (torusGlide_involutive y).symm
        _ = torusGlide x := h'
  · intro h
    rcases h with h | h
    · exact ⟨1, by
        change finiteGlideAction (1 : finiteGlideGroup) y = x
        simpa [finiteGlideAction, finiteGlideGroup_one_ne_nontrivial] using h⟩
    · exact ⟨Multiplicative.ofAdd 1, by
        change finiteGlideAction (Multiplicative.ofAdd 1) y = x
        rw [finiteGlideAction, if_pos rfl]
        have h' := congrArg torusGlide h
        calc
          torusGlide y = torusGlide (torusGlide x) := h'
          _ = x := torusGlide_involutive x⟩

def finiteGlideOrbitMap (x : BrillouinTorus) : finiteGlideQuotient :=
  @Quotient.mk' BrillouinTorus
    (MulAction.orbitRel finiteGlideGroup BrillouinTorus) x

theorem finiteGlideOrbitMap_continuous :
    Continuous finiteGlideOrbitMap := by
  change Continuous (@Quotient.mk' BrillouinTorus
    (MulAction.orbitRel finiteGlideGroup BrillouinTorus))
  exact continuous_quot_mk

def finiteGlideToLiteral : finiteGlideQuotient → KleinBrillouinQuotient :=
  Quotient.lift quotientMap (by
    intro x y hxy
    exact Quotient.sound ((finiteGlideOrbitRel_iff x y).mp hxy))

theorem finiteGlideToLiteral_continuous :
    Continuous finiteGlideToLiteral := by
  exact continuous_quot_lift
    (fun x y hxy => Quotient.sound ((finiteGlideOrbitRel_iff x y).mp hxy))
    quotientMap_continuous

def literalToFiniteGlide : KleinBrillouinQuotient → finiteGlideQuotient :=
  Quotient.lift finiteGlideOrbitMap (by
    intro x y hxy
    exact Quotient.sound ((finiteGlideOrbitRel_iff x y).mpr hxy))

theorem literalToFiniteGlide_continuous :
    Continuous literalToFiniteGlide := by
  exact continuous_quot_lift
    (fun x y hxy => Quotient.sound ((finiteGlideOrbitRel_iff x y).mpr hxy))
    finiteGlideOrbitMap_continuous

theorem finiteGlideToLiteral_leftInverse :
    Function.LeftInverse literalToFiniteGlide finiteGlideToLiteral := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  change finiteGlideOrbitMap x = finiteGlideOrbitMap x
  rfl

theorem finiteGlideToLiteral_rightInverse :
    Function.RightInverse literalToFiniteGlide finiteGlideToLiteral := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  change quotientMap x = quotientMap x
  rfl

def finiteGlideToLiteralHomeomorph :
    finiteGlideQuotient ≃ₜ KleinBrillouinQuotient :=
  { toEquiv :=
      { toFun := finiteGlideToLiteral
        invFun := literalToFiniteGlide
        left_inv := finiteGlideToLiteral_leftInverse
        right_inv := finiteGlideToLiteral_rightInverse }
    continuous_toFun := finiteGlideToLiteral_continuous
    continuous_invFun := literalToFiniteGlide_continuous }

instance literalQuotient_t2 : T2Space KleinBrillouinQuotient :=
  finiteGlideToLiteralHomeomorph.t2Space

theorem canonicalToOrbit_isQuotientMap :
    Topology.IsQuotientMap canonicalToOrbit :=
  Topology.IsQuotientMap.of_surjective_continuous
    canonicalToOrbit_surjective canonicalToOrbit_continuous

def canonicalToOrbitHomeomorph :
    CanonicalKleinBottle ≃ₜ KleinBrillouinQuotient := by
  let e : CanonicalKleinBottle ≃ KleinBrillouinQuotient :=
    Equiv.ofBijective canonicalToOrbit
      ⟨canonicalToOrbit_injective, canonicalToOrbit_surjective⟩
  have hcomp : e.symm ∘ canonicalToOrbit = fun x => x := by
    funext x
    exact e.left_inv x
  refine
    { toEquiv := e
      continuous_toFun := canonicalToOrbit_continuous
      continuous_invFun := ?_ }
  apply (canonicalToOrbit_isQuotientMap.continuous_iff).2
  change Continuous (e.symm ∘ canonicalToOrbit)
  rw [hcomp]
  exact continuous_id

end InfoGeometry.Topology.KleinBottleMappingTorusOrbitBridge
end noncomputable section
