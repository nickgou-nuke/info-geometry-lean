/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCanonicalCarrier
import InfoGeometry.Topology.KleinBottleOrbitQuotient

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

end InfoGeometry.Topology.KleinBottleMappingTorusOrbitBridge
end noncomputable section
