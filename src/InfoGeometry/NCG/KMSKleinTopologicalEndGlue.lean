/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.KMSStripKleinMonodromy
import InfoGeometry.Topology.KleinBottleCanonicalCarrier

/-!
# KMS logistic ends in the canonical Klein mapping torus

The logistic coordinate has two endpoint limits.  The compact mapping-torus
quotient identifies these endpoints together with fibre negation.  This module
states that transition on the existing carrier and transports the two limits
through its quotient projection.
-/

noncomputable section

namespace InfoGeometry.NCG.KMSKleinTopologicalEndGlue

open Filter
open InfoGeometry.NCG.KMSStripKleinMonodromy
open InfoGeometry.Topology.KleinBottleCanonicalCarrier
open InfoGeometry.Topology.CompactMappingTorus
open KleinBrillouinBase

/-- The logistic coordinate, viewed as a point of the compact mapping-torus base. -/
def compactifiedBase (t : ℝ) : Base :=
  ⟨compactifiedTime t,
    (compactifiedTime_mem_unitInterval t).1.le,
    (compactifiedTime_mem_unitInterval t).2.le⟩

/-- The KMS real-time path in the canonical Klein mapping-torus carrier. -/
def compactifiedKleinPath (x : KleinBrillouinBase.MomentumCircle) (t : ℝ) : CanonicalKleinBottle :=
  canonicalMk (compactifiedBase t, x)

private def baseZero : Base := ⟨0, by norm_num, by norm_num⟩
private def baseOne : Base := ⟨1, by norm_num, by norm_num⟩

/-- The negative-time end converges in the actual quotient topology to the left
endpoint represented by the fibre element `x`. -/
theorem compactifiedKleinPath_tendsto_atBot (x : KleinBrillouinBase.MomentumCircle) :
    Tendsto (compactifiedKleinPath x) atBot (nhds (canonicalMk (baseZero, x))) := by
  have hbase : Tendsto compactifiedBase atBot (nhds baseZero) := by
    apply tendsto_subtype_rng.2
    simpa [compactifiedBase, baseZero] using tendsto_compactifiedTime_atBot
  have hsource : Tendsto (fun t : ℝ => (compactifiedBase t, x)) atBot
      (nhds (baseZero, x)) := by
    simpa only [nhds_prod_eq] using
      hbase.prodMk (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atBot (nhds x))
  have hquotient : Continuous canonicalMk := continuous_quotient_mk'
  exact hquotient.continuousAt.tendsto.comp hsource

/-- The positive-time end converges in the actual quotient topology to the right
endpoint represented by the same fibre element `x`. -/
theorem compactifiedKleinPath_tendsto_atTop (x : KleinBrillouinBase.MomentumCircle) :
    Tendsto (compactifiedKleinPath x) atTop (nhds (canonicalMk (baseOne, x))) := by
  have hbase : Tendsto compactifiedBase atTop (nhds baseOne) := by
    apply tendsto_subtype_rng.2
    simpa [compactifiedBase, baseOne] using tendsto_compactifiedTime_atTop
  have hsource : Tendsto (fun t : ℝ => (compactifiedBase t, x)) atTop
      (nhds (baseOne, x)) := by
    simpa only [nhds_prod_eq] using
      hbase.prodMk (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atTop (nhds x))
  have hquotient : Continuous canonicalMk := continuous_quotient_mk'
  exact hquotient.continuousAt.tendsto.comp hsource

/-- At the seam, the right endpoint with fibre `x` is the left endpoint with
fibre negated.  This is the canonical mapping-torus endpoint relation. -/
theorem kmsKlein_endpoint_transition (x : KleinBrillouinBase.MomentumCircle) :
    canonicalMk (baseZero, x) = canonicalMk (baseOne, fibreNeg x) := by
  exact canonical_endpoint x

/-- The asymptotic limits of the logistic path are exchanged by the Klein
fibre transition. -/
theorem kmsKlein_end_limits_glue (x : KleinBrillouinBase.MomentumCircle) :
    canonicalMk (baseZero, x) = canonicalMk (baseOne, fibreNeg x) ∧
    canonicalMk (baseOne, x) = canonicalMk (baseZero, fibreNeg x) := by
  constructor
  · exact kmsKlein_endpoint_transition x
  · symm
    simpa [fibreNeg] using kmsKlein_endpoint_transition (fibreNeg x)

private theorem baseReflection_endpointStep {p q : Base × MomentumCircle}
    (h : endpointStep fibreNeg p q) :
    endpointStep fibreNeg (mobiusFlip p.1, p.2) (mobiusFlip q.1, q.2) := by
  rcases h with h | h
  · right
    refine ⟨?_, ?_, ?_⟩
    · change 1 - p.1.1 = 1
      rw [h.1]
      norm_num
    · change 1 - q.1.1 = 0
      rw [h.2.1]
      norm_num
    · simpa [fibreNeg] using (congrArg fibreNeg h.2.2).symm
  · left
    refine ⟨?_, ?_, ?_⟩
    · change 1 - p.1.1 = 0
      rw [h.1]
      norm_num
    · change 1 - q.1.1 = 1
      rw [h.2.1]
      norm_num
    · simpa [fibreNeg] using (congrArg fibreNeg h.2.2).symm

private theorem baseReflection_respects : ∀ {p q : Base × MomentumCircle},
    Relation.EqvGen (endpointStep fibreNeg) p q →
      Relation.EqvGen (endpointStep fibreNeg)
        (mobiusFlip p.1, p.2) (mobiusFlip q.1, q.2) := by
  intro p q h
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ (baseReflection_endpointStep h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Reflection of the compactified interval descends to the existing Klein
mapping-torus carrier. The endpoint relation is preserved because the base
reflection exchanges the two ends of the twisted seam. -/
def canonicalBaseReflection : CanonicalKleinBottle → CanonicalKleinBottle :=
  @Quotient.lift (Base × MomentumCircle) CanonicalKleinBottle
    (endpointSetoid fibreNeg)
    (fun p => canonicalMk (mobiusFlip p.1, p.2))
    (by
      intro p q h
      exact Quotient.sound (baseReflection_respects h))

/-- The interval reflection is an involution on the canonical Klein carrier. -/
theorem canonicalBaseReflection_involutive (q : CanonicalKleinBottle) :
    canonicalBaseReflection (canonicalBaseReflection q) = q := by
  refine Quotient.inductionOn q ?_
  intro p
  change project fibreNeg (mobiusFlip (mobiusFlip p.1), p.2) = project fibreNeg p
  rw [mobiusFlip_involutive]

/-- Time reversal on the KMS axis becomes the base-reflection involution of the
Klein carrier. -/
theorem compactifiedKleinPath_timeReflection
    (x : KleinBrillouinBase.MomentumCircle) (t : ℝ) :
    canonicalBaseReflection (compactifiedKleinPath x t) =
      compactifiedKleinPath x (-t) := by
  change project fibreNeg (mobiusFlip (compactifiedBase t), x) =
    project fibreNeg (compactifiedBase (-t), x)
  apply congrArg (project fibreNeg)
  apply Prod.ext
  · apply Subtype.ext
    simp [compactifiedKleinPath, compactifiedBase, mobiusFlip, compactifiedTime_neg]
  · rfl

/-- The logistic coordinate is injective. -/
private theorem compactifiedTime_injective : Function.Injective compactifiedTime := by
  intro t s h
  have hcross : Real.exp t * (1 + Real.exp s) =
      Real.exp s * (1 + Real.exp t) := by
    unfold compactifiedTime at h
    exact (div_eq_div_iff (by positivity) (by positivity)).mp h
  have hexp : Real.exp t = Real.exp s := by
    calc
      Real.exp t = Real.exp t * (1 + Real.exp s) - Real.exp t * Real.exp s := by ring
      _ = Real.exp s * (1 + Real.exp t) - Real.exp t * Real.exp s := by rw [hcross]
      _ = Real.exp s := by ring
  exact Real.exp_injective hexp

/-- The compactified KMS path has no accidental identifications in the Klein
quotient: its points lie in the open base interval, away from the glued ends. -/
private theorem compactifiedKleinPath_injective (x : KleinBrillouinBase.MomentumCircle) :
    Function.Injective (compactifiedKleinPath x) := by
  intro t s h
  change project fibreNeg (compactifiedBase t, x) =
    project fibreNeg (compactifiedBase s, x) at h
  have hfibre : Function.Involutive fibreNeg := by
    intro y
    simp [fibreNeg]
  have hrel : Relation.EqvGen (endpointStep fibreNeg)
      (compactifiedBase t, x) (compactifiedBase s, x) := Quotient.exact h
  rcases (endpointEqvGen_iff hfibre
      (compactifiedBase t, x) (compactifiedBase s, x)).mp hrel with heq | hstep
  · have hbase := congrArg (fun z : Base × KleinBrillouinBase.MomentumCircle => z.1.1) heq
    exact compactifiedTime_injective hbase
  · rcases hstep with hleft | hright
    · rcases hleft with ⟨htzero, _, _⟩
      change compactifiedTime t = 0 at htzero
      have hpos := (compactifiedTime_mem_unitInterval t).1
      linarith
    · rcases hright with ⟨htone, _, _⟩
      change compactifiedTime t = 1 at htone
      have hlt := (compactifiedTime_mem_unitInterval t).2
      linarith

/-- On the compactified KMS path, the fixed locus of Klein base reflection is
exactly the midline time `t = 0`. -/
theorem compactifiedKleinPath_reflection_fixed_iff_zero
    (x : KleinBrillouinBase.MomentumCircle) (t : ℝ) :
    canonicalBaseReflection (compactifiedKleinPath x t) = compactifiedKleinPath x t ↔
      t = 0 := by
  constructor
  · intro h
    rw [compactifiedKleinPath_timeReflection] at h
    have htime := compactifiedKleinPath_injective x h
    linarith
  · rintro rfl
    simpa using compactifiedKleinPath_timeReflection x 0

end InfoGeometry.NCG.KMSKleinTopologicalEndGlue

end noncomputable section
