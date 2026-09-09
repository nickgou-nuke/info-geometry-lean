import InfoGeometry.Canonical.SchnakenbergHodgeConstruction
import InfoGeometry.Canonical.PositiveRayCore

/-!
# Cycle production on the existing positive-ray state space

The stochastic graph owner already distinguishes rate affinity from flux
 affinity and proves edgewise positivity. Here its probability field is
constructed from the existing projective gauge section. The stored `flow`
and `affinity` fields are not used as arbitrary substitutes for kinetic fluxes.
Raw production changes with a common kinetic scale; its ratio to total traffic
is exposed separately, with an Option guard at zero traffic.
-/

noncomputable section
namespace InfoGeometry.Projective.GraphCycleEntropy

open InfoGeometry
open Canonical.ThermodynamicChiralGraphCalculus
open Canonical.PositiveRayCore
open Canonical.SchnakenbergHodgeConstruction
open scoped BigOperators

variable {V E : Type} [Fintype V] [Nonempty V] [Fintype E] [DecidableEq V]

/-- Use the already constructed normalized section of a positive state ray. -/
def graphAtRay (G : DirectedThermoGraph V E) (q : PositiveRay V) :
    DirectedThermoGraph V E :=
  { G with probability := fun v => gaugeSection q v }

/-- Representative adapter only; `graphAtRay` is defined on the quotient. -/
def graphAtWeight (G : DirectedThermoGraph V E) (w : PositiveMeasure V ℝ) :
    DirectedThermoGraph V E := graphAtRay G (Quotient.mk _ w)

theorem graphAtWeight_scale (G : DirectedThermoGraph V E) (w : PositiveMeasure V ℝ)
    (c : ℝ) (hc : 0 < c) :
    graphAtWeight G (PositiveMeasure.scale c hc w) = graphAtWeight G w := by
  simp only [graphAtWeight, graphAtRay, gaugeSection_mk, PositiveMeasure.normalize_scale]

/-- Actual kinetic positivity, using existing edgewise proofs and constructed state weights. -/
theorem production_nonneg (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e) :
    0 ≤ (graphAtRay G q).stochasticEntropyProduction := by
  apply (graphAtRay G q).stochasticEntropyProduction_nonneg_of_positive_flux
  · intro e
    exact mul_pos ((gaugeSection q).pos (G.src e)) (hk e)
  · intro e
    exact mul_pos ((gaugeSection q).pos (G.dst e)) (hl e)

/-- The probability correction is an exact log-ratio coboundary with the owner's sign. -/
theorem fluxAffinity_split (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e) (e : E) :
    (graphAtRay G q).stochasticAffinity e =
      (graphAtRay G q).logAffinity e -
        (graphAtRay G q).gaugeCoboundary (fun v => Real.log (gaugeSection q v)) e := by
  have hs := (gaugeSection q).pos (G.src e)
  have ht := (gaugeSection q).pos (G.dst e)
  dsimp [DirectedThermoGraph.stochasticAffinity, DirectedThermoGraph.logAffinity,
    DirectedThermoGraph.gaugeCoboundary, graphAtRay]
  rw [Real.log_div (mul_pos hs (hk e)).ne' (mul_pos ht (hl e)).ne',
    Real.log_mul hs.ne' (hk e).ne', Real.log_mul ht.ne' (hl e).ne',
    Real.log_div (hk e).ne' (hl e).ne']
  ring

/-- Under Kirchhoff conservation the exact probability correction contributes zero. -/
theorem steady_production_rateAffinity (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e)
    (hJ : (graphAtRay G q).IsCycleFlow (graphAtRay G q).stochasticCurrent) :
    (graphAtRay G q).stochasticEntropyProduction =
      ∑ e, (graphAtRay G q).stochasticCurrent e * (graphAtRay G q).logAffinity e := by
  unfold DirectedThermoGraph.stochasticEntropyProduction
  simp_rw [fluxAffinity_split G q hk hl, mul_sub]
  rw [Finset.sum_sub_distrib,
    steady_pair_coboundary_zero (graphAtRay G q) _ hJ
      (fun v => Real.log (gaugeSection q v)), sub_zero]

/-- The cycle component is constructed by projection, not supplied as a hypothesis. -/
theorem steady_production_cycleComponent (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e)
    (hJ : (graphAtRay G q).IsCycleFlow (graphAtRay G q).stochasticCurrent) :
    (graphAtRay G q).stochasticEntropyProduction =
      ∑ e, (graphAtRay G q).stochasticCurrent e *
        cycleComponent (graphAtRay G q) (graphAtRay G q).logAffinity e := by
  rw [steady_production_rateAffinity G q hk hl hJ]
  exact steady_pair_cycleComponent (graphAtRay G q) _ _ hJ

/-- Strict positivity of the elementary logarithmic entropy kernel. -/
theorem fluxKernel_zero_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x-y) * Real.log (x/y) = 0 ↔ x = y := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hsub | hlog
    · exact sub_eq_zero.mp hsub
    · have he := Real.exp_log (div_pos hx hy)
      rw [hlog, Real.exp_zero] at he
      exact (div_eq_one_iff_eq hy.ne').mp he.symm
  · rintro rfl
    simp

/-- Zero total production means equality of every forward/reverse probability flux. -/
theorem production_zero_iff_edge_balance (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e) :
    (graphAtRay G q).stochasticEntropyProduction = 0 ↔
      ∀ e, gaugeSection q (G.src e) * G.forwardRate e =
        gaugeSection q (G.dst e) * G.reverseRate e := by
  let H := graphAtRay G q
  have hp (e : E) : 0 < H.probability (H.src e) * H.forwardRate e :=
    mul_pos ((gaugeSection q).pos (G.src e)) (hk e)
  have hm (e : E) : 0 < H.probability (H.dst e) * H.reverseRate e :=
    mul_pos ((gaugeSection q).pos (G.dst e)) (hl e)
  have hn (e : E) : 0 ≤ H.stochasticCurrent e * H.stochasticAffinity e :=
    H.stochasticCurrent_mul_stochasticAffinity_nonneg_of_positive_flux e (hp e) (hm e)
  change (∑ e, H.stochasticCurrent e * H.stochasticAffinity e) = 0 ↔ _
  constructor
  · intro h e
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hn e)).mp h e
      (Finset.mem_univ e)
    exact (fluxKernel_zero_iff (hp e) (hm e)).mp he
  · intro h
    apply Finset.sum_eq_zero
    intro e _
    apply (fluxKernel_zero_iff (hp e) (hm e)).mpr
    exact h e

/-- A common kinetic scale, distinct from changing the homogeneous state lift. -/
def scaleRates (G : DirectedThermoGraph V E) (c : ℝ) : DirectedThermoGraph V E :=
  { G with forwardRate := fun e => c * G.forwardRate e
           reverseRate := fun e => c * G.reverseRate e }

/-- The sum of both directed probability fluxes; no external time coordinate. -/
def traffic (G : DirectedThermoGraph V E) (q : PositiveRay V) : ℝ :=
  ∑ e, (gaugeSection q (G.src e) * G.forwardRate e +
    gaugeSection q (G.dst e) * G.reverseRate e)

/-- At zero traffic there is no production-per-traffic ratio. -/
def productionPerTraffic (G : DirectedThermoGraph V E) (q : PositiveRay V) : Option ℝ :=
  if traffic G q = 0 then none
  else some ((graphAtRay G q).stochasticEntropyProduction / traffic G q)

theorem traffic_pos [Nonempty E] (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e) :
    0 < traffic G q := by
  classical
  apply Finset.sum_pos
  · intro e _
    exact add_pos (mul_pos ((gaugeSection q).pos _) (hk e))
      (mul_pos ((gaugeSection q).pos _) (hl e))
  · exact Finset.univ_nonempty

theorem productionPerTraffic_eq_some [Nonempty E]
    (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (hk : ∀ e, 0 < G.forwardRate e) (hl : ∀ e, 0 < G.reverseRate e) :
    productionPerTraffic G q =
      some ((graphAtRay G q).stochasticEntropyProduction / traffic G q) := by
  simp only [productionPerTraffic, if_neg (traffic_pos G q hk hl).ne']

/-- Both directed fluxes scale; their log ratio does not. -/
theorem scaled_stochasticAffinity (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (c : ℝ) (hc : c ≠ 0) (e : E) :
    (graphAtRay (scaleRates G c) q).stochasticAffinity e =
      (graphAtRay G q).stochasticAffinity e := by
  unfold DirectedThermoGraph.stochasticAffinity
  dsimp [graphAtRay, scaleRates]
  congr 1
  rw [mul_left_comm (gaugeSection q (G.src e)) c,
    mul_left_comm (gaugeSection q (G.dst e)) c]
  exact mul_div_mul_left _ _ hc

theorem production_scaleRates (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (c : ℝ) (hc : c ≠ 0) :
    (graphAtRay (scaleRates G c) q).stochasticEntropyProduction =
      c * (graphAtRay G q).stochasticEntropyProduction := by
  unfold DirectedThermoGraph.stochasticEntropyProduction
  simp_rw [scaled_stochasticAffinity G q c hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  dsimp [DirectedThermoGraph.stochasticCurrent, graphAtRay, scaleRates]
  ring

theorem traffic_scaleRates (G : DirectedThermoGraph V E) (q : PositiveRay V) (c : ℝ) :
  traffic (scaleRates G c) q = c * traffic G q := by
  simp only [traffic, scaleRates, Finset.sum_add_distrib, Finset.mul_sum]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro e he
    ring
  · apply Finset.sum_congr rfl
    intro e he
    ring

/-- The guarded ratio is invariant under a common nonzero kinetic scale. -/
theorem productionPerTraffic_scaleRates (G : DirectedThermoGraph V E) (q : PositiveRay V)
    (c : ℝ) (hc : c ≠ 0) :
    productionPerTraffic (scaleRates G c) q = productionPerTraffic G q := by
  unfold productionPerTraffic
  rw [traffic_scaleRates, production_scaleRates G q c hc]
  by_cases h : traffic G q = 0
  · simp [h]
  · simp only [mul_eq_zero, hc, false_or, h, if_false]
    congr 1
    exact mul_div_mul_left _ _ hc

end InfoGeometry.Projective.GraphCycleEntropy
