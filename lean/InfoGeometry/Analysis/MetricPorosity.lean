/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.PorosityIteration
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.FieldSimp

/-!
# Metric pores under open thickening

The holes in this owner are genuinely disjoint from the set. The predicate
also requires positive porosity and a nonempty interval of positive scales.
No identification with an almost-everywhere porosity notion is asserted.
Open thickening at radius zero is the native empty thickening; no equality
between successive thickenings and thickening by their sum is assumed.
-/

namespace InfoGeometry.Analysis.MetricPorosity

open Metric Set PorosityIteration

variable {X : Type*} [PseudoMetricSpace X]

/-- Every ball at a specified positive scale contains a disjoint relative hole. -/
def HasDisjointPores (s : Set X) (ν lower upper : ℝ) : Prop :=
  0 < ν ∧ ν ≤ 1 ∧ 0 < lower ∧ lower ≤ upper ∧
    ∀ (x : X) (r : ℝ), lower ≤ r → r ≤ upper →
      ∃ y, ball y (ν * r) ⊆ ball x r ∧ Disjoint (ball y (ν * r)) s

/-- Thickening a set shrinks any disjoint ball by at most the thickening radius. -/
theorem disjoint_ball_thickening {s : Set X} {y : X} {r ε : ℝ}
    (h : Disjoint (ball y r) s) :
    Disjoint (ball y (r - ε)) (thickening ε s) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hxt
  obtain ⟨z, hzs, hxz⟩ := mem_thickening_iff.mp hxt
  have hz : z ∈ ball y r := by
    rw [mem_ball] at hx ⊢
    have htriangle := dist_triangle z x y
    rw [dist_comm z x] at htriangle
    linarith
  exact Set.disjoint_left.mp h hz hzs

/-- Disjoint-hole porosity survives thickening on the smaller scale interval,
with an explicit positive reduced porosity parameter. -/
theorem HasDisjointPores.thickening {s : Set X} {ν lower upper lower' ε : ℝ}
    (h : HasDisjointPores s ν lower upper)
    (hlower : lower ≤ lower') (hupper : lower' ≤ upper)
    (hε : 0 ≤ ε) (hsmall : ε < ν * lower') :
    HasDisjointPores (Metric.thickening ε s) (ν - ε / lower') lower' upper := by
  obtain ⟨hν, hν1, hlowerpos, _, hpores⟩ := h
  have hlower' : 0 < lower' := hlowerpos.trans_le hlower
  have hdiv : ε / lower' < ν := (div_lt_iff₀ hlower').mpr hsmall
  have hdiv0 : 0 ≤ ε / lower' := div_nonneg hε hlower'.le
  refine ⟨sub_pos.mpr hdiv, (sub_le_self _ hdiv0).trans hν1,
    hlower', hupper, ?_⟩
  intro x r hrl hru
  obtain ⟨y, hinside, hdisjoint⟩ := hpores x r (hlower.trans hrl) hru
  have hloss : ε ≤ (ε / lower') * r := by
    calc
      ε = (ε / lower') * lower' := by field_simp
      _ ≤ (ε / lower') * r := mul_le_mul_of_nonneg_left hrl hdiv0
  have hshrink : (ν - ε / lower') * r ≤ ν * r - ε := by nlinarith
  refine ⟨y, (ball_subset_ball (hshrink.trans (sub_le_self _ hε))).trans hinside, ?_⟩
  exact (disjoint_ball_thickening hdisjoint).mono_left (ball_subset_ball hshrink)

/-- A concrete cumulative thickness realizes each remaining-porosity parameter.
This uses one thickening, without identifying it with iterated thickenings. -/
theorem HasDisjointPores.remainingPorosity_thickening
    {s : Set X} {ν lower upper lower' : ℝ}
    (h : HasDisjointPores s ν lower upper)
    (hlower : lower ≤ lower') (hupper : lower' ≤ upper) (n : ℕ) :
    HasDisjointPores
      (Metric.thickening ((ν - remainingPorosity ν n) * lower') s)
      (remainingPorosity ν n) lower' upper := by
  have hν := h.1
  have hν1 := h.2.1
  have hlower' : 0 < lower' := h.2.2.1.trans_le hlower
  have hremaining := remainingPorosity_pos hν hν1 n
  have hε : 0 ≤ (ν - remainingPorosity ν n) * lower' :=
    mul_nonneg (sub_nonneg.mpr (remainingPorosity_le_initial hν.le n)) hlower'.le
  have hsmall : (ν - remainingPorosity ν n) * lower' < ν * lower' := by
    nlinarith
  have ht := h.thickening hlower hupper hε hsmall
  have hid : ν - ((ν - remainingPorosity ν n) * lower') / lower' =
      remainingPorosity ν n := by field_simp; ring
  simpa only [hid] using ht

end InfoGeometry.Analysis.MetricPorosity
