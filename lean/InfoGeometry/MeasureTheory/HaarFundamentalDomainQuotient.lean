/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# InfoGeometry.MeasureTheory.HaarFundamentalDomainQuotient

Ported to Mathlib `v4.34.1` from `mccorvie/riemann-masullo` (Apache-2.0, upstream
commit `b967ac4`):
- `RiemannMasullo/ForMathlib/MeasureTheory/Group/FundamentalDomain.lean`
- `RiemannMasullo/ForMathlib/MeasureTheory/Group/Compact.lean`

Provides:
- `map_restrict_fundamentalDomain_eq`: a fundamental domain with matching total mass
  pushes Haar measure on `G` down to the prescribed Haar measure on the compact quotient `Q`;
- `compactSpace_of_isFiniteMeasure_haar`: a topological group carrying a finite regular
  Haar measure is compact.
-/

open Function MeasureTheory Set
open scoped Pointwise ENNReal

namespace InfoGeometry.MeasureTheory.HaarFundamentalDomainQuotient

/-- A fundamental domain with the prescribed quotient mass pushes Haar measure to
the given Haar measure on the compact quotient. -/
theorem map_restrict_fundamentalDomain_eq
    {G Q : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (p : G →* Q) (hp : Continuous p) (hsur : Surjective p) (H : Subgroup G)
    [Countable H] (hker : H ≤ p.ker) (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]
    (ν : Measure Q) [ν.IsHaarMeasure] [ν.InnerRegularCompactLTTop] {D : Set G}
    (hD : IsFundamentalDomain H D μ) (hmass : μ D = ν univ) :
    (μ.restrict D).map p = ν := by
  let ρ := (μ.restrict D).map p
  have hρ : ρ univ = ν univ := by
    rwa [Measure.map_apply hp.measurable MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  let : IsFiniteMeasure ρ := ⟨hρ.trans_lt (measure_lt_top _ _)⟩
  let : ρ.InnerRegularCompactLTTop :=
    Measure.InnerRegularCompactLTTop.map_of_continuous hp
  let : ρ.IsMulLeftInvariant := ⟨fun a ↦ by
    obtain ⟨u, rfl⟩ := hsur a
    ext S hS
    have hA : MeasurableSet (p ⁻¹' S) := hp.measurable hS
    have hinv (h : H) : (fun x : G ↦ h • x) ⁻¹' (p ⁻¹' S) = p ⁻¹' S := by
      ext x
      change p (h.val * x) ∈ S ↔ p x ∈ S
      rw [map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
    rw [Measure.map_apply (measurable_const_mul _) hS]
    change (μ.restrict D).map p _ = (μ.restrict D).map p S
    rw [Measure.map_apply hp.measurable ((measurable_const_mul _) hS),
      Measure.map_apply hp.measurable hS,
      Measure.restrict_apply (hp.measurable ((measurable_const_mul _) hS)),
      Measure.restrict_apply hA]
    calc
      _ = μ ((fun x : G ↦ u * x) ⁻¹' ((p ⁻¹' S) ∩ u • D)) := by
        congr 1
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, Set.mem_smul_set_iff_inv_smul_mem,
          smul_eq_mul, inv_mul_cancel_left]
      _ = μ ((p ⁻¹' S) ∩ u • D) := measure_preimage_mul μ u _
      _ = _ := (hD.smul_of_comm u).measure_set_eq hD hA hinv⟩
  let c := Measure.haarScalarFactor ρ ν
  have heq (S : Set Q) : ρ S = c • ν S :=
    Measure.measure_isMulLeftInvariant_eq_smul_of_ne_top ρ ν (measure_ne_top _ _) (measure_ne_top _ _)
  have hc : (c : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj (NeZero.ne (ν univ))
      (measure_ne_top ν univ)).mp
    simpa only [ENNReal.smul_def, smul_eq_mul, one_mul] using (heq univ).symm.trans hρ
  ext S
  simpa only [ENNReal.smul_def, smul_eq_mul, hc, one_mul] using heq S

/-- A topological group with finite, regular Haar measure is compact. -/
theorem compactSpace_of_isFiniteMeasure_haar {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [IsFiniteMeasure μ] : CompactSpace G := by
  obtain ⟨K, _, hK, hmass⟩ := isOpen_univ.exists_lt_isCompact (μ := μ)
    (ENNReal.half_lt_self (isOpen_univ.measure_ne_zero μ univ_nonempty) (measure_lt_top μ _).ne)
  have hcover : K * K⁻¹ = univ := by
    apply eq_univ_of_forall
    intro x
    have hdisj : ¬ Disjoint K ((x * ·) ⁻¹' K) := by
      intro h
      have hmeas := hK.isClosed.measurableSet.preimage (measurable_const_mul x)
      have hlarge : μ univ < μ (K ∪ (x * ·) ⁻¹' K) := calc
        μ univ = μ univ / 2 + μ univ / 2 := (ENNReal.add_halves _).symm
        _ < μ K + μ K := ENNReal.add_lt_add hmass hmass
        _ = μ (K ∪ (x * ·) ⁻¹' K) := by rw [measure_union h hmeas, measure_preimage_mul]
      exact hlarge.not_ge (measure_mono (subset_univ _))
    obtain ⟨y, hy, hxy⟩ := Set.not_disjoint_iff.mp hdisj
    exact Set.mem_mul.mpr ⟨x * y, hxy, y⁻¹, Set.inv_mem_inv.mpr hy, by simp⟩
  exact ⟨hcover ▸ hK.mul hK.inv⟩

end InfoGeometry.MeasureTheory.HaarFundamentalDomainQuotient
