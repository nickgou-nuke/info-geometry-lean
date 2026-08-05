import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

/-!
# Finite binary stages and the interval readout

This owner records the concrete approximation supplied by finite binary
prefixes.  It does not identify the Cantor boundary with an interval; that
identification belongs to the quotient readout owner.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.CantorBinaryReadoutSynthesis

open InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget
open InfoGeometry.Canonical.CantorBoundaryDyadicCover
open InfoGeometry.Canonical.CantorBoundaryReadoutDyadicRange
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def finitePrefixReadoutPoint (p : Σ n : ℕ, BitWord n) : UnitInterval :=
  ⟨finitePrefixReadout (List.ofFn p.2), by
    obtain ⟨w, hw⟩ := finitePrefixReadout_mem_realBinaryReadout_range
      (List.ofFn p.2)
    rw [← hw]
    exact realBinaryReadout_mem_unitInterval w⟩

@[simp] theorem finitePrefixReadoutPoint_val (p : Σ n : ℕ, BitWord n) :
    (finitePrefixReadoutPoint p : ℝ) =
      finitePrefixReadout (List.ofFn p.2) :=
  rfl

theorem finitePrefixReadoutPoint_has_quotient_representative
    (p : Σ n : ℕ, BitWord n) :
    ∃ q : ReadoutQuotient,
      (quotientReadoutInterval q : ℝ) = finitePrefixReadout (List.ofFn p.2) := by
  obtain ⟨w, hw⟩ := finitePrefixReadout_mem_realBinaryReadout_range
    (List.ofFn p.2)
  refine ⟨quotientMap w, ?_⟩
  change quotientReadout (quotientMap w) = finitePrefixReadout (List.ofFn p.2)
  rw [quotientReadout_comp, hw]

theorem exists_finitePrefixReadoutPoint_close
    (x : UnitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Σ n : ℕ, BitWord n,
      dist x (finitePrefixReadoutPoint p) < ε := by
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    have hN' := hN N (le_rfl)
    rw [Real.dist_eq] at hN'
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)]
      using hN'
  obtain ⟨w, hw⟩ := exists_prefix_dyadic_cover x.1 x.2 N
  refine ⟨⟨N, w⟩, ?_⟩
  have h_lower :
      0 ≤ x.1 - finitePrefixReadout (List.ofFn w) := by
    linarith [hw.1]
  change dist x.1 (finitePrefixReadout (List.ofFn w)) < ε
  rw [Real.dist_eq, abs_of_nonneg h_lower]
  linarith [hw.2, hpowN]

theorem finitePrefixReadoutPoint_arbitrarily_close
    (x : UnitInterval) :
    ∀ ε : ℝ, 0 < ε →
      ∃ p : Σ n : ℕ, BitWord n,
        dist x (finitePrefixReadoutPoint p) < ε := by
  intro ε hε
  exact exists_finitePrefixReadoutPoint_close x hε

theorem finitePrefixReadoutPoint_mem_closure_range
    (x : UnitInterval) :
    x ∈ closure (Set.range finitePrefixReadoutPoint) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_finitePrefixReadoutPoint_close x hε
  exact ⟨finitePrefixReadoutPoint p, ⟨p, rfl⟩, hp⟩

theorem closure_range_finitePrefixReadoutPoint :
    closure (Set.range finitePrefixReadoutPoint) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact finitePrefixReadoutPoint_mem_closure_range x

theorem denseRange_finitePrefixReadoutPoint :
    DenseRange finitePrefixReadoutPoint := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  exact exists_finitePrefixReadoutPoint_close x hε

end InfoGeometry.Canonical.CantorBinaryReadoutSynthesis
