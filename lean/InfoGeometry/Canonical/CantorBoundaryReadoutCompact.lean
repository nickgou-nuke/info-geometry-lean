import InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact readout images of finite cylinders

The continuous binary readout sends each compact finite cylinder to a compact
real set.  The refinement estimate additionally places that image in the
corresponding dyadic interval.  This is a topological/metric consequence of
the existing boundary and readout owners, with no measure extension claim.
-/

namespace InfoGeometry.Canonical.CantorBoundaryReadoutCompact

open Set
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.StoneCantorMathlib

theorem isCompact_readout_image_prefixCylinder
    (n : ℕ) (w : BitWord n) :
    IsCompact (realBinaryReadout '' prefixCylinder n w) := by
  exact (isCompact_prefixCylinder n w).image continuous_realBinaryReadout

theorem isClosed_readout_image_prefixCylinder
    (n : ℕ) (w : BitWord n) :
    IsClosed (realBinaryReadout '' prefixCylinder n w) := by
  letI : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
  exact (isCompact_readout_image_prefixCylinder n w).isClosed

theorem prefixCylinder_nonempty (n : ℕ) (w : BitWord n) :
    (prefixCylinder n w).Nonempty := by
  exact ⟨prefixExtend w (fun _ => false), prefixExtend_mem_prefixCylinder w _⟩

theorem readout_image_prefixCylinder_nonempty
    (n : ℕ) (w : BitWord n) :
    (realBinaryReadout '' prefixCylinder n w).Nonempty := by
  rcases prefixCylinder_nonempty n w with ⟨x, hx⟩
  exact ⟨realBinaryReadout x, ⟨x, hx, rfl⟩⟩

theorem readout_image_prefixCylinder_subset_unitInterval
    (n : ℕ) (w : BitWord n) :
    realBinaryReadout '' prefixCylinder n w ⊆ Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rcases hz with ⟨x, _, rfl⟩
  exact realBinaryReadout_mem_unitInterval x

theorem readout_image_prefixCylinder_subset_dyadicInterval
    (n : ℕ) (w : BitWord n) :
    realBinaryReadout '' prefixCylinder n w ⊆
      Set.Icc (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n) := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  rw [← range_prefixExtend_eq_prefixCylinder] at hy
  rcases hy with ⟨x, rfl⟩
  exact realBinaryReadout_prefixExtend_mem_dyadicInterval n w x

theorem readout_image_prefixCylinder_eq_affine_image
    (n : ℕ) (w : BitWord n) :
    realBinaryReadout '' prefixCylinder n w =
      (fun t : ℝ =>
        finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n * t) ''
        Set.range realBinaryReadout := by
  rw [← range_prefixExtend_eq_prefixCylinder]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨x, rfl⟩
    refine ⟨realBinaryReadout x, ⟨x, rfl⟩, ?_⟩
    exact (realBinaryReadout_prefixExtend n w x).symm
  · rintro ⟨t, ⟨x, rfl⟩, rfl⟩
    refine ⟨prefixExtend w x, ?_, ?_⟩
    · exact ⟨x, rfl⟩
    · exact realBinaryReadout_prefixExtend n w x

theorem readout_image_prefixCylinder_eq_affine_unitInterval
    (n : ℕ) (w : BitWord n) :
    realBinaryReadout '' prefixCylinder n w =
      (fun t : ℝ =>
        finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n * t) ''
        Set.Icc (0 : ℝ) 1 := by
  rw [readout_image_prefixCylinder_eq_affine_image,
    realBinaryReadout_range_eq_unitInterval]

theorem readout_image_prefixCylinder_eq_dyadicInterval
    (n : ℕ) (w : BitWord n) :
    realBinaryReadout '' prefixCylinder n w =
      Set.Icc (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n) := by
  rw [readout_image_prefixCylinder_eq_affine_unitInterval]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · have hc : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
      nlinarith [mul_nonneg hc ht.1]
    · have hc : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hc]
  · intro hz
    have hc : 0 < (1 / 2 : ℝ) ^ n := by positivity
    refine ⟨(z - finitePrefixReadout (List.ofFn w)) / (1 / 2 : ℝ) ^ n, ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hz.1) (le_of_lt hc)
      · apply (div_le_iff₀ hc).2
        linarith [hz.2]
    · field_simp
      ring

theorem finitePrefixReadout_mem_readout_image_prefixCylinder
    (n : ℕ) (w : BitWord n) :
    finitePrefixReadout (List.ofFn w) ∈
      realBinaryReadout '' prefixCylinder n w := by
  rw [readout_image_prefixCylinder_eq_dyadicInterval]
  constructor
  · exact le_rfl
  · linarith [show 0 ≤ (1 / 2 : ℝ) ^ n by positivity]

theorem finitePrefixReadout_plus_tail_mem_readout_image_prefixCylinder
    (n : ℕ) (w : BitWord n) :
    finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n ∈
      realBinaryReadout '' prefixCylinder n w := by
  rw [readout_image_prefixCylinder_eq_dyadicInterval]
  constructor
  · linarith [show 0 ≤ (1 / 2 : ℝ) ^ n by positivity]
  · exact le_rfl

end InfoGeometry.Canonical.CantorBoundaryReadoutCompact
