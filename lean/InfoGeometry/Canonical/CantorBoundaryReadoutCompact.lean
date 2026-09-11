import InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.StoneCantorMathlib

theorem isCompact_readout_image_prefixCylinder
    (n : ℕ) (w : BitWord n) :
    IsCompact (realBinaryReadout '' prefixCylinder n w) := by
  exact (isCompact_prefixCylinder n w).image continuous_realBinaryReadout

theorem prefixCylinder_nonempty (n : ℕ) (w : BitWord n) :
    (prefixCylinder n w).Nonempty := by
  exact ⟨prefixExtend w (fun _ => false), prefixExtend_mem_prefixCylinder w _⟩

theorem readout_image_prefixCylinder_nonempty
    (n : ℕ) (w : BitWord n) :
    (realBinaryReadout '' prefixCylinder n w).Nonempty := by
  rcases prefixCylinder_nonempty n w with ⟨x, hx⟩
  exact ⟨realBinaryReadout x, ⟨x, hx, rfl⟩⟩

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

end InfoGeometry.Canonical.CantorBoundaryReadoutCompact
