/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceLogisticBitwordBridge
import InfoGeometry.Canonical.WheelerItFromBit
import InfoGeometry.NCG.KMSStripKleinMonodromy
import InfoGeometry.Canonical.CantorBoundaryDyadicCover

/-!
# Concrete Wheeler readout of Peirce logistic bitword cylinders

The previous module proves operator-valued cylinder identities over an
arbitrary ring and transports them through an arbitrary additive readout.
Here the readout is the existing finite Wheeler functional
`itFromBitCoordinate ψ X = Tr(ρ_η(ψ) X)`. Its additivity is proved from the
trace definition. No normalization is assumed: the conserved total is the
actual value of this readout on `1`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Canonical.WheelerItFromBit
open InfoGeometry.NCG.KMSStripKleinMonodromy
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryDyadicCover

/-- For each spinor, the existing trace-based Wheeler coordinate is additive
in the operator argument. -/
theorem wheelerReadout_additive
    (ψ : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (X Y : InfoGeometry.Canonical.WheelerItFromBit.Mat32) :
    itFromBitCoordinate ψ (X + Y) =
      itFromBitCoordinate ψ X + itFromBitCoordinate ψ Y := by
  simp [itFromBitCoordinate,
    InfoGeometry.Physics.EmergentSpacetimeBilinear.spacetimeCoordinate,
    Matrix.trace_add, mul_add]

/-- The concrete Wheeler readout carries logistic operator complementarity to
conservation with the (not necessarily normalized) total readout of `1`. -/
theorem wheelerReadout_logistic_partition
    (ψ : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    {P : InfoGeometry.Canonical.WheelerItFromBit.Mat32} (hP : P * P = P)
    (A C : InfoGeometry.Canonical.WheelerItFromBit.Mat32) :
    itFromBitCoordinate ψ (peirceLogisticPlus P A C) +
      itFromBitCoordinate ψ (peirceLogisticMinus P A C) =
        itFromBitCoordinate ψ 1 := by
  rw [← wheelerReadout_additive ψ,
    (peirceLogistic_operator_identities hP A C).1]

/-- Refinement of operator cylinders remains additive after applying the
concrete Wheeler trace readout. -/
theorem wheelerReadout_cylinder_refinement
    (ψ : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (L : InfoGeometry.Canonical.WheelerItFromBit.Mat32) (w : List Bool) :
    itFromBitCoordinate ψ (operatorBitwordCylinder (true :: w) L) +
      itFromBitCoordinate ψ (operatorBitwordCylinder (false :: w) L) =
        itFromBitCoordinate ψ (operatorBitwordCylinder w L) := by
  rw [← wheelerReadout_additive ψ, operatorBitwordCylinder_refinement]

/-- The concrete Wheeler readout of either mixed Peirce-logistic cylinder is
the readout of the negative idempotency defect of the Peirce variance. -/
theorem wheelerReadout_mixed_logistic_variance
    (ψ : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    {P : InfoGeometry.Canonical.WheelerItFromBit.Mat32} (hP : P * P = P)
    (A C : InfoGeometry.Canonical.WheelerItFromBit.Mat32) :
    itFromBitCoordinate ψ
      (operatorBitwordCylinder [true, false] (peirceLogisticPlus P A C)) =
        itFromBitCoordinate ψ
          (-(genV P A C * genV P A C - genV P A C)) ∧
    itFromBitCoordinate ψ
      (operatorBitwordCylinder [false, true] (peirceLogisticPlus P A C)) =
        itFromBitCoordinate ψ
          (-(genV P A C * genV P A C - genV P A C)) := by
  rcases peirceLogistic_mixed_cylinders_are_variance hP A C with ⟨hTF, hFT⟩
  exact ⟨congrArg (itFromBitCoordinate ψ) hTF,
    congrArg (itFromBitCoordinate ψ) hFT⟩

/-- At every finite depth, the Wheeler readout of any operator-valued bitword
cylinder lies in an actual dyadic cell indexed by a finite Cantor bitword.
This is a finite-resolution statement, not an assertion of an infinite
compatible branch or a measure on the Cantor quotient. -/
theorem wheelerCylinder_finite_bitword_cover
    (ψ : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (L : InfoGeometry.Canonical.WheelerItFromBit.Mat32)
    (w : List Bool) (N : ℕ) :
    ∃ v : BitWord N,
      compactifiedTime
          (itFromBitCoordinate ψ (operatorBitwordCylinder w L)) ∈
        Set.Icc (finitePrefixReadout (List.ofFn v))
          (finitePrefixReadout (List.ofFn v) + (1 / 2 : ℝ) ^ N) := by
  let t := itFromBitCoordinate ψ (operatorBitwordCylinder w L)
  have ht : compactifiedTime t ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨(compactifiedTime_mem_unitInterval t).1.le,
      (compactifiedTime_mem_unitInterval t).2.le⟩
  exact exists_prefix_dyadic_cover (compactifiedTime t) ht N

end InfoGeometry.OperatorAlgebra.PeirceSpine
