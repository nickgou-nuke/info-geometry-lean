import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms
import InfoGeometry.Canonical.SplitOctonionCanonicalThreeForm

/-!
# Native cyclic colour automorphism property

The repository already owns the native order-three colour cycle.  This file
exposes its verified multiplication and order properties.
-/

namespace InfoGeometry.Canonical

@[simp] theorem trialityColorCycle_map_one :
    trialityColorCycle (Pi.single IntegralSplitBasis.one (1 : ℚ)) =
      Pi.single IntegralSplitBasis.one (1 : ℚ) :=
  trialityColorCycle_one_basis

theorem trialityColorCycle_map_mul_readout
    (x y : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y) :=
  trialityColorCycle_map_mul x y

theorem trialityColorCycle_order_three_readout
    (x : StandardRationalSplitOctonion) :
    trialityColorCycle (trialityColorCycle (trialityColorCycle x)) = x :=
  colorCycle_order_three x

end InfoGeometry.Canonical
