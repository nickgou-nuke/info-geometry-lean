import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms
import InfoGeometry.Canonical.SplitOctonionCanonicalThreeForm

/-!
# Native cyclic colour automorphism property

The repository already owns the native order-three colour cycle.  This file
packages its verified properties in one small structure.  The result is a
finite rational property preserving multiplication, the coordinate quadratic
form, and the canonical trilinear form.  It is not a construction of the
Lie group `G₂`, a `Spin (4,4)` representation, or a holonomy theorem.
-/

namespace InfoGeometry.Canonical

structure SplitOctonionCyclicAutomorphismWitness where
  map_one :
    trialityColorCycle (Pi.single IntegralSplitBasis.one (1 : ℚ)) =
      Pi.single IntegralSplitBasis.one (1 : ℚ)
  map_mul :
    ∀ x y : StandardRationalSplitOctonion,
      trialityColorCycle (splitOctonionMulQ x y) =
        splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y)
  order_three :
    ∀ x : StandardRationalSplitOctonion,
      trialityColorCycle (trialityColorCycle (trialityColorCycle x)) = x
  map_norm :
    ∀ x : StandardRationalSplitOctonion,
      coordinateSplitNorm (trialityColorCycle x) = coordinateSplitNorm x
  map_three_form :
    ∀ x y z : StandardRationalSplitOctonion,
      canonicalThreeForm
          (trialityColorCycle x) (trialityColorCycle y) (trialityColorCycle z) =
        canonicalThreeForm x y z

noncomputable def trialityColorCycleWitness :
    SplitOctonionCyclicAutomorphismWitness where
  map_one := trialityColorCycle_one_basis
  map_mul := trialityColorCycle_map_mul
  order_three := by
    intro x
    exact colorCycle_order_three x
  map_norm := trialityColorCycle_preserves_norm
  map_three_form := trialityColorCycle_preserves_canonicalThreeForm

@[simp] theorem trialityColorCycleWitness_map_one :
    trialityColorCycle (Pi.single IntegralSplitBasis.one (1 : ℚ)) =
      Pi.single IntegralSplitBasis.one (1 : ℚ) :=
  trialityColorCycle_one_basis

theorem trialityColorCycleWitness_map_mul
    (x y : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y) :=
  trialityColorCycleWitness.map_mul x y

theorem trialityColorCycleWitness_order_three
    (x : StandardRationalSplitOctonion) :
    trialityColorCycle (trialityColorCycle (trialityColorCycle x)) = x :=
  trialityColorCycleWitness.order_three x

end InfoGeometry.Canonical
