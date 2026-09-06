import InfoGeometry.Canonical.CanonicalChiralZornEquivariance
import InfoGeometry.Lie.SplitOctonionImaginaryThreeForm
import InfoGeometry.Lie.SplitOctonionImaginaryTensor

/-!
# Canonical colour automorphisms on the native imaginary form

The canonical/chiral coordinate equivalence supplies concrete multiplication
automorphisms on the canonical Zorn carrier.  This owner consumes those
automorphisms in the native imaginary three-form owner; it does not introduce
a second form or identify the two distinct `ell` conventions.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCanonicalColorImaginaryForm

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryThreeForm
open InfoGeometry.Lie.SplitOctonionImaginaryTensor

abbrev Imaginary := InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary

theorem canonicalColorCycle_preserves_imaginaryThreeForm
    (X Y Z : Imaginary) :
    imaginaryThreeForm
        (imaginaryAut canonicalColorCycleCompositionAut X)
        (imaginaryAut canonicalColorCycleCompositionAut Y)
        (imaginaryAut canonicalColorCycleCompositionAut Z) =
      imaginaryThreeForm X Y Z := by
  rw [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryAut_preserves_commutatorForm
    canonicalColorCycleCompositionAut X Y Z

theorem canonicalColorReflection_preserves_imaginaryThreeForm
    (X Y Z : Imaginary) :
    imaginaryThreeForm
        (imaginaryAut canonicalColorReflectionCompositionAut X)
        (imaginaryAut canonicalColorReflectionCompositionAut Y)
        (imaginaryAut canonicalColorReflectionCompositionAut Z) =
      imaginaryThreeForm X Y Z := by
  rw [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryAut_preserves_commutatorForm
    canonicalColorReflectionCompositionAut X Y Z

theorem canonicalColorCycle_preserves_imaginaryExteriorEvaluation
    (X Y Z : Imaginary) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![
          imaginaryAut canonicalColorCycleCompositionAut X,
          imaginaryAut canonicalColorCycleCompositionAut Y,
          imaginaryAut canonicalColorCycleCompositionAut Z]) =
      imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![X, Y, Z]) := by
  exact imaginaryAut_preserves_exteriorEvaluation
    canonicalColorCycleCompositionAut X Y Z

theorem canonicalColorReflection_preserves_imaginaryExteriorEvaluation
    (X Y Z : Imaginary) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![
          imaginaryAut canonicalColorReflectionCompositionAut X,
          imaginaryAut canonicalColorReflectionCompositionAut Y,
          imaginaryAut canonicalColorReflectionCompositionAut Z]) =
      imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![X, Y, Z]) := by
  exact imaginaryAut_preserves_exteriorEvaluation
    canonicalColorReflectionCompositionAut X Y Z

end InfoGeometry.Lie.SplitOctonionCanonicalColorImaginaryForm
