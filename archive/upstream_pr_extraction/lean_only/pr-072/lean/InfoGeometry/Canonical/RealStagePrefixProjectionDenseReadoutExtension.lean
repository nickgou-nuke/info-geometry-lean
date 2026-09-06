import InfoGeometry.Canonical.RealStagePrefixProjectionReadout

/-!
# Dense-readout uniqueness for the real prefix completion

The explicit finite-prefix readout is dense in the real unit interval.  This
owner records the corresponding uniqueness principle for continuous maps into
Hausdorff targets.  It is a topological extension theorem only; it does not
assert a C*-completion, a state-space theorem, or K-theory.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open RealUHFProjectionRankRealCompletionTopological

theorem prefixRankReadout_dense_equalizer
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (g h : RealUnitInterval → Y)
    (hg : Continuous g) (hh : Continuous h)
    (H : g ∘ prefixRankReadout = h ∘ prefixRankReadout) :
    g = h := by
  exact DenseRange.equalizer denseRange_prefixRankReadout hg hh H

theorem prefixRankReadoutTopCatHom_right_cancel
    {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (g h : TopCat.of RealUnitInterval ⟶ TopCat.of Y)
    (H : prefixRankReadoutTopCatHom ≫ g =
      prefixRankReadoutTopCatHom ≫ h) :
    g = h := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have hgh : (g : RealUnitInterval → Y) = h :=
    prefixRankReadout_dense_equalizer
      g.hom h.hom g.hom.continuous h.hom.continuous (by
        funext p
        have hp := congrArg (fun q => q p) H
        simpa only [TopCat.comp_app] using hp)
  exact congrFun hgh x

end InfoGeometry.Canonical

end
