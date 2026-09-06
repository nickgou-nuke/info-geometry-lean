import InfoGeometry.Topology.KTheoryO2
import InfoGeometry.Topology.PeirceProjectorGrothendieckTopological
import InfoGeometry.Canonical.CuntzGrothendieckShadow

/-!
# K₀(O₂) and additive Grothendieck readouts

This file combines existing readouts without identifying their carriers.
`Grothendieck A` is the additive completion of the underlying additive
monoid, whereas `K0_O_2` is the existing `ZMod 1` readout.  The bridge below
therefore records their simultaneous values, but makes no unsupported claim
that the two types are equivalent.
-/

namespace InfoGeometry.Topology.KTheoryO2GrothendieckBridge

open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology.KTheory
open InfoGeometry.Topology.PeirceProjectorGrothendieckTopological

noncomputable section

variable {R : Type*} [TopologicalSpace R] [Ring R] [Algebra ℝ R]
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The pair of already-defined additive Grothendieck shadows. -/
def peirceCuntzGrothendieckReadout
    (T : R) (O2 : CuntzTwoAlgebra A) :
    Grothendieck R × Grothendieck A :=
  (peirceProjectorGrothendieckReadout T,
    InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf
      (O2.S1 * O2.S1_star) +
      InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf
        (O2.S2 * O2.S2_star))

omit [TopologicalSpace R] in
@[simp] theorem peirceCuntzGrothendieckReadout_eq
    (T : R) (O2 : CuntzTwoAlgebra A) :
    peirceCuntzGrothendieckReadout T O2 =
      (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
          (1 : R),
        InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf (1 : A)) := by
  change
    (peirceProjectorGrothendieckReadout T,
        InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf
          (O2.S1 * O2.S1_star) +
          InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf
            (O2.S2 * O2.S2_star)) = _
  rw [peirceProjectorGrothendieckReadout_eq,
    InfoGeometry.Canonical.CuntzGrothendieckShadow.cuntz_projector_class_sum]

omit [TopologicalSpace R] in
theorem peirceCuntzGrothendieckReadout_fst
    (T : R) (O2 : CuntzTwoAlgebra A) :
    (peirceCuntzGrothendieckReadout T O2).1 =
      InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (1 : R) := by
  rw [peirceCuntzGrothendieckReadout_eq]

omit [TopologicalSpace R] in
theorem peirceCuntzGrothendieckReadout_snd
    (T : R) (O2 : CuntzTwoAlgebra A) :
    (peirceCuntzGrothendieckReadout T O2).2 =
      InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf (1 : A) := by
  rw [peirceCuntzGrothendieckReadout_eq]

/-- The independent `K₀(O₂)` readout remains the trivial `ZMod 1` group. -/
theorem k0_o2_readout_eq_zero (x : K0_O_2) : x = 0 :=
  k0_o2_is_trivial x

omit [TopologicalSpace R] in
theorem peirceCuntz_readout_and_k0_o2
    (T : R) (O2 : CuntzTwoAlgebra A) (x : K0_O_2) :
    peirceCuntzGrothendieckReadout T O2 =
        (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
            (1 : R),
          InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf (1 : A)) ∧
      x = 0 := by
  exact ⟨peirceCuntzGrothendieckReadout_eq T O2,
    k0_o2_readout_eq_zero x⟩

/-- The paired Peirce/Cuntz Grothendieck readout is locally constant in `T`. -/
theorem isLocallyConstant_peirceCuntzGrothendieckReadout
    (O2 : CuntzTwoAlgebra A) :
    IsLocallyConstant (fun T : R => peirceCuntzGrothendieckReadout T O2) := by
  have hconst :
      (fun T : R => peirceCuntzGrothendieckReadout T O2) =
        fun _ : R =>
          (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
              (1 : R),
            InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf (1 : A)) := by
    funext T
    exact peirceCuntzGrothendieckReadout_eq (T := T) (O2 := O2)
  rw [hconst]
  exact IsLocallyConstant.const
    (y := (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (1 : R),
      InfoGeometry.Canonical.CuntzGrothendieckShadow.classOf (1 : A)))

/-- The paired Peirce/Cuntz Grothendieck readout is continuous in `T`. -/
theorem continuous_peirceCuntzGrothendieckReadout
    (O2 : CuntzTwoAlgebra A) :
    Continuous (fun T : R => peirceCuntzGrothendieckReadout T O2) := by
  exact (isLocallyConstant_peirceCuntzGrothendieckReadout (R := R) (A := A) O2).continuous

end

end InfoGeometry.Topology.KTheoryO2GrothendieckBridge
