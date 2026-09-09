import Mathlib
import InfoGeometry.Canonical.CuntzGrothendieckShadow

/-!
# Topological Grothendieck readout for the Cuntz shadow

This file packages the additive Grothendieck shadow of the Cuntz projection
completeness identity as a topological readout. The source and target are given
the discrete topology, so continuity is bookkeeping only.
-/

namespace InfoGeometry.Topology.CuntzGrothendieckShadowTopological

open InfoGeometry.Canonical.CuntzGrothendieckShadow
open InfoGeometry.Physics.Algebra

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

instance sourceTopologicalSpace : TopologicalSpace (CuntzTwoAlgebra A) := ⊥
instance sourceDiscreteTopology : DiscreteTopology (CuntzTwoAlgebra A) :=
  ⟨rfl⟩

instance grothendieckTopologicalSpace : TopologicalSpace (Grothendieck A) := ⊥
instance grothendieckDiscreteTopology : DiscreteTopology (Grothendieck A) :=
  ⟨rfl⟩

/-- The Cuntz additive Grothendieck readout. -/
def cuntzGrothendieckReadout (O2 : CuntzTwoAlgebra A) : Grothendieck A :=
  classOf (O2.S1 * O2.S1_star) + classOf (O2.S2 * O2.S2_star)

@[simp] theorem cuntzGrothendieckReadout_eq
    (O2 : CuntzTwoAlgebra A) :
    cuntzGrothendieckReadout O2 = classOf (1 : A) := by
  simpa [cuntzGrothendieckReadout, add_assoc] using
    (cuntz_projector_class_sum (A := A) O2)

theorem continuous_cuntzGrothendieckReadout :
    Continuous (cuntzGrothendieckReadout : CuntzTwoAlgebra A → Grothendieck A) := by
  have hconst :
      cuntzGrothendieckReadout = fun _ : CuntzTwoAlgebra A => (classOf (1 : A) : Grothendieck A) := by
    funext O2
    exact cuntzGrothendieckReadout_eq (A := A) O2
  simpa [hconst] using
    (continuous_of_discreteTopology :
      Continuous (fun _ : CuntzTwoAlgebra A => (classOf (1 : A) : Grothendieck A)))

/-- The Cuntz Grothendieck readout is locally constant. -/
theorem isLocallyConstant_cuntzGrothendieckReadout :
    IsLocallyConstant (cuntzGrothendieckReadout : CuntzTwoAlgebra A → Grothendieck A) := by
  have hconst :
      cuntzGrothendieckReadout = fun _ : CuntzTwoAlgebra A => (classOf (1 : A) : Grothendieck A) := by
    funext O2
    exact cuntzGrothendieckReadout_eq (A := A) O2
  rw [hconst]
  exact IsLocallyConstant.const (X := CuntzTwoAlgebra A) (y := classOf (1 : A))
