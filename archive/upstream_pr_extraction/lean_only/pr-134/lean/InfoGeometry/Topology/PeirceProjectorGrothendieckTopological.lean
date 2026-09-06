import Mathlib
import InfoGeometry.Canonical.PeirceProjectorGrothendieckClass

/-!
# Topological Grothendieck readout for Peirce projectors

This file packages the additive Grothendieck shadow of the Peirce projector
calculus as a topological readout. The algebraic content remains in
`InfoGeometry.Canonical.PeirceProjectorGrothendieckClass`; the topological
layer only records that the readout is constant.
-/

namespace InfoGeometry.Topology.PeirceProjectorGrothendieckTopological

open InfoGeometry.Canonical.PeirceProjectorGrothendieckClass
open InfoGeometry.Physics.Algebra

noncomputable section

variable {R : Type*} [TopologicalSpace R] [Ring R] [Algebra ℝ R]

instance grothendieckTopologicalSpace : TopologicalSpace (Grothendieck R) := ⊥

/-- The additive Grothendieck readout of the three Peirce projectors. -/
def peirceProjectorGrothendieckReadout (T : R) : Grothendieck R :=
  classOf (projPos T) + classOf (projZero T) + classOf (projNeg T)

omit [TopologicalSpace R] in
@[simp] theorem peirceProjectorGrothendieckReadout_eq
    (T : R) :
    peirceProjectorGrothendieckReadout T = classOf (1 : R) := by
  simpa [peirceProjectorGrothendieckReadout, add_assoc] using
    peirce_projector_class_sum (R := R) T

theorem continuous_peirceProjectorGrothendieckReadout :
    Continuous (peirceProjectorGrothendieckReadout : R → Grothendieck R) := by
  have hconst :
      peirceProjectorGrothendieckReadout = fun _ : R => classOf (1 : R) := by
    funext T
    exact peirceProjectorGrothendieckReadout_eq (R := R) T
  simpa [hconst] using
    (continuous_const :
      Continuous (fun _ : R => (classOf (1 : R) : Grothendieck R)))

/-- The Peirce Grothendieck readout is locally constant. -/
theorem isLocallyConstant_peirceProjectorGrothendieckReadout :
    IsLocallyConstant (peirceProjectorGrothendieckReadout : R → Grothendieck R) := by
  have hconst :
      peirceProjectorGrothendieckReadout = fun _ : R => classOf (1 : R) := by
    funext T
    exact peirceProjectorGrothendieckReadout_eq (R := R) T
  rw [hconst]
  exact IsLocallyConstant.const (X := R) (y := classOf (1 : R))

omit [TopologicalSpace R] in
@[simp] theorem peirceProjectorGrothendieckReadout_tripotent_eq
    (T : R) (_hT : T * T * T = T) :
    peirceProjectorGrothendieckReadout T = classOf (1 : R) := by
  exact peirceProjectorGrothendieckReadout_eq (R := R) T
