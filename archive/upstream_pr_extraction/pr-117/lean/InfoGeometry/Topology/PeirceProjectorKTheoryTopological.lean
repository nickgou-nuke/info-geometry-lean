import Mathlib
import InfoGeometry.Topology.PeirceProjectorKTheoryBridge

/-!
# Topological Peirce projector K-theory readout

This file packages the additive readout from `PeirceProjectorKTheoryBridge`
as a continuous map. The readout is constant after the additive Grothendieck
identity is applied, so no stronger K-theoretic claim is made here.
-/

namespace InfoGeometry.Topology.PeirceProjectorKTheoryTopological

open InfoGeometry.Canonical.PeirceProjectorGrothendieckClass
open InfoGeometry.Topology.PeirceProjectorKTheoryBridge
open InfoGeometry.Physics.Algebra

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The Peirce K-theory readout through an additive homomorphism. -/
def peirceKTheoryReadout {G : Type*} [AddCommGroup G]
    (φ : Grothendieck R →+ G) (T : R) : G :=
  φ (classOf (projPos T)) + φ (classOf (projZero T)) + φ (classOf (projNeg T))

@[simp] theorem peirceKTheoryReadout_eq
    {G : Type*} [AddCommGroup G] (φ : Grothendieck R →+ G) (T : R) :
    peirceKTheoryReadout (R := R) φ T = φ (classOf (1 : R)) := by
  simpa [peirceKTheoryReadout, add_assoc] using
    peirce_ktheory_readout_sum (φ := φ) (T := T)

theorem continuous_peirceKTheoryReadout
    {G : Type*} [TopologicalSpace R] [TopologicalSpace G] [AddCommGroup G]
    (φ : Grothendieck R →+ G) :
    Continuous (peirceKTheoryReadout (R := R) (G := G) φ) := by
  have hconst :
      peirceKTheoryReadout (R := R) (G := G) φ =
        fun _ : R => φ (classOf (1 : R)) := by
    funext T
    exact peirceKTheoryReadout_eq (R := R) (G := G) φ T
  simpa [hconst] using
    (continuous_const :
      Continuous (fun _ : R => (φ (classOf (1 : R)) : G)))

theorem isLocallyConstant_peirceKTheoryReadout
    {G : Type*} [TopologicalSpace R] [TopologicalSpace G] [AddCommGroup G]
    (φ : Grothendieck R →+ G) :
    IsLocallyConstant (peirceKTheoryReadout (R := R) (G := G) φ) := by
  have hconst :
      peirceKTheoryReadout (R := R) (G := G) φ =
        fun _ : R => φ (classOf (1 : R)) := by
    funext T
    exact peirceKTheoryReadout_eq (R := R) (G := G) φ T
  rw [hconst]
  exact IsLocallyConstant.const (X := R) (y := φ (classOf (1 : R)))
