/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

/-!
# Topological Family of Cubic Klein-Bottle Charges

This module defines the discrete parameter subtype `CubicRootParameter := {w : ℂ // w ^ 3 = 1}`
and the family `cubicRootChargeReadout : CubicRootParameter → ColourOperator`, and proves
its evaluation, continuity, local constancy, order-three law `cubicRootChargeReadout_cube`,
and chiral reflection conjugation `chiralExchange_conj_cubicRootChargeReadout`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.KleinBottleCyclotomicChiralLift`:
    `A2ColourFiber`, `cubicCharge`, `chiralExchange`, `cubicCharge_cube`,
    `chiralExchange_conj_cubicCharge`.
- BUCKET 2 (Deconfabulation):
  * All algebraic order-three, chiral conjugation, and topological continuity laws
    are proved via explicit unfolding and reduction to the canonical Klein-bottle lift.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `CubicRootParameter`, `ColourFiber`, `ColourOperator`, `cubicRootChargeReadout`.
  * `cubicRootChargeReadout_apply`, `continuous_cubicRootChargeReadout`,
    `isLocallyConstant_cubicRootChargeReadout`, `cubicRootChargeReadout_cube`,
    `chiralExchange_conj_cubicRootChargeReadout`.
-/

namespace InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

open InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

noncomputable section

/-- Subtype of complex cube roots of unity `{w : ℂ // w ^ 3 = 1}`. -/
abbrev CubicRootParameter := {w : ℂ // w ^ 3 = 1}

/-- Complex `A2` colour fiber `Fin 3 → ℂ`. -/
abbrev ColourFiber :=
  InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.A2ColourFiber ℂ

/-- Linear endomorphism algebra of the complex `A2` colour fiber. -/
abbrev ColourOperator := ColourFiber →ₗ[ℂ] ColourFiber

instance cubicRootParameterTopologicalSpace :
    TopologicalSpace CubicRootParameter := ⊥

instance cubicRootParameterDiscreteTopology :
    DiscreteTopology CubicRootParameter := DiscreteTopology.mk (Eq.refl _)

instance colourOperatorTopologicalSpace :
    TopologicalSpace ColourOperator := ⊥

instance colourOperatorDiscreteTopology :
    DiscreteTopology ColourOperator := DiscreteTopology.mk (Eq.refl _)

/-- Cubic colour charge operator as a continuous family over `CubicRootParameter`. -/
def cubicRootChargeReadout (q : CubicRootParameter) : ColourOperator :=
  InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge q.1

/-- Explicit evaluation of `cubicRootChargeReadout q`. -/
@[simp] theorem cubicRootChargeReadout_apply (q : CubicRootParameter) :
    cubicRootChargeReadout q =
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge q.1 := by
  unfold cubicRootChargeReadout
  exact Eq.refl _

/-- Continuity of `cubicRootChargeReadout` on the discrete parameter subtype. -/
theorem continuous_cubicRootChargeReadout :
    Continuous cubicRootChargeReadout := by
  exact continuous_of_discreteTopology

/-- Local constancy of `cubicRootChargeReadout` on the discrete parameter subtype. -/
theorem isLocallyConstant_cubicRootChargeReadout :
    IsLocallyConstant cubicRootChargeReadout := by
  intro s
  exact isOpen_discrete _

/-- Every member of the family `cubicRootChargeReadout` has order three. -/
theorem cubicRootChargeReadout_cube (q : CubicRootParameter) :
    (cubicRootChargeReadout q).comp
        ((cubicRootChargeReadout q).comp (cubicRootChargeReadout q)) =
      LinearMap.id := by
  unfold cubicRootChargeReadout
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge_cube
    q.1 q.2

/-- Chiral reflection conjugates every cubic charge in the family to its square. -/
theorem chiralExchange_conj_cubicRootChargeReadout
    (q : CubicRootParameter) :
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
      (K := ℂ)).comp
        ((cubicRootChargeReadout q).comp
          (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
            (K := ℂ))) =
      (cubicRootChargeReadout q).comp (cubicRootChargeReadout q) := by
  unfold cubicRootChargeReadout
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange_conj_cubicCharge
    q.1 q.2

end
end InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
