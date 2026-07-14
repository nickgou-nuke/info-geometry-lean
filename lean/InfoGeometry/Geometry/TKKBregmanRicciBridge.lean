/-
InfoGeometry/Geometry/TKKBregmanRicciBridge.lean

Bridge from TKK Ricci flux to Bregman second variation.

This module connects the algebraic/conformal TKK closure ledger to the
information-geometric Bregman shear ledger.

It is the adapter for the newer
`OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum` socket. It does not
replace the older repo-native `BregmanRicciFluxBridge` already defined in
`Geometry.OperatorBregmanDivergence` for the `PO55RicciFlux` /
`TKKLieClosure` lane.

It does not assert that Ricci flux is always a Bregman Hessian. It packages the
concrete identification as proof-carrying bridge data.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TKKConformalClosure
import InfoGeometry.Geometry.OperatorBregmanDivergence

noncomputable section

namespace InfoGeometry.Geometry.TKKBregmanRicciBridge

open InfoGeometry.Geometry.OperatorBregmanDivergence
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorFenchelRegularCone
open InfoGeometry.OperatorAlgebra.TKKConformalClosure

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. TKK/Bregman bridge datum -/

/--
A bridge from TKK Ricci flux to Bregman second variation.

`State` is the state space used by the TKK Ricci-flux readout.

`Geometry` is the curvature/flux codomain.

The bridge supplies:

* a way to associate a TKK state to each regular-cone operator point;
* a TKK generator associated to that point;
* a scalar readout from the geometric Ricci-flux value;
* the equality between scalar Ricci flux and the Bregman second variation.
-/
structure Bridge
    (c : CertifiedModularReduction
      (E := InfoGeometry.Krein.DoubledSpace E))
    (ω :
      OperatorEnd E →L[ℝ] ℝ)
    (gradPhi :
      OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (F : ModularRegularConeFlow (E := E) c)
    (D2 : SecondVariationAtZero)
    (L State Geometry : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (R : TKKRicciFluxDatum L State Geometry) where
  /-- Assign a TKK state to a regular operator point. -/
  stateOf :
    RegularConePoint (E := E) c
      → State
  /-- Assign a TKK generator to a regular operator point. -/
  generatorOf :
    RegularConePoint (E := E) c
      → L
  /-- Scalar readout of a curvature/flux value. -/
  fluxScalar :
    Geometry → ℝ
  /--
  Bridge law:

  scalar TKK Ricci flux equals the Bregman second variation of the modular
  shear energy.
  -/
  scalar_ricciFlux_eq_bregman_secondVariation :
    ∀ U : RegularConePoint (E := E) c,
      fluxScalar
          (R.ricciFlux (generatorOf U) (stateOf U))
        =
      D2.eval (modularBregmanEnergy (E := E) ω gradPhi F U)

namespace Bridge

variable
    {c : CertifiedModularReduction
      (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}
    {F : ModularRegularConeFlow (E := E) c}
    {D2 : SecondVariationAtZero}
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {R : TKKRicciFluxDatum L State Geometry}

variable
    (B : Bridge
      (E := E) c ω gradPhi F D2 L State Geometry R)

/-- Re-export the TKK/Bregman bridge law. -/
theorem ricciFlux_eq_bregman_secondVariation
    (U : RegularConePoint (E := E) c) :
    B.fluxScalar
        (R.ricciFlux (B.generatorOf U) (B.stateOf U))
      =
    D2.eval (modularBregmanEnergy (E := E) ω gradPhi F U) :=
  B.scalar_ricciFlux_eq_bregman_secondVariation U

/--
If the TKK closure defect vanishes, the Bregman second variation is identified
with the scalar curvature-variation readout.
-/
theorem scalar_curvatureVariation_eq_bregman_of_closed
    (U : RegularConePoint (E := E) c)
    (hclosed :
      R.closureDefect.defect (B.generatorOf U) (B.stateOf U) = 0) :
    B.fluxScalar
        (R.derivativeAlong.deriv
          R.curvatureReadout.curvature
          (B.generatorOf U)
          (B.stateOf U))
      =
    D2.eval (modularBregmanEnergy (E := E) ω gradPhi F U) := by
  have hflux :=
    B.ricciFlux_eq_bregman_secondVariation U
  have hricci :
      R.ricciFlux (B.generatorOf U) (B.stateOf U) =
        R.derivativeAlong.deriv
          R.curvatureReadout.curvature
          (B.generatorOf U)
          (B.stateOf U) :=
    R.ricciFlux_eq_derivative_of_closed
      (B.generatorOf U) (B.stateOf U) hclosed
  rw [hricci] at hflux
  exact hflux

/--
If curvature is stationary along the TKK generator, the Bregman second
variation is identified with the scalar closure-defect readout.
-/
theorem scalar_closureDefect_eq_bregman_of_curvature_stationary
    (U : RegularConePoint (E := E) c)
    (hstat :
      R.derivativeAlong.deriv
          R.curvatureReadout.curvature
          (B.generatorOf U)
          (B.stateOf U)
        = 0) :
    B.fluxScalar
        (R.closureDefect.defect
          (B.generatorOf U)
          (B.stateOf U))
      =
    D2.eval (modularBregmanEnergy (E := E) ω gradPhi F U) := by
  have hflux :=
    B.ricciFlux_eq_bregman_secondVariation U
  have hricci :
      R.ricciFlux (B.generatorOf U) (B.stateOf U) =
        R.closureDefect.defect
          (B.generatorOf U)
          (B.stateOf U) :=
    R.ricciFlux_eq_defect_of_curvature_stationary
      (B.generatorOf U) (B.stateOf U) hstat
  rw [hricci] at hflux
  exact hflux

end Bridge

/-! ## 2. Owner target -/

/-- Owner target for installing a TKK/Bregman Ricci-flux bridge. -/
def TKKBregmanRicciBridgeOwnerTarget
    (c : CertifiedModularReduction
      (E := InfoGeometry.Krein.DoubledSpace E))
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (F : ModularRegularConeFlow (E := E) c)
    (D2 : SecondVariationAtZero)
    (L State Geometry : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (R : TKKRicciFluxDatum L State Geometry) : Prop :=
  Nonempty
    (Bridge
      (E := E) c ω gradPhi F D2 L State Geometry R)

end InfoGeometry.Geometry.TKKBregmanRicciBridge
