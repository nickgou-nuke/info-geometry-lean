/-
InfoGeometry/Geometry/OperatorBregmanDivergence.lean

Bregman divergence on the Drazin regular positive operator cone.

This module bridges the regular operator Fenchel lane to geometric shear
energy. Convexity, strictness, and second-variation/Ricci identification are
proof-carrying data, not placeholder assertions.
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.PO55RicciFlux

noncomputable section

namespace InfoGeometry.Geometry.OperatorBregmanDivergence

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorFenchelRegularCone
open InfoGeometry.OperatorAlgebra

/-- Continuous endomorphisms of the doubled real Krein carrier. -/
abbrev OperatorEnd
    (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. Regular cone points -/

/--
A point of the Drazin regular positive operator cone.

Using a subtype-like structure keeps the Bregman divergence restricted to the
log-admissible regular branch.
-/
structure RegularConePoint
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)) where
  /-- The underlying operator. -/
  op : OperatorEnd E

  /-- Membership in the regular positive cone. -/
  mem : op ∈ regularPositiveConeOmegaD c

namespace RegularConePoint

/-- Coerce a regular cone point to its underlying operator. -/
instance
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)} :
    CoeOut (RegularConePoint c) (OperatorEnd E) where
  coe U := U.op

@[simp]
theorem coe_mk
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (op : OperatorEnd E)
    (hmem : op ∈ regularPositiveConeOmegaD c) :
    (({ op := op, mem := hmem } : RegularConePoint c) : OperatorEnd E) = op :=
  rfl

end RegularConePoint

/-! ## 2. Operatorial Bregman divergence -/

/--
The Bregman divergence between two operators on the regular cone:

`D_Φ(U || V) = Φ(U) - Φ(V) - dΦ_V(U - V)`.

The gradient is supplied as a map

`gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ`.
-/
@[rep_depth operator]
def operatorBregmanDivergence
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U V : RegularConePoint c) : ℝ :=
  operatorFenchelPotentialOnRegularCone (E := E) ω U.op -
    operatorFenchelPotentialOnRegularCone (E := E) ω V.op -
      gradPhi V.op (U.op - V.op)

/--
The Bregman divergence vanishes on the diagonal.
-/
@[simp]
theorem operatorBregmanDivergence_self
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U : RegularConePoint c) :
    operatorBregmanDivergence ω gradPhi U U = 0 := by
  simp [operatorBregmanDivergence]

/--
The oriented/asymmetric Bregman skew.

This is a useful readout for torsion or arrow-of-time effects.
-/
@[rep_depth operator]
def operatorBregmanSkew
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U V : RegularConePoint c) : ℝ :=
  operatorBregmanDivergence ω gradPhi U V -
    operatorBregmanDivergence ω gradPhi V U

/--
The symmetrized Bregman divergence.
-/
@[rep_depth operator]
def operatorBregmanSym
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U V : RegularConePoint c) : ℝ :=
  operatorBregmanDivergence ω gradPhi U V +
    operatorBregmanDivergence ω gradPhi V U

/-! ## 2a. Elementary Bregman identities -/

/--
The Bregman skew changes sign when its arguments are swapped.
-/
@[rep_depth thermo]
theorem operatorBregmanSkew_swap
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U V : RegularConePoint c) :
    operatorBregmanSkew ω gradPhi V U =
      - operatorBregmanSkew ω gradPhi U V := by
  dsimp [operatorBregmanSkew]
  ring

/--
The symmetrized Bregman divergence vanishes on the diagonal.
-/
@[simp]
theorem operatorBregmanSym_self
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (U : RegularConePoint c) :
    operatorBregmanSym ω gradPhi U U = 0 := by
  simp [operatorBregmanSym]

/-! ## 3. Convexity datum for the regular cone -/

/--
Proof-carrying convexity/strictness datum for the operator potential on the
Drazin regular cone.

The first-order lower bound is the exact condition needed to prove Bregman
nonnegativity:

`dΦ_V(U - V) ≤ Φ(U) - Φ(V)`.
-/
structure OperatorBregmanConvexityDatum
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E))
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ) where
  /-- First-order convexity inequality on the regular cone. -/
  first_order_lower_bound :
    ∀ U V : RegularConePoint c,
      gradPhi V.op (U.op - V.op) ≤
        operatorFenchelPotentialOnRegularCone (E := E) ω U.op -
          operatorFenchelPotentialOnRegularCone (E := E) ω V.op

  /--
  Strictness/equality characterization.

  This is stronger than convexity and must be supplied by the concrete strictly
  convex potential.
  -/
  eq_zero_iff :
    ∀ U V : RegularConePoint c,
      operatorBregmanDivergence ω gradPhi U V = 0 ↔ U.op = V.op

namespace OperatorBregmanConvexityDatum

variable
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}

/-- Bregman divergence is nonnegative on the regular positive cone. -/
@[rep_depth thermo]
theorem nonneg
    (C : OperatorBregmanConvexityDatum c ω gradPhi)
    (U V : RegularConePoint c) :
    0 ≤ operatorBregmanDivergence ω gradPhi U V := by
  have h := OperatorBregmanConvexityDatum.first_order_lower_bound C U V
  dsimp [operatorBregmanDivergence]
  linarith

/-- Identity of indiscernibles, supplied by strict convexity. -/
@[rep_depth thermo]
theorem eq_zero_iff_eq
    (C : OperatorBregmanConvexityDatum c ω gradPhi)
    (U V : RegularConePoint c) :
    operatorBregmanDivergence ω gradPhi U V = 0 ↔ U.op = V.op :=
  OperatorBregmanConvexityDatum.eq_zero_iff C U V

/--
The symmetrized Bregman divergence is nonnegative.
-/
@[rep_depth thermo]
theorem sym_nonneg
    (C : OperatorBregmanConvexityDatum c ω gradPhi)
    (U V : RegularConePoint c) :
    0 ≤ operatorBregmanSym ω gradPhi U V := by
  dsimp [operatorBregmanSym]
  have hUV := C.nonneg U V
  have hVU := C.nonneg V U
  linarith

end OperatorBregmanConvexityDatum

/-! ## 4. Cone-preserving modular flows -/

/-- A modular/operator flow preserving the Drazin regular positive cone. -/
structure ModularRegularConeFlow
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)) where
  /-- Flow on operators. -/
  flow : ℝ → OperatorEnd E → OperatorEnd E

  /-- The flow preserves the regular positive cone. -/
  preserves_cone :
    ∀ (t : ℝ) (U : OperatorEnd E),
      U ∈ regularPositiveConeOmegaD c →
        flow t U ∈ regularPositiveConeOmegaD c

  /-- Zero-time identity law. -/
  flow_zero : ∀ U : OperatorEnd E, flow 0 U = U

  /-- Additive flow law. -/
  flow_add :
    ∀ (s t : ℝ) (U : OperatorEnd E),
      flow (s + t) U = flow s (flow t U)

namespace ModularRegularConeFlow

variable {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
variable (F : ModularRegularConeFlow c)

/-- The flow sends a regular cone point to a regular cone point. -/
def mapPoint
    (t : ℝ)
    (U : RegularConePoint c) :
    RegularConePoint c where
  op := F.flow t U.op
  mem := F.preserves_cone t U.op U.mem

@[simp]
theorem mapPoint_zero
    (U : RegularConePoint c) :
    (F.mapPoint 0 U).op = U.op := by
  simp [mapPoint, F.flow_zero]

end ModularRegularConeFlow

/-! ## 5. Modular Bregman energy -/

/--
Bregman energy of the modular shear path:

`E_B(t) = D_Φ(U || σ_t(U))`.
-/
@[rep_depth thermo]
def modularBregmanEnergy
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (F : ModularRegularConeFlow c)
    (U : RegularConePoint c) :
    ℝ → ℝ :=
  fun t => operatorBregmanDivergence ω gradPhi U (F.mapPoint t U)

/-- At time zero, the modular Bregman energy vanishes. -/
@[simp]
theorem modularBregmanEnergy_zero
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (F : ModularRegularConeFlow c)
    (U : RegularConePoint c) :
    modularBregmanEnergy ω gradPhi F U 0 = 0 := by
  simp [modularBregmanEnergy, operatorBregmanDivergence, ModularRegularConeFlow.mapPoint,
    F.flow_zero]

/--
Modular Bregman energy is nonnegative when the potential is convex on the
regular cone.
-/
@[rep_depth thermo]
theorem modularBregmanEnergy_nonneg
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}
    (C : OperatorBregmanConvexityDatum c ω gradPhi)
    (F : ModularRegularConeFlow c)
    (U : RegularConePoint c)
    (t : ℝ) :
    0 ≤ modularBregmanEnergy ω gradPhi F U t :=
  C.nonneg U (F.mapPoint t U)

/-! ## 6. Second-variation socket -/

/--
A second-variation extractor at `t = 0`.

Concrete calculus modules may instantiate this by a second derivative at zero
or by a quadratic-form/Hessian construction.
-/
structure SecondVariationAtZero where
  /-- Second variation of a real path at zero. -/
  eval : (ℝ → ℝ) → ℝ

/-! ## 7. Bregman realization of Ricci flux -/

/--
Bregman realization of Ricci flux.

The scalar Ricci-flux readout from `PO55RicciFlux` is identified with the
second variation of a modular Bregman energy path.

The regular cone point depends on the TKK/Jordan input `(x,y)`. Otherwise this
bridge would force all fluxes to be the same scalar.
-/
structure BregmanRicciFluxBridge
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E))
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (F : ModularRegularConeFlow c)
    (D2 : SecondVariationAtZero)
    (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    (T : TKKLieClosure J L)
    (R : RicciFluxReadout J L Obs T) where
  /-- The regular cone point whose modular shear energy realizes the flux for `(x,y)`. -/
  conePointOf :
    J → J → RegularConePoint c

  /-- Scalar Ricci flux equals the second variation of Bregman shear energy. -/
  flux_eq_bregman_secondVariation :
    ∀ (x y : J),
      R.flux x y =
        D2.eval (modularBregmanEnergy ω gradPhi F (conePointOf x y))

namespace BregmanRicciFluxBridge

variable
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {ω : OperatorEnd E →L[ℝ] ℝ}
    {gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ}
    {F : ModularRegularConeFlow c}
    {D2 : SecondVariationAtZero}
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {T : TKKLieClosure J L}
    {R : RicciFluxReadout J L Obs T}
    (B : BregmanRicciFluxBridge c ω gradPhi F D2 J L Obs T R)

/-- The Bregman energy path realizing the Ricci flux for `(x,y)`. -/
def energyPath
    (x y : J) : ℝ → ℝ :=
  modularBregmanEnergy ω gradPhi F (B.conePointOf x y)

/-- Re-export the Ricci/Bregman bridge law. -/
theorem ricciFlux_eq_secondVariation
    (x y : J) :
    R.flux x y = D2.eval (B.energyPath x y) :=
  B.flux_eq_bregman_secondVariation x y

end BregmanRicciFluxBridge

/-! ## 8. Owner targets -/

/-- Owner target for constructing a convex Bregman geometry on the regular cone. -/
def OperatorBregmanConvexityOwnerTarget
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E))
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ) : Prop :=
  (∀ U V : RegularConePoint c,
    0 ≤ operatorBregmanDivergence ω gradPhi U V) ∧
  (∀ U V : RegularConePoint c,
    operatorBregmanDivergence ω gradPhi U V = 0 ↔ U.op = V.op)

/-- Owner target for a modular Bregman/Ricci bridge. -/
def BregmanRicciFluxBridgeOwnerTarget
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E))
    (ω : OperatorEnd E →L[ℝ] ℝ)
    (gradPhi : OperatorEnd E → OperatorEnd E →L[ℝ] ℝ)
    (F : ModularRegularConeFlow c)
    (D2 : SecondVariationAtZero)
    (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    (T : TKKLieClosure J L)
    (R : RicciFluxReadout J L Obs T) : Prop :=
  ∃ conePointOf : J → J → RegularConePoint c,
    ∀ (x y : J),
      R.flux x y =
        D2.eval (modularBregmanEnergy ω gradPhi F (conePointOf x y))

end InfoGeometry.Geometry.OperatorBregmanDivergence
