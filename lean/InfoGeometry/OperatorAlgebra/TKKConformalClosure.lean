/-
InfoGeometry/OperatorAlgebra/TKKConformalClosure.lean

TKK conformal closure and Ricci-flux sockets.

This file records the Lie-algebraic Tits-Kantor-Koecher closure layer:

  g = g_-1 + g_0 + g_+1

where the plus/minus-one pieces encode Jordan translation/special-conformal directions
and g_0 encodes the derivation/structure algebra.

The conformal group-level interpretation, such as SO(5,5), Pin(5,5), or
projective null-cone Mobius geometry, is kept as an explicit witness layer.

Ricci flux is defined as a covariant readout of the variation of curvature /
closure defect along TKK generators. It is not a bare Ricci tensor until a
connection/curvature contraction API is supplied.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TKKConformalClosure

set_option linter.dupNamespace false

/-! ## 1. Abstract conformal compactification socket -/

/--
A conformal compactification datum.

`V` is the affine/local carrier, morally `R^{4,4}`.

`W` is the ambient conformal carrier, morally `R^{5,5}`.

The null cone and projective boundary are carried as data rather than derived
here.
-/
structure ConformalCompactificationDatum
    (V W : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] where
  /-- Affine chart inclusion. -/
  affineEmbed : V →ₗ[ℝ] W

  /-- Ambient quadratic form, morally signature `(5,5)`. -/
  ambientQ : W → ℝ

  /-- Null cone in the ambient conformal carrier. -/
  nullCone : Set W

  /-- Projective conformal boundary / compactification surface. -/
  projectiveNullBoundary : Set W

  /-- The null cone is represented by `ambientQ = 0`. -/
  nullCone_eq_zero_locus :
    ∀ w : W, w ∈ nullCone ↔ ambientQ w = 0

  /-- Certificate that this is the intended conformal compactification. -/
  conformal_compactification_certificate : Prop

/-! ## 2. TKK 3-grading socket -/

/--
A TKK 3-grading on a Lie algebra.

The intended structure is `L = L_-1 + L_0 + L_+1`.

The bracket rules record the grading behavior. They are proof fields, not bare
theorem claims.
-/
structure TKKThreeGrading
    (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  /-- Translation/Jordan-minus piece. -/
  gMinus : Set L

  /-- Structure/derivation piece. -/
  gZero : Set L

  /-- Special-conformal/Jordan-plus piece. -/
  gPlus : Set L

  /-- The intended direct-sum/decomposition law, left abstract at this layer. -/
  decomposition_law : Prop

  /-- `[g_-1, g_-1] = 0` for the short grading. -/
  bracket_minus_minus :
    ∀ X Y : L, X ∈ gMinus → Y ∈ gMinus → ⁅X, Y⁆ = 0

  /-- `[g_+1, g_+1] = 0` for the short grading. -/
  bracket_plus_plus :
    ∀ X Y : L, X ∈ gPlus → Y ∈ gPlus → ⁅X, Y⁆ = 0

  /-- `[g_0, g_-1] ⊆ g_-1`. -/
  bracket_zero_minus :
    ∀ X Y : L, X ∈ gZero → Y ∈ gMinus → ⁅X, Y⁆ ∈ gMinus

  /-- `[g_0, g_+1] ⊆ g_+1`. -/
  bracket_zero_plus :
    ∀ X Y : L, X ∈ gZero → Y ∈ gPlus → ⁅X, Y⁆ ∈ gPlus

  /-- `[g_-1, g_+1] ⊆ g_0`. -/
  bracket_minus_plus :
    ∀ X Y : L, X ∈ gMinus → Y ∈ gPlus → ⁅X, Y⁆ ∈ gZero

namespace TKKThreeGrading

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (G : TKKThreeGrading L)

/-- Re-export: the negative grade is abelian. -/
theorem minus_minus_eq_zero
    {X Y : L}
    (hX : X ∈ G.gMinus)
    (hY : Y ∈ G.gMinus) :
    ⁅X, Y⁆ = 0 :=
  G.bracket_minus_minus X Y hX hY

/-- Re-export: the positive grade is abelian. -/
theorem plus_plus_eq_zero
    {X Y : L}
    (hX : X ∈ G.gPlus)
    (hY : Y ∈ G.gPlus) :
    ⁅X, Y⁆ = 0 :=
  G.bracket_plus_plus X Y hX hY

/-- Re-export: the mixed outer bracket lands in grade zero. -/
theorem minus_plus_mem_zero
    {X Y : L}
    (hX : X ∈ G.gMinus)
    (hY : Y ∈ G.gPlus) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.bracket_minus_plus X Y hX hY

end TKKThreeGrading

/--
A Jordan-to-TKK closure datum.

`J` is the Jordan-side carrier.

`L` is the Lie algebra produced/used by the TKK construction.
-/
structure TKKClosureDatum
    (J L : Type*) [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  grading :
    TKKThreeGrading L

  /-- Jordan translation embedding into `g_-1`. -/
  toMinus : J →ₗ[ℝ] L

  /-- Jordan special-conformal embedding into `g_+1`. -/
  toPlus : J →ₗ[ℝ] L

  toMinus_mem :
    ∀ x : J, toMinus x ∈ grading.gMinus

  toPlus_mem :
    ∀ x : J, toPlus x ∈ grading.gPlus

  /--
  TKK identity/certificate.

  A concrete version should identify the bracket-derived triple product on
  `g_-1/g_+1` with the Jordan pair/triple product.
  -/
  tkk_identity_certificate : Prop

namespace TKKClosureDatum

variable
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (T : TKKClosureDatum J L)

/-- The embedded Jordan translation lies in the negative grade. -/
theorem toMinus_mem_grade
    (x : J) :
    T.toMinus x ∈ T.grading.gMinus :=
  T.toMinus_mem x

/-- The embedded Jordan special-conformal element lies in the positive grade. -/
theorem toPlus_mem_grade
    (x : J) :
    T.toPlus x ∈ T.grading.gPlus :=
  T.toPlus_mem x

end TKKClosureDatum

/-! ## 3. Conformal action socket -/

/--
A Lie-algebraic conformal action of the TKK algebra on a state space.

This is the infinitesimal version. Group-level `SO(5,5)`/`Pin(5,5)` integration
is a separate witness.
-/
structure TKKInfinitesimalAction
    (L State : Type*) [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State] where
  /-- Infinitesimal action of a generator on states. -/
  act : L → State →ₗ[ℝ] State

  /-- Compatibility with the Lie bracket, left abstract at this layer. -/
  lie_action_law : Prop

/--
A group-level conformal/Mobius lift witness.

This is where `SO(5,5)`, `Pin(5,5)`, projective null-cone action, and discrete
CPT/V4 components should be recorded.
-/
structure ConformalGroupLiftWitness
    (L W : Type*) [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] where
  /-- Infinitesimal action on the ambient conformal carrier. -/
  infinitesimalAction : L → W →ₗ[ℝ] W

  /-- Predicate for admissible conformal motions. -/
  IsConformalMotion : (W →ₗ[ℝ] W) → Prop

  /-- Integration/lift certificate from Lie algebra to conformal motions. -/
  integrates_to_conformal_group : Prop

  /-- Optional `Pin(5,5)`/discrete lift certificate. -/
  pin_lift_certificate : Prop

/-! ## 4. Closure defect and Ricci flux -/

/--
A closure defect readout.

This measures the failure of a transported state/operator to remain inside the
TKK-conformal closure.
-/
structure TKKClosureDefect
    (L State Defect : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Defect] [Module ℝ Defect] where
  /-- Defect readout along a generator. -/
  defect : L → State → Defect

  /-- Certificate that this is the intended closure-obstruction readout. -/
  closure_defect_certificate : Prop

namespace TKKClosureDefect

variable
    {L State Defect : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Defect] [Module ℝ Defect]

/-- Zero-defect predicate for remaining inside the TKK-conformal closure. -/
def IsClosed
    (D : TKKClosureDefect L State Defect)
    (X : L)
    (s : State) : Prop :=
  D.defect X s = 0

end TKKClosureDefect

/--
A curvature readout reconstructed from operator/conformal state data.
-/
structure CurvatureReadout
    (State Geometry : Type*) [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  /-- Effective curvature/geometric readout. -/
  curvature : State → Geometry

  /-- Certificate that this is the intended GR/conformal curvature readout. -/
  curvature_certificate : Prop

/--
Abstract directional derivative of a readout along a TKK generator.

This is deliberately not a full calculus API. A later manifold/calculus layer
can instantiate it by an actual derivative.
-/
structure DirectionalDerivativeAlong
    (L State Geometry : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  deriv :
    (State → Geometry) → L → State → Geometry

  linearity_certificate : Prop

/--
Ricci-flux datum.

`ricciFlux X s` is the flux/readout obtained by differentiating curvature along
a TKK generator and adding the closure defect contribution.
-/
structure TKKRicciFluxDatum
    (L State Geometry : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  curvatureReadout :
    CurvatureReadout State Geometry

  derivativeAlong :
    DirectionalDerivativeAlong L State Geometry

  /-- Closure defect valued in the same geometry/readout type. -/
  closureDefect :
    TKKClosureDefect L State Geometry

  /-- Ricci/conformal flux readout. -/
  ricciFlux :
    L → State → Geometry

  /--
  Defining law:

  Ricci flux is curvature variation plus TKK closure defect.
  -/
  ricciFlux_eq :
    ∀ X : L, ∀ s : State,
      ricciFlux X s =
        derivativeAlong.deriv curvatureReadout.curvature X s +
          closureDefect.defect X s

namespace TKKRicciFluxDatum

variable
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (R : TKKRicciFluxDatum L State Geometry)

/-- Re-export of the Ricci-flux defining law. -/
theorem ricciFlux_def
    (X : L)
    (s : State) :
    R.ricciFlux X s =
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s +
        R.closureDefect.defect X s :=
  R.ricciFlux_eq X s

/--
If the TKK closure defect vanishes, Ricci flux is pure curvature variation.
-/
theorem ricciFlux_eq_derivative_of_closed
    (X : L)
    (s : State)
    (hclosed : R.closureDefect.defect X s = 0) :
    R.ricciFlux X s =
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s := by
  rw [R.ricciFlux_def X s, hclosed, add_zero]

end TKKRicciFluxDatum

/-! ## 5. Full TKK conformal closure package -/

/--
Full TKK conformal closure package.

This is the closed accounting ledger:

* Jordan/base carrier;
* TKK 3-graded Lie algebra;
* conformal compactification;
* infinitesimal action;
* optional group-level lift;
* closure-defect and Ricci-flux readout.
-/
structure TKKConformalClosure
    (J V W L State Geometry : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  compactification :
    ConformalCompactificationDatum V W

  tkk :
    TKKClosureDatum J L

  infinitesimalAction :
    TKKInfinitesimalAction L State

  groupLift :
    ConformalGroupLiftWitness L W

  ricciFlux :
    TKKRicciFluxDatum L State Geometry

  /--
  The GR/Erlanger anomaly is interpreted as the TKK closure defect.
  -/
  anomaly_is_closure_defect_certificate : Prop

end InfoGeometry.OperatorAlgebra.TKKConformalClosure
