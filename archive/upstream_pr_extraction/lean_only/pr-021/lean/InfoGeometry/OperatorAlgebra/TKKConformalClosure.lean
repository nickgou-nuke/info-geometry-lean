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

  /-- Projective conformal boundary / representative socket for compactification. -/
  projectiveNullBoundary : Set W

  /-- The null cone is represented by `ambientQ = 0`. -/
  nullCone_eq_zero_locus :
    ∀ w : W, w ∈ nullCone ↔ ambientQ w = 0

  /--
  The projective boundary lies on the null cone.

  This keeps the “boundary is the projectivized null cone” interpretation
  explicit while still storing a representative socket rather than a quotient.
  -/
  boundary_subset_nullCone :
    projectiveNullBoundary ⊆ nullCone

  /-- Statement that this is the intended conformal compactification. -/
  conformal_compactification_law : Prop

  /-- Proof of the conformal compactification law. -/
  conformal_compactification_law_holds :
    conformal_compactification_law

namespace ConformalCompactificationDatum

variable
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]

variable (C : ConformalCompactificationDatum V W)

/-- Every boundary point is null. -/
theorem boundary_point_null
    {w : W}
    (hw : w ∈ C.projectiveNullBoundary) :
    C.ambientQ w = 0 :=
  (C.nullCone_eq_zero_locus w).mp (C.boundary_subset_nullCone hw)

/-- The stored conformal compactification law is available as a proof. -/
theorem conformal_compactification_valid :
    C.conformal_compactification_law :=
  C.conformal_compactification_law_holds

end ConformalCompactificationDatum

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
  gMinus : Submodule ℝ L

  /-- Structure/derivation piece. -/
  gZero : Submodule ℝ L

  /-- Special-conformal/Jordan-plus piece. -/
  gPlus : Submodule ℝ L

  /-- The intended direct-sum/decomposition law, left abstract at this layer. -/
  decomposition_law : Prop

  /-- Proof of the decomposition law. -/
  decomposition_law_holds :
    decomposition_law

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

  /-- `[g_0, g_0] ⊆ g_0`; the structure/derivation part is a Lie subalgebra. -/
  bracket_zero_zero :
    ∀ X Y : L, X ∈ gZero → Y ∈ gZero → ⁅X, Y⁆ ∈ gZero

  /-- `[g_-1, g_+1] ⊆ g_0`. -/
  bracket_minus_plus :
    ∀ X Y : L, X ∈ gMinus → Y ∈ gPlus → ⁅X, Y⁆ ∈ gZero

namespace TKKThreeGrading

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (G : TKKThreeGrading L)

/-- The stored decomposition law is available as a proof. -/
theorem decomposition_valid :
    G.decomposition_law :=
  G.decomposition_law_holds

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

/-- Re-export: the zero grade is closed under the bracket. -/
theorem zero_zero_mem_zero
    {X Y : L}
    (hX : X ∈ G.gZero)
    (hY : Y ∈ G.gZero) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.bracket_zero_zero X Y hX hY

/-- The negative grade is closed under addition. -/
theorem minus_add_mem
    {X Y : L}
    (hX : X ∈ G.gMinus)
    (hY : Y ∈ G.gMinus) :
    X + Y ∈ G.gMinus :=
  G.gMinus.add_mem hX hY

/-- The zero grade is closed under scalar multiplication. -/
theorem zero_smul_mem
    (a : ℝ)
    {X : L}
    (hX : X ∈ G.gZero) :
    a • X ∈ G.gZero :=
  G.gZero.smul_mem a hX

/-- The positive grade is closed under negation. -/
theorem plus_neg_mem
    {X : L}
    (hX : X ∈ G.gPlus) :
    -X ∈ G.gPlus :=
  G.gPlus.neg_mem hX

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
  TKK identity law.

  A concrete version should identify the bracket-derived triple product on
  `g_-1/g_+1` with the Jordan pair/triple product.
  -/
  tkk_identity_law : Prop

  /-- Proof of the TKK identity law. -/
  tkk_identity_law_holds :
    tkk_identity_law

namespace TKKClosureDatum

variable
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (T : TKKClosureDatum J L)

/-- The stored TKK identity law is available as a proof. -/
theorem tkk_identity_valid :
    T.tkk_identity_law :=
  T.tkk_identity_law_holds

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
  /--
  Infinitesimal action of a generator on states.

  The action is linear in the Lie generator.
  -/
  act : L →ₗ[ℝ] State →ₗ[ℝ] State

  /--
  Compatibility with the Lie bracket.

  This says the action is a Lie representation:
  `act [X,Y] = act X ∘ act Y - act Y ∘ act X`.
  -/
  lie_action_law :
    ∀ X Y : L,
      act ⁅X, Y⁆ =
        (act X).comp (act Y) - (act Y).comp (act X)

namespace TKKInfinitesimalAction

variable
    {L State : Type*} [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]

variable (A : TKKInfinitesimalAction L State)

/-- Re-export the Lie action law. -/
theorem act_lie
    (X Y : L) :
    A.act ⁅X, Y⁆ =
      (A.act X).comp (A.act Y) - (A.act Y).comp (A.act X) :=
  A.lie_action_law X Y

end TKKInfinitesimalAction

/--
A group-level conformal/Mobius lift witness.

This is where `SO(5,5)`, `Pin(5,5)`, projective null-cone action, and discrete
CPT/V4 components should be recorded.
-/
structure ConformalGroupLiftWitness
    (L W : Type*) [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] where
  /-- Infinitesimal action on the ambient conformal carrier, linear in generators. -/
  infinitesimalAction : L →ₗ[ℝ] W →ₗ[ℝ] W

  /-- Predicate for admissible conformal motions. -/
  IsConformalMotion : (W →ₗ[ℝ] W) → Prop

  /-- Integration/lift certificate from Lie algebra to conformal motions. -/
  integrates_to_conformal_group_law : Prop

  /-- Proof of the integration/lift law. -/
  integrates_to_conformal_group_law_holds :
    integrates_to_conformal_group_law

  /-- Optional `Pin(5,5)`/discrete lift certificate. -/
  pin_lift_law : Prop

  /-- Proof of the optional `Pin`/discrete lift law. -/
  pin_lift_law_holds :
    pin_lift_law

namespace ConformalGroupLiftWitness

variable
    {L W : Type*} [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W]

variable (G : ConformalGroupLiftWitness L W)

/-- The stored conformal-group integration law is available as a proof. -/
theorem integrates_to_conformal_group_valid :
    G.integrates_to_conformal_group_law :=
  G.integrates_to_conformal_group_law_holds

/-- The stored optional `Pin`/discrete lift law is available as a proof. -/
theorem pin_lift_valid :
    G.pin_lift_law :=
  G.pin_lift_law_holds

end ConformalGroupLiftWitness

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

  /-- Statement that this is the intended closure-obstruction readout. -/
  closure_defect_law : Prop

  /-- Proof of the closure-defect law. -/
  closure_defect_law_holds :
    closure_defect_law

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

variable (D : TKKClosureDefect L State Defect)

/-- The stored closure-defect law is available as a proof. -/
theorem closure_defect_valid :
    D.closure_defect_law :=
  D.closure_defect_law_holds

end TKKClosureDefect

/--
A curvature readout reconstructed from operator/conformal state data.
-/
structure CurvatureReadout
    (State Geometry : Type*) [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  /-- Effective curvature/geometric readout. -/
  curvature : State → Geometry

  /-- Statement that this is the intended GR/conformal curvature readout. -/
  curvature_law : Prop

  /-- Proof of the curvature law. -/
  curvature_law_holds :
    curvature_law

namespace CurvatureReadout

variable
    {State Geometry : Type*} [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (C : CurvatureReadout State Geometry)

/-- The stored curvature law is available as a proof. -/
theorem curvature_valid :
    C.curvature_law :=
  C.curvature_law_holds

end CurvatureReadout

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

  /-- Abstract linearity/calculus compatibility law. -/
  linearity_law : Prop

  /-- Proof of the abstract linearity/calculus law. -/
  linearity_law_holds :
    linearity_law

namespace DirectionalDerivativeAlong

variable
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (D : DirectionalDerivativeAlong L State Geometry)

/-- The stored linearity/calculus law is available as a proof. -/
theorem linearity_valid :
    D.linearity_law :=
  D.linearity_law_holds

end DirectionalDerivativeAlong

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

/--
If the curvature readout is stationary along `X`, Ricci flux is exactly the
closure defect.
-/
theorem ricciFlux_eq_defect_of_curvature_stationary
    (X : L)
    (s : State)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0) :
    R.ricciFlux X s = R.closureDefect.defect X s := by
  rw [R.ricciFlux_def X s, hstat, zero_add]

/--
If both the curvature variation and the TKK closure defect vanish, Ricci flux
vanishes.
-/
theorem ricciFlux_eq_zero_of_closed_and_stationary
    (X : L)
    (s : State)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0)
    (hclosed :
      R.closureDefect.defect X s = 0) :
    R.ricciFlux X s = 0 := by
  rw [R.ricciFlux_def X s, hstat, hclosed, zero_add]

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
  anomaly_is_closure_defect_law : Prop

  /-- Proof of the anomaly/closure-defect law. -/
  anomaly_is_closure_defect_law_holds :
    anomaly_is_closure_defect_law

namespace TKKConformalClosure

variable
    {J V W L State Geometry : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (C : TKKConformalClosure J V W L State Geometry)

/-- The stored anomaly/closure-defect law is available as a proof. -/
theorem anomaly_is_closure_defect_valid :
    C.anomaly_is_closure_defect_law :=
  C.anomaly_is_closure_defect_law_holds

/-- Ricci flux expands as curvature variation plus closure defect. -/
theorem ricciFlux_def
    (X : L)
    (s : State) :
    C.ricciFlux.ricciFlux X s =
      C.ricciFlux.derivativeAlong.deriv
        C.ricciFlux.curvatureReadout.curvature X s +
      C.ricciFlux.closureDefect.defect X s :=
  C.ricciFlux.ricciFlux_def X s

end TKKConformalClosure

end InfoGeometry.OperatorAlgebra.TKKConformalClosure
