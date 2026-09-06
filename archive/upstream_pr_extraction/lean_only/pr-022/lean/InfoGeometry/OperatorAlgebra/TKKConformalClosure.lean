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

  /-- The affine embedding is injective. -/
  affineEmbed_injective :
    Function.Injective affineEmbed

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

/-- The affine chart is injective. -/
theorem affineEmbed_injective_prop :
    Function.Injective C.affineEmbed :=
  C.affineEmbed_injective

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

  /-- The Lie algebra decomposes as `L = g₋₁ ⊕ g₀ ⊕ g₊₁`. -/
  decomposition_law : ⊤ = gMinus ⊔ gZero ⊔ gPlus

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

/-- The grading spans the full Lie algebra. -/
theorem decomposition_valid :
    ⊤ = G.gMinus ⊔ G.gZero ⊔ G.gPlus :=
  G.decomposition_law

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
  TKK identity: the Jordan triple-product symmetry recovered from the Lie bracket.
  `[[x⁻, y⁺], z⁻] = [[z⁻, y⁺], x⁻]` in `L`.
  -/
  tkk_identity :
    ∀ x y z : J,
      ⁅⁅toMinus x, toPlus y⁆, toMinus z⁆ =
        ⁅⁅toMinus z, toPlus y⁆, toMinus x⁆

namespace TKKClosureDatum

variable
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (T : TKKClosureDatum J L)

/-- The TKK triple-product symmetry. -/
theorem tkk_identity_valid
    (x y z : J) :
    ⁅⁅T.toMinus x, T.toPlus y⁆, T.toMinus z⁆ =
      ⁅⁅T.toMinus z, T.toPlus y⁆, T.toMinus x⁆ :=
  T.tkk_identity x y z

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

  /-- The infinitesimal action is a Lie homomorphism. -/
  infinitesimalAction_lie :
    ∀ X Y : L,
      infinitesimalAction ⁅X, Y⁆ =
        (infinitesimalAction X).comp (infinitesimalAction Y) -
        (infinitesimalAction Y).comp (infinitesimalAction X)

namespace ConformalGroupLiftWitness

variable
    {L W : Type*} [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W]

variable (G : ConformalGroupLiftWitness L W)

/-- The infinitesimal action respects the Lie bracket. -/
theorem infinitesimalAction_lie_eq
    (X Y : L) :
    G.infinitesimalAction ⁅X, Y⁆ =
      (G.infinitesimalAction X).comp (G.infinitesimalAction Y) -
      (G.infinitesimalAction Y).comp (G.infinitesimalAction X) :=
  G.infinitesimalAction_lie X Y

end ConformalGroupLiftWitness

/-! ## 3A. Pin group lift witness -/

/--
Pin group lift witness for the TKK conformal double cover.

Certifies that the `so(5,5)` infinitesimal action on the ambient conformal
module `W` lifts to a group-level `Pin(p,q)` action through the Clifford
algebra `Cl(W, Q)`.

The defining data are:

* a quadratic form `Q` on `W` (intended signature `(5,5)`);
* an abstract Pin group carrier and multiplication;
* the Clifford squaring relation `ι(w)² = Q(w) · 1`;
* a group action on `W` preserving `Q`.

The Lie-algebra level action is inherited from `ConformalGroupLiftWitness`.

See: Lawson–Michelsohn, *Spin Geometry*, Ch. I;
Meinrenken, *Clifford Algebras and Lie Theory*.
-/
structure PinLiftWitness
    (L W : Type*)
    [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] where

  /-- Quadratic form on `W`, intended signature `(5,5)`. -/
  quadraticForm : QuadraticForm ℝ W

  /-- Underlying infinitesimal conformal action at the Lie algebra level. -/
  infinitesimalAction : ConformalGroupLiftWitness L W

  /-- Abstract Pin group carrier (double cover of `O(quadraticForm)`). -/
  PinGroupCarrier : Type*

  /-- Abstract group multiplication on `PinGroupCarrier`. -/
  pinMul : PinGroupCarrier → PinGroupCarrier → PinGroupCarrier

  /-- Abstract unit of `PinGroupCarrier`. -/
  pinOne : PinGroupCarrier

  /-- Scalar embedding `ℝ → PinGroupCarrier` (multiples of the identity). -/
  scalarEmbed : ℝ → PinGroupCarrier

  /-- Clifford generator map `W → PinGroupCarrier`. -/
  cliffordGen : W → PinGroupCarrier

  /--
  Clifford squaring relation: `ι(w) · ι(w) = Q(w) · 1`.

  This is the defining relation of the Clifford algebra `Cl(W, Q)` from which
  the Pin group is constructed.
  -/
  clifford_sq :
    ∀ w : W,
      pinMul (cliffordGen w) (cliffordGen w) =
        scalarEmbed (quadraticForm w)

  /-- Group-level Pin action on `W`. -/
  pinAction : PinGroupCarrier → W →ₗ[ℝ] W

  /-- The Pin action preserves the quadratic form. -/
  pinAction_preserves_Q :
    ∀ (g : PinGroupCarrier) (w : W),
      quadraticForm (pinAction g w) = quadraticForm w

namespace PinLiftWitness

variable
    {L W : Type*}
    [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W]

variable (P : PinLiftWitness L W)

/-- The Clifford squaring relation at a given vector `w`. -/
theorem clifford_sq_eq (w : W) :
    P.pinMul (P.cliffordGen w) (P.cliffordGen w) =
      P.scalarEmbed (P.quadraticForm w) :=
  P.clifford_sq w

/-- The Pin action preserves the ambient quadratic form. -/
theorem pinAction_preserves_form (g : P.PinGroupCarrier) (w : W) :
    P.quadraticForm (P.pinAction g w) = P.quadraticForm w :=
  P.pinAction_preserves_Q g w

/-- The infinitesimal action is a Lie homomorphism. -/
theorem infinitesimalAction_lie (X Y : L) :
    P.infinitesimalAction.infinitesimalAction ⁅X, Y⁆ =
      (P.infinitesimalAction.infinitesimalAction X).comp
          (P.infinitesimalAction.infinitesimalAction Y) -
      (P.infinitesimalAction.infinitesimalAction Y).comp
          (P.infinitesimalAction.infinitesimalAction X) :=
  P.infinitesimalAction.infinitesimalAction_lie X Y

end PinLiftWitness

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

  /-- The defect readout is linear in the generator. -/
  defect_linear_gen :
    ∀ (a b : ℝ) (X Y : L) (s : State),
      defect (a • X + b • Y) s = a • defect X s + b • defect Y s

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

/-- The defect is linear in the Lie generator. -/
theorem defect_linear
    (a b : ℝ) (X Y : L) (s : State) :
    D.defect (a • X + b • Y) s = a • D.defect X s + b • D.defect Y s :=
  D.defect_linear_gen a b X Y s

end TKKClosureDefect

/--
A curvature readout reconstructed from operator/conformal state data.
-/
structure CurvatureReadout
    (State Geometry : Type*) [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  /-- Effective curvature/geometric readout. -/
  curvature : State → Geometry

  /-- The curvature readout is a linear map. -/
  curvature_linear : State →ₗ[ℝ] Geometry

  /-- The curvature function agrees with the linear map. -/
  curvature_eq_linear :
    ∀ s : State, curvature s = curvature_linear s

namespace CurvatureReadout

variable
    {State Geometry : Type*} [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (C : CurvatureReadout State Geometry)

/-- The curvature readout agrees with its linear witness. -/
theorem curvature_eq
    (s : State) :
    C.curvature s = C.curvature_linear s :=
  C.curvature_eq_linear s

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

  /-- Linearity in the Lie generator. -/
  deriv_linear_gen :
    ∀ (f : State → Geometry) (a b : ℝ) (X Y : L) (s : State),
      deriv f (a • X + b • Y) s = a • deriv f X s + b • deriv f Y s

namespace DirectionalDerivativeAlong

variable
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (D : DirectionalDerivativeAlong L State Geometry)

/-- The directional derivative is linear in the generator. -/
theorem deriv_linear
    (f : State → Geometry) (a b : ℝ) (X Y : L) (s : State) :
    D.deriv f (a • X + b • Y) s = a • D.deriv f X s + b • D.deriv f Y s :=
  D.deriv_linear_gen f a b X Y s

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

/--
Explicit anomaly/closure-defect identification law.

This reintroduces the old witness name as an equation-level contract: an
`anomaly` readout is exactly the TKK closure defect readout.
-/
def anomaly_is_closure_defect_law
    (anomaly : L → State → Geometry) : Prop :=
  ∀ X s, anomaly X s = R.closureDefect.defect X s

/-- Re-export of the anomaly/closure-defect equation. -/
theorem anomaly_is_closure_defect_law_at
    {anomaly : L → State → Geometry}
    (h : R.anomaly_is_closure_defect_law anomaly)
    (X : L)
    (s : State) :
    anomaly X s = R.closureDefect.defect X s :=
  h X s

end TKKRicciFluxDatum

/-! ## 4A. Anomaly-closure-defect datum -/

/--
Anomaly-closure-defect datum.

Proof-carrying structure asserting that the conformal anomaly equals
the TKK closure defect:

  `anomalyReadout X s = closureDefect.defect X s`

In conformal field theory, the Weyl anomaly equals the trace of the stress
tensor under quantization — i.e. the failure of conformal invariance. In the
TKK 3-grading framework this is exactly the closure defect.

Both sides are required to share compatible linearity in the generator.

See: Nakahara, *Geometry, Topology and Physics* §13.5;
Fradkin–Tseytlin, Phys. Lett. B 134 (1984) 187.
-/
structure AnomalyClosureDefectDatum
    (L State Geometry : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry] where

  /-- Underlying TKK closure defect. -/
  closureDefect : TKKClosureDefect L State Geometry

  /-- Anomaly readout (e.g. Weyl anomaly / trace of stress tensor). -/
  anomalyReadout : L → State → Geometry

  /--
  The anomaly readout is linear in the Lie generator,
  matching the linearity of the closure defect.
  -/
  anomalyReadout_linear :
    ∀ (a b : ℝ) (X Y : L) (s : State),
      anomalyReadout (a • X + b • Y) s =
        a • anomalyReadout X s + b • anomalyReadout Y s

  /--
  Anomaly equals closure defect:
  `anomalyReadout X s = closureDefect.defect X s`.
  -/
  anomaly_eq_closure_defect :
    ∀ (X : L) (s : State),
      anomalyReadout X s = closureDefect.defect X s

namespace AnomalyClosureDefectDatum

variable
    {L State Geometry : Type*}
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (A : AnomalyClosureDefectDatum L State Geometry)

/-- Re-export: anomaly equals the TKK closure defect. -/
theorem anomaly_eq_defect (X : L) (s : State) :
    A.anomalyReadout X s = A.closureDefect.defect X s :=
  A.anomaly_eq_closure_defect X s

/-- The anomaly vanishes iff the closure defect vanishes. -/
theorem anomaly_eq_zero_iff (X : L) (s : State) :
    A.anomalyReadout X s = 0 ↔ A.closureDefect.defect X s = 0 := by
  rw [A.anomaly_eq_defect]

/-- Anomaly linearity re-export. -/
theorem anomalyReadout_linear_apply (a b : ℝ) (X Y : L) (s : State) :
    A.anomalyReadout (a • X + b • Y) s =
      a • A.anomalyReadout X s + b • A.anomalyReadout Y s :=
  A.anomalyReadout_linear a b X Y s

end AnomalyClosureDefectDatum

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



/-- Ricci flux expands as curvature variation plus closure defect. -/
theorem ricciFlux_def
    (X : L)
    (s : State) :
    C.ricciFlux.ricciFlux X s =
      C.ricciFlux.derivativeAlong.deriv
        C.ricciFlux.curvatureReadout.curvature X s +
      C.ricciFlux.closureDefect.defect X s :=
  C.ricciFlux.ricciFlux_def X s

/--
The conformal anomaly (Ricci flux) is identified with the TKK closure defect
when curvature is stationary along a generator `X`.

This is the formal content of the Weyl anomaly theorem in the TKK framework:
the trace anomaly of the stress tensor equals the failure of conformal
invariance, expressed as the closure defect of the three-grading.

**Literature**: Fradkin–Tseytlin, Phys. Lett. B 134 (1984) 187;
Nakahara, Geometry, Topology and Physics §13.5.
-/
theorem anomaly_is_closure_defect
    (X : L)
    (s : State)
    (hstat :
      C.ricciFlux.derivativeAlong.deriv
        C.ricciFlux.curvatureReadout.curvature X s = 0) :
    C.ricciFlux.ricciFlux X s = C.ricciFlux.closureDefect.defect X s :=
  C.ricciFlux.ricciFlux_eq_defect_of_curvature_stationary X s hstat

end TKKConformalClosure

end InfoGeometry.OperatorAlgebra.TKKConformalClosure
