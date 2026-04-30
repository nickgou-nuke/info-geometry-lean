/-
InfoGeometry/OperatorAlgebra/PO55ConformalClosure.lean

Projective O(5,5) conformal closure of the O(4,4)/Pin(4,4) stack.

The point of this file is to make the final symmetry layer explicit:

* Base local split geometry lives in signature `(4,4)`.
* Reflection-sensitive local symmetry is `O(4,4)`/`Pin(4,4)`, not
  `SO(4,4)`/`Spin(4,4)`.
* Möbius inversion is not a nontrivial transformation of base projective rays
  in `P(R⁴,⁴)`; it becomes genuine only on the conformal compactification,
  modeled as projective null rays in an ambient `(5,5)` space.
* The global conformal ledger is the projective action of `O(5,5)`, with the
  Clifford reflection lift supplied by ambient `Pin(5,5)`.

This is an owner-level socket.  It does not quotient by `±1` as an actual Lean
quotient type; instead it records projective equality by equality of actions on
rays.  Concrete matrix/Clifford models can later instantiate the quotient.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.O44PinMobiusProjective
import InfoGeometry.OperatorAlgebra.TKKClosure

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Ambient null rays for signature `(5,5)` -/

namespace SplitQuadratic55

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W)

/-- Null/isotropic vectors in the ambient conformal `(5,5)` carrier. -/
def IsNull
    (w : W) : Prop :=
  Q.q w = 0

/-- Regular/non-null ambient vectors. -/
def IsRegular
    (w : W) : Prop :=
  Q.q w ≠ 0

/-- Same ambient projective ray, represented by nonzero real scaling. -/
def SameRay
    (v w : W) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ w = c • v

/-- Nullity is invariant under nonzero rescaling. -/
theorem isNull_of_sameRay
    {v w : W}
    (hvw : SameRay v w)
    (hv : Q.IsNull v) :
    Q.IsNull w := by
  rcases hvw with ⟨c, _hc, rfl⟩
  dsimp [IsNull]
  rw [Q.q_smul, hv]
  ring

end SplitQuadratic55

namespace ProjectiveRay

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- A represented projective ray lies on the ambient projective null quadric. -/
def IsAmbientNullRay
    (Q : SplitQuadratic55 W)
    (r : ProjectiveRay W) : Prop :=
  Q.IsNull r.vec

/-- Ambient null-ray membership is independent of representative. -/
theorem isAmbientNullRay_of_same
    (Q : SplitQuadratic55 W)
    {r s : ProjectiveRay W}
    (hrs : SameProjectiveRay r s)
    (hr : IsAmbientNullRay Q r) :
    IsAmbientNullRay Q s :=
  Q.isNull_of_sameRay hrs hr

end ProjectiveRay

namespace Orthogonal55

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}

/-- The ambient `O(5,5)` action preserves the projective null quadric. -/
theorem actRay_preserves_null
    (g : Orthogonal55 Q)
    (r : ProjectiveRay W)
    (hr : r.IsAmbientNullRay Q) :
    (g.actRay r).IsAmbientNullRay Q := by
  dsimp [actRay, ProjectiveRay.IsAmbientNullRay, SplitQuadratic55.IsNull] at *
  rw [g.preserves_q]
  exact hr

/-- The ambient `O(5,5)` action respects projective ray representatives. -/
theorem actRay_respects_same
    (g : Orthogonal55 Q)
    {r s : ProjectiveRay W}
    (hrs : r.SameProjectiveRay s) :
    (g.actRay r).SameProjectiveRay (g.actRay s) := by
  rcases hrs with ⟨c, hc, hs⟩
  refine ⟨c, hc, ?_⟩
  dsimp [actRay]
  rw [hs]
  simp

end Orthogonal55

/-! ## 2. Projective `O(5,5)` as action on rays -/

/--
Two ambient orthogonal transformations are projectively equivalent when they
have the same action on represented projective rays.

This is the quotient-by-scalars idea behind `PO(5,5)`, expressed without
introducing an actual quotient type at this owner layer.
-/
def SamePO55Action
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}
    (g h : Orthogonal55 Q) : Prop :=
  ∀ r : ProjectiveRay W,
    (g.actRay r).SameProjectiveRay (h.actRay r)

/-- A projective `O(5,5)` element, represented by an ambient orthogonal map. -/
structure ProjectiveOrthogonal55
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) where
  rep : Orthogonal55 Q

namespace ProjectiveOrthogonal55

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}

/-- Projective action on represented ambient rays. -/
def actRay
    (g : ProjectiveOrthogonal55 Q)
    (r : ProjectiveRay W) : ProjectiveRay W :=
  g.rep.actRay r

/-- Projective action preserves the ambient null quadric. -/
theorem actRay_preserves_null
    (g : ProjectiveOrthogonal55 Q)
    (r : ProjectiveRay W)
    (hr : r.IsAmbientNullRay Q) :
    (g.actRay r).IsAmbientNullRay Q :=
  g.rep.actRay_preserves_null r hr

end ProjectiveOrthogonal55

/--
A compactified conformal state is a projective null ray in the ambient `(5,5)`
model.
-/
abbrev ConformalState55
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) :=
  { r : ProjectiveRay W // r.IsAmbientNullRay Q }

namespace ConformalState55

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}

/-- Projective `O(5,5)` action on compactified conformal states. -/
def act
    (g : ProjectiveOrthogonal55 Q)
    (r : ConformalState55 Q) : ConformalState55 Q :=
  ⟨g.actRay r.1, g.actRay_preserves_null r.1 r.2⟩

end ConformalState55

/-! ## 3. Component bookkeeping after projectivization -/

/--
Projectivization removes the central antipodal ambiguity, but it should not be
confused with passing automatically to the identity component.

For split real signatures, reflection components remain meaningful unless the
model explicitly restricts to a connected subgroup or complexifies.
-/
structure PO55ComponentLedger where
  /-- The central `±1` ambiguity has been identified projectively. -/
  central_antipodal_identified : Prop

  /-- Reflection/inversion components are still part of the full real group. -/
  residual_reflection_components : Prop

  /-- The chosen component label of the distinguished Möbius inversion. -/
  inversion_component : O44Component

  /-- Certificate explaining the component convention used by the model. -/
  component_convention : Prop

/-! ## 4. Null-pair model for affine charts and inversion -/

/--
A pair of distinguished ambient null directions used to build the affine chart.

In concrete conformal geometry one writes representatives using two null
vectors, morally `e₋` and `e₊`, and an affine point `x : R⁴,⁴` is sent to a null
ray such as `[e₋ + x - 1/2 Q(x)e₊]`, up to sign convention.  Swapping the two
null directions realizes inversion on the affine chart.
-/
structure AmbientNullPair
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) where
  eMinus : W
  ePlus : W

  eMinus_null :
    Q.IsNull eMinus

  ePlus_null :
    Q.IsNull ePlus

  eMinus_ne_zero :
    eMinus ≠ 0

  ePlus_ne_zero :
    ePlus ≠ 0

  /-- Nondegenerate pairing of the two null directions, left abstract here. -/
  null_pair_nonzero : Prop

/--
A distinguished ambient transformation swapping the two conformal null
directions.  This is the projective/geometric source of sphere inversion.
-/
structure NullSwapInversion
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W)
    (N : AmbientNullPair Q) where
  swap : Orthogonal55 Q

  maps_minus_to_plus_projectively :
    N.ePlus = swap.toLinearEquiv N.eMinus ∨
      SplitQuadratic55.SameRay (swap.toLinearEquiv N.eMinus) N.ePlus

  maps_plus_to_minus_projectively :
    N.eMinus = swap.toLinearEquiv N.ePlus ∨
      SplitQuadratic55.SameRay (swap.toLinearEquiv N.ePlus) N.eMinus

  /-- Certificate that this null swap realizes affine Möbius inversion. -/
  realizes_affine_inversion : Prop

/-! ## 5. PO(5,5) conformal closure ledger -/

/--
The global `PO(5,5)` conformal closure of the local `O(4,4)` geometry.

This is the precise formal layer for the slogan:

`O(4,4)` is local; `PO(5,5)` is the conformal/projective global ledger.
-/
structure PO55ConformalClosure
    (V W : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] where
  /-- Existing base-to-ambient conformal extension. -/
  mobius : ConformalMobius44Extension V W

  /-- Component bookkeeping after quotienting by projective scalars. -/
  components : PO55ComponentLedger

  /-- Null directions selecting the affine chart. -/
  nullPair : AmbientNullPair mobius.ambientQ

  /-- Distinguished inversion/null-swap transformation. -/
  inversion : NullSwapInversion mobius.ambientQ nullPair

  /-- Every base affine point is represented by an ambient projective null ray. -/
  affine_points_are_conformal_states :
    ∀ v : V, (mobius.projectivePoint v).IsAmbientNullRay mobius.ambientQ

  /-- The base `O(4,4)` action is lifted into the projective conformal ledger. -/
  base_action_lifts_to_PO55 :
    ∀ g : Orthogonal44 mobius.baseQ,
      ∃ G : ProjectiveOrthogonal55 mobius.ambientQ,
        SamePO55Action G.rep (mobius.base_orthogonal_lift g)

  /-- Möbius inversion is represented by a projective `O(5,5)` element. -/
  inversion_is_PO55_element :
    ProjectiveOrthogonal55 mobius.ambientQ

  /-- The affine-chart formula for inversion is supplied by the model. -/
  inversion_affine_chart_formula : Prop

namespace PO55ConformalClosure

variable
    {V W : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (C : PO55ConformalClosure V W)

/-- The compactified state space attached to the closure. -/
abbrev State :=
  ConformalState55 C.mobius.ambientQ

/-- The affine point `v` as a compactified/projective null state. -/
def affineState
    (v : V) : C.State :=
  ⟨C.mobius.projectivePoint v, C.affine_points_are_conformal_states v⟩

end PO55ConformalClosure

/-! ## 6. TKK plus PO(5,5) symmetry closure -/

/--
Final closed algebra-plus-symmetry ledger.

The TKK layer closes the infinitesimal algebra; the `PO(5,5)` layer closes the
projective conformal state space; the Pin layer retains reflection/chiral data.
-/
structure TKKPO55ClosedSymmetry
    (J L V W PinBase PinConf : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf] where
  /-- TKK infinitesimal closure. -/
  tkkMobius : TKKMobiusGroupClosure J L V W PinBase PinConf

  /-- Projective conformal `PO(5,5)` closure of the state space. -/
  po55 : PO55ConformalClosure V W

  /-- Compatibility between the TKK ambient action and the `PO(5,5)` action. -/
  tkk_integrates_to_projective_conformal_action : Prop

  /-- Ambient `Pin(5,5)` retains the reflection/chiral classes. -/
  pin55_reflection_lift_matches_PO55 : Prop

  /-- The positive TKK grade is inversion-conjugate to the negative grade. -/
  inversion_swaps_tkk_outer_grades : Prop

  /-- Projective null rays are the closed state space of the model. -/
  projective_null_rays_are_closed_states : Prop

/-! ## 7. Owner target -/

/-- Compatibility predicate for constructing the `PO(5,5)` closure. -/
def PO55ConformalClosureCompatibility
    (V W : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] : Prop :=
  True

/-- Owner target for the projective conformal closure. -/
def PO55ConformalClosureOwnerTarget : Prop :=
  ∀ (V W : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W],
    PO55ConformalClosureCompatibility V W →
      Nonempty (PO55ConformalClosure V W)

end InfoGeometry.OperatorAlgebra
