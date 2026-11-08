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

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.O44PinMobiusProjective
import InfoGeometry.OperatorAlgebra.TKKClosure

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
Projective action preserves ambient null rays; the Boolean component convention
is decidable by case split; a supplied null-swap inversion exchanges the two
distinguished null directions; the owner closure re-exports its explicit
structure fields as theorem-level obligations.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The conformal compactification, base-action lift, TKK integration, and Pin
reflection claims are conditional on the named fields of
`ConformalMobius44Extension`, `PO55ConformalClosure`, and
`TKKMobiusGroupClosure`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct a concrete analytic `PO(5,5)` quotient, a full
ambient Clifford/Pin representation, or a continuum conformal compactification.
Those remain model-supplied inputs.
-/

/-! ## 1. Projective `O(5,5)` as action on rays -/

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

/--
Two ambient orthogonal transformations have the same conformal action when
they agree projectively on compactified null states.

This is weaker than `SamePO55Action`, which asks for equality on every
represented projective ray.
-/
def SamePO55NullAction
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}
    (g h : Orthogonal55 Q) : Prop :=
  ∀ r : ConformalState55 Q,
    (g.actRay r.1).SameProjectiveRay (h.actRay r.1)

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
structure PO55ComponentLedger
    (W PinConf : Type*) [AddCommGroup W] [Module ℝ W] [Monoid PinConf]
    (Q : SplitQuadratic55 W) where
  /-- The central `±1` ambiguity is identified projectively. -/
  central_antipodal_identified :
    ∀ (r : ProjectiveRay W),
      ProjectiveRay.SameProjectiveRay r (ProjectiveRay.antipode r)

  /-- Ambient Pin cover carrying the reflection-sensitive inversion component. -/
  conformalPin : Pin55CoverDatum (W := W) (PinEl := PinConf) Q

  /-- The chosen component label of the distinguished Möbius inversion. -/
  inversion_component : O44Component

  /-- The chosen label is the component of the covered ambient inversion. -/
  residual_reflection_components :
    inversion_component =
      (conformalPin.cover conformalPin.inversionPin
        conformalPin.inversionPin_isPin).component

namespace PO55ComponentLedger

variable
    {W PinConf : Type*} [AddCommGroup W] [Module ℝ W] [Monoid PinConf]
    {Q : SplitQuadratic55 W}
    (C : PO55ComponentLedger W PinConf Q)

/-- Both Boolean bookkeeping fields have concrete truth values. -/
theorem component_convention_holds :
    (∀ (r : ProjectiveRay W),
      ProjectiveRay.SameProjectiveRay r (ProjectiveRay.antipode r)) ∧
    (C.inversion_component = O44Component.reflection ∨
      C.inversion_component = O44Component.totalInversion) := by
  refine ⟨C.central_antipodal_identified, ?_⟩
  rcases C.conformalPin.inversion_is_reflection_or_null_swap with h | h
  · exact Or.inl (C.residual_reflection_components.trans h)
  · exact Or.inr (C.residual_reflection_components.trans h)

end PO55ComponentLedger

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

  /--
  Model-supplied null-pairing readout. In a concrete bilinear model this is
  morally `⟪e₋, e₊⟫`.
  -/
  pairing : W → W → ℝ

  /-- The two null directions are paired nondegenerately. -/
  pairing_ne_zero :
    pairing eMinus ePlus ≠ 0

namespace AmbientNullPair

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}

variable (N : AmbientNullPair Q)

/-- If the supplied pairing vanishes on both null diagonals, the null directions are distinct. -/
theorem eMinus_ne_ePlus_of_pairing_zero_on_diagonal
    (h_diag_minus : N.pairing N.eMinus N.eMinus = 0)
    (_h_diag_plus : N.pairing N.ePlus N.ePlus = 0) :
    N.eMinus ≠ N.ePlus := by
  intro h
  apply N.pairing_ne_zero
  rw [← h]
  exact h_diag_minus

end AmbientNullPair

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
    SplitQuadratic55.SameRay (swap.toLinearEquiv N.eMinus) N.ePlus

  maps_plus_to_minus_projectively :
    SplitQuadratic55.SameRay (swap.toLinearEquiv N.ePlus) N.eMinus

namespace NullSwapInversion

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}
    {N : AmbientNullPair Q}

variable (I : NullSwapInversion Q N)

/-- The null swap is an ambient projective orthogonal element. -/
def toProjectiveOrthogonal55 :
    ProjectiveOrthogonal55 Q where
  rep := I.swap

/-- The affine-chart inversion law is available. -/
theorem realizes_affine_inversion_holds :
    SplitQuadratic55.SameRay (I.swap.toLinearEquiv N.eMinus) N.ePlus ∧
    SplitQuadratic55.SameRay (I.swap.toLinearEquiv N.ePlus) N.eMinus :=
  ⟨I.maps_minus_to_plus_projectively, I.maps_plus_to_minus_projectively⟩

end NullSwapInversion

/-! ## 4A. Projective survivors of Möbius inversion -/

/--
An abstract Möbius inversion datum on an ambient carrier.

The affine chart is deliberately not part of this structure.  The surviving
data are the linear involution, the null cone, and preservation of that cone.
-/
structure MobiusInversionDatum
    (W : Type*) [AddCommGroup W] [Module ℝ W] where
  /-- The ambient linear involution implementing the chart swap. -/
  inv : W →ₗ[ℝ] W

  /-- The inversion squares to the identity. -/
  inv_sq :
    ∀ x : W, inv (inv x) = x

  /-- The projective conformal null cone. -/
  nullCone : Set W

  /-- The inversion preserves the null cone. -/
  preserves_null :
    ∀ x : W, x ∈ nullCone → inv x ∈ nullCone

namespace MobiusInversionDatum

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (I : MobiusInversionDatum W)

/--
The inversion also reflects nullness backwards.

This follows from involutivity, so null-cone preservation is an equivalence
along inversion orbits.
-/
theorem preserves_null_reverse
    {x : W}
    (hx : I.inv x ∈ I.nullCone) :
    x ∈ I.nullCone := by
  have h := I.preserves_null (I.inv x) hx
  simpa [I.inv_sq x] using h

/--
A null vector represents a projectively fixed ray when inversion rescales it
by a nonzero scalar.  The zero vector is excluded because projective rays have
nonzero representatives.
-/
def IsProjectiveFixed
    (x : W) : Prop :=
  x ≠ 0 ∧
    x ∈ I.nullCone ∧
      ∃ c : ℝ, c ≠ 0 ∧ I.inv x = c • x

/--
A readout survives Möbius inversion when it is constant on the inversion orbit
of every null vector.
-/
def IsMobiusInvariantReadout
    {α : Type*}
    (read : W → α) : Prop :=
  ∀ x : W, x ∈ I.nullCone → read (I.inv x) = read x

/-- A readout is projective when it ignores nonzero scalar rescaling. -/
def IsProjectiveReadout
    {α : Type*}
    (read : W → α) : Prop :=
  ∀ c : ℝ, ∀ x : W, c ≠ 0 → read (c • x) = read x

/-- The fixed linear subspace predicate for the inversion. -/
def IsFixedVector
    (x : W) : Prop :=
  I.inv x = x

/-- The anti-fixed linear subspace predicate for the inversion. -/
def IsAntiFixedVector
    (x : W) : Prop :=
  I.inv x = -x

/-- A fixed null vector gives a projectively fixed null ray. -/
theorem fixedVector_isProjectiveFixed
    {x : W}
    (hx0 : x ≠ 0)
    (hnull : x ∈ I.nullCone)
    (hfix : I.IsFixedVector x) :
    I.IsProjectiveFixed x := by
  refine ⟨hx0, hnull, 1, one_ne_zero, ?_⟩
  simpa [IsFixedVector] using hfix

/-- An anti-fixed null vector also gives a projectively fixed null ray. -/
theorem antiFixedVector_isProjectiveFixed
    {x : W}
    (hx0 : x ≠ 0)
    (hnull : x ∈ I.nullCone)
    (hanti : I.IsAntiFixedVector x) :
    I.IsProjectiveFixed x := by
  refine ⟨hx0, hnull, -1, by norm_num, ?_⟩
  simpa [IsAntiFixedVector] using hanti

/-- The inverse representative of a projectively fixed ray is projectively fixed. -/
theorem inv_isProjectiveFixed
    {x : W}
    (hx : I.IsProjectiveFixed x) :
    I.IsProjectiveFixed (I.inv x) := by
  rcases hx with ⟨hx0, hnull, c, hc, hscale⟩
  have hinv0 : I.inv x ≠ 0 := by
    intro hzero
    apply hx0
    have h := congrArg I.inv hzero
    simpa [I.inv_sq x] using h
  refine ⟨hinv0, I.preserves_null x hnull, c⁻¹, inv_ne_zero hc, ?_⟩
  have hxscale : x = c⁻¹ • I.inv x := by
    rw [hscale]
    simp [hc]
  simpa [I.inv_sq x] using hxscale

/--
For a nonzero projectively fixed representative, the projective scale squares
to one.  This is the algebraic content of `I² = 1` on projective fixed rays.
-/
theorem scale_sq_eq_one_of_projectiveFixed_scale
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    {c : ℝ}
    (hx0 : x ≠ 0)
    (hscale : I.inv x = c • x) :
    c ^ 2 = 1 := by
  have happly : x = (c ^ 2) • x := by
    calc
      x = I.inv (I.inv x) := (I.inv_sq x).symm
      _ = I.inv (c • x) := by rw [hscale]
      _ = c • I.inv x := by simp
      _ = c • (c • x) := by rw [hscale]
      _ = (c ^ 2) • x := by
          simpa [pow_two] using (smul_smul c c x)
  have hsmulzero : (c ^ 2 - 1) • x = 0 := by
    calc
      (c ^ 2 - 1) • x
          = (c ^ 2) • x - (1 : ℝ) • x := by
              rw [sub_smul]
      _ = (c ^ 2) • x - x := by
              rw [one_smul]
      _ = x - x := by
              rw [← happly]
      _ = 0 := by
              simp
  rcases smul_eq_zero.mp hsmulzero with hcoef | hx
  · exact sub_eq_zero.mp hcoef
  · exact (hx0 hx).elim

/-- The projective fixed scale is either `1` or `-1`. -/
theorem scale_eq_one_or_neg_one_of_projectiveFixed_scale
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    {c : ℝ}
    (hx0 : x ≠ 0)
    (hscale : I.inv x = c • x) :
    c = 1 ∨ c = -1 := by
  have hsquare :
      c ^ 2 = 1 :=
    I.scale_sq_eq_one_of_projectiveFixed_scale hx0 hscale
  have hfactor : (c - 1) * (c + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    linarith
  · right
    linarith

/--
A nonzero projectively fixed vector is represented by either a fixed vector or
an anti-fixed vector.  This is the Lean form of
`Fix_P(I) = P(N ∩ W_+) ∪ P(N ∩ W_-)`, modulo the explicit representative.
-/
theorem projectiveFixed_fixed_or_antiFixed
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    (hx : I.IsProjectiveFixed x) :
    I.IsFixedVector x ∨ I.IsAntiFixedVector x := by
  rcases hx with ⟨hx0, _hnull, c, _hc, hscale⟩
  rcases I.scale_eq_one_or_neg_one_of_projectiveFixed_scale hx0 hscale with hc | hc
  · left
    simpa [IsFixedVector, hc] using hscale
  · right
    simpa [IsAntiFixedVector, hc] using hscale

/-- Projective readouts are unchanged on projectively fixed rays. -/
theorem readout_eq_on_projectiveFixed
    {α : Type*}
    {read : W → α}
    (hread : IsProjectiveReadout read)
    {x : W}
    (hfix : I.IsProjectiveFixed x) :
    read (I.inv x) = read x := by
  rcases hfix with ⟨_hx0, _hnull, c, hc, hscale⟩
  rw [hscale]
  exact hread c x hc

/-- Re-export: invariant readouts agree on the inverted representative. -/
theorem invariantReadout_inv_eq
    {α : Type*}
    {read : W → α}
    (hread : I.IsMobiusInvariantReadout read)
    {x : W}
    (hnull : x ∈ I.nullCone) :
    read (I.inv x) = read x :=
  hread x hnull

/--
The paired readout that remembers both chart representatives.

This is the formal socket for symmetrized visible/hidden memory accounting:
under inversion, the two components swap.
-/
def symmetrizedReadout
    {α : Type*}
    (read : W → α)
    (x : W) : α × α :=
  (read x, read (I.inv x))

/-- Möbius inversion swaps the two entries of the symmetrized readout. -/
theorem symmetrizedReadout_inv
    {α : Type*}
    (read : W → α)
    (x : W) :
    I.symmetrizedReadout read (I.inv x) =
      (read (I.inv x), read x) := by
  simp [symmetrizedReadout, I.inv_sq x]

end MobiusInversionDatum

namespace SplitQuadratic55

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}

/--
The ambient orthogonal action supplies a Möbius-inversion datum when its
representative is involutive.
-/
def mobiusInversionOfOrthogonal
    (g : Orthogonal55 Q)
    (hg : ∀ x : W, g.toLinearEquiv (g.toLinearEquiv x) = x) :
    MobiusInversionDatum W where
  inv := g.toLinearEquiv.toLinearMap
  inv_sq := hg
  nullCone := {x : W | Q.IsNull x}
  preserves_null := by
    intro x hx
    dsimp [IsNull] at *
    rw [g.preserves_q x]
    exact hx

end SplitQuadratic55

/-! ## 5. PO(5,5) conformal closure ledger -/

/--
The global `PO(5,5)` conformal closure of the local `O(4,4)` geometry.

This is the precise formal layer for the slogan:

`O(4,4)` is local; `PO(5,5)` is the conformal/projective global ledger.
-/
structure PO55ConformalClosure
    (V W PinConf : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [Monoid PinConf] where
  /-- Existing base-to-ambient conformal extension. -/
  mobius : ConformalMobius44Extension V W

  /-- Component bookkeeping after quotienting by projective scalars. -/
  components : PO55ComponentLedger W PinConf mobius.ambientQ

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

  /-- Möbius inversion as a projective `O(5,5)` element. -/
  inversionPO55 :
    ProjectiveOrthogonal55 mobius.ambientQ

  /--
  The projective inversion representative is exactly the supplied null-swap
  orthogonal map.
  -/
  inversionPO55_rep :
    inversionPO55.rep = inversion.swap

namespace PO55ConformalClosure

variable
    {V W PinConf : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinConf]
    (C : PO55ConformalClosure V W PinConf)

/-- The compactified state space attached to the closure. -/
abbrev State :=
  ConformalState55 C.mobius.ambientQ

/-- The affine point `v` as a compactified/projective null state. -/
def affineState
    (v : V) : C.State :=
  ⟨C.mobius.projectivePoint v, C.affine_points_are_conformal_states v⟩

/-- The distinguished inversion acts on compactified conformal states. -/
def inversionAct
    (r : C.State) : C.State :=
  ConformalState55.act C.inversionPO55 r

/-- The affine-chart inversion law is available. -/
theorem inversion_affine_chart_formula_holds :
    C.inversionPO55.rep = C.inversion.swap ∧
    SplitQuadratic55.SameRay
      (C.inversion.swap.toLinearEquiv C.nullPair.eMinus)
      C.nullPair.ePlus ∧
    SplitQuadratic55.SameRay
      (C.inversion.swap.toLinearEquiv C.nullPair.ePlus)
      C.nullPair.eMinus := by
  exact ⟨
    C.inversionPO55_rep,
    C.inversion.maps_minus_to_plus_projectively,
    C.inversion.maps_plus_to_minus_projectively
  ⟩

/-- The distinguished projective inversion is represented by the null swap. -/
theorem inversionPO55_is_nullSwap :
    C.inversionPO55.rep = C.inversion.swap :=
  C.inversionPO55_rep

/-- Re-export: base `O(4,4)` actions lift into the projective conformal ledger. -/
theorem base_action_lifts
    (g : Orthogonal44 C.mobius.baseQ) :
    ∃ G : ProjectiveOrthogonal55 C.mobius.ambientQ,
      SamePO55Action G.rep (C.mobius.base_orthogonal_lift g) :=
  C.base_action_lifts_to_PO55 g

/-- Re-export: affine points are compactified null states. -/
theorem affineState_is_null
    (v : V) :
    (C.affineState v).1.IsAmbientNullRay C.mobius.ambientQ :=
  (C.affineState v).2

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
  po55 : PO55ConformalClosure V W PinConf

namespace TKKPO55ClosedSymmetry

variable
    {J L V W PinBase PinConf : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf]

variable (S : TKKPO55ClosedSymmetry J L V W PinBase PinConf)

/-- The TKK integration law is available. -/
theorem tkk_integrates_to_projective_conformal_action :
    ∀ r : ProjectiveRay W,
      r.IsAmbientNullRay S.tkkMobius.pinMobius.mobius.ambientQ →
        ((S.tkkMobius.pinMobius.conformalPin.cover
          S.tkkMobius.pinMobius.conformalPin.inversionPin
          S.tkkMobius.pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
            S.tkkMobius.pinMobius.mobius.ambientQ :=
  by
    intro r hr
    exact S.tkkMobius.pinMobius.acts_on_projective_null_rays r hr

/-- The Pin(5,5) reflection-lift law is available. -/
theorem pin55_reflection_lift_matches_PO55 :
    (∀ (a : PinBase)
        (ha : S.tkkMobius.pinMobius.basePin.isPin a),
      S.tkkMobius.pinMobius.conformalPin.cover
          (S.tkkMobius.pinMobius.basePin_lifts_to_conformalPin.pinMap a)
          (S.tkkMobius.pinMobius.basePin_lifts_to_conformalPin.pinMap_isPin a ha) =
        S.tkkMobius.pinMobius.mobius.base_orthogonal_lift
          (S.tkkMobius.pinMobius.basePin.cover a ha)) ∧
      (∀ r : ProjectiveRay W,
        r.IsAmbientNullRay S.tkkMobius.pinMobius.mobius.ambientQ →
          ((S.tkkMobius.pinMobius.conformalPin.cover
            S.tkkMobius.pinMobius.conformalPin.inversionPin
            S.tkkMobius.pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
              S.tkkMobius.pinMobius.mobius.ambientQ) :=
  by
    refine ⟨S.tkkMobius.pinMobius.basePin_lifts_to_conformalPin.cover_compatibility,
      ?_⟩
    intro r hr
    exact S.tkkMobius.pinMobius.acts_on_projective_null_rays r hr

/-- The inversion grade-swap law is available. -/
theorem inversion_swaps_tkk_outer_grades
    (x : J) :
    S.tkkMobius.inversionClosure.inversion (S.tkkMobius.tkk.neg x) =
      S.tkkMobius.tkk.pos x :=
  S.tkkMobius.positive_is_inversion_conjugate x

/-- The projective-null-state closure law is available. -/
theorem projective_null_rays_are_closed_states :
    ∀ v : V,
      (S.po55.mobius.projectivePoint v).IsAmbientNullRay S.po55.mobius.ambientQ :=
  S.po55.affine_points_are_conformal_states

end TKKPO55ClosedSymmetry

/-! ## 7. Owner target -/

/--
Installed-owner target: once a `PO55ConformalClosure` witness is supplied, each
base affine point gives a compactified projective null state.
-/
def PO55ConformalClosureInstalledTarget : Prop :=
  ∀ (V W PinConf : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [Monoid PinConf],
  ∀ C : PO55ConformalClosure V W PinConf,
  ∀ v : V,
    (C.affineState v).1.IsAmbientNullRay C.mobius.ambientQ

/--
Installed `PO(5,5)` closures satisfy the affine-null-state target.
-/
theorem po55ConformalClosureInstalledTarget :
    PO55ConformalClosureInstalledTarget := by
  intro V W PinConf _ _ _ _ _ C v
  exact C.affineState_is_null v

end InfoGeometry.OperatorAlgebra
