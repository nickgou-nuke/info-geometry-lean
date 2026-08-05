/-
InfoGeometry/OperatorAlgebra/TKKClosure.lean

Tits-Kantor-Koecher closure sockets for the reflection-sensitive
O(4,4)/Pin(4,4) and projective Möbius stack.

The architectural point is:

* The algebraic closure is a 3-graded TKK Lie algebra

      g = g₋₁ ⊕ g₀ ⊕ g₊₁

  where the negative grade is the translation/system side, the zero grade is
  the structure algebra, and the positive grade is the special-conformal/
  mirror side.

* The symmetry-group closure is not `SO(4,4)` or `Spin(4,4)`.  Those forget
  reflection/chiral components.  The reflection-sensitive base is `O(4,4)`
  and `Pin(4,4)`.

* Möbius inversion is not a base projective transformation on `P(R⁴,⁴)`; it
  belongs to the ambient conformal compactification, modeled here by the
  projective null rays of signature `(5,5)` and by `O(5,5)`/`Pin(5,5)` data.

This file is an owner-level socket.  It does not construct a concrete Clifford
algebra or a concrete Jordan triple system; it records the dependency graph and
proof-carrying closure laws needed by concrete models.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.O44PinMobiusProjective
import InfoGeometry.OperatorAlgebra.KleinianTwist
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.SocketTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Jordan triple input for TKK -/

/--
A real Jordan triple system socket.

The intended product is written `{x y z}` and is symmetric in the outer
variables.  The Jordan triple identity is included explicitly because concrete
operator models may use different analytic domains or completions.
-/
structure JordanTripleSystem
    (J : Type*) [AddCommGroup J] [Module ℝ J] where
  /-- Triple product `{x y z}`. -/
  triple : J → J → J → J

  /-- Outer symmetry: `{x y z} = {z y x}`. -/
  outer_symm :
    ∀ x y z : J, triple x y z = triple z y x

  /-- Left linearity in addition. -/
  triple_add_left :
    ∀ u v x y : J, triple (u + v) x y = triple u x y + triple v x y

  /-- Left linearity in scalar multiplication. -/
  triple_smul_left :
    ∀ (c : ℝ) (x y z : J), triple (c • x) y z = c • triple x y z

  /-- Jordan triple identity. -/
  triple_identity :
    ∀ u v x y z : J,
      triple u v (triple x y z) - triple x y (triple u v z)
        =
      triple (triple u v x) y z -
        triple x (triple v u y) z

namespace JordanTripleSystem

variable
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (T : JordanTripleSystem J)

/-- Box operator associated to the pair `(x,y)`: `z ↦ {x y z}`. -/
def box
    (x y : J) : J → J :=
  fun z => T.triple x y z

/-- Apply the box operator. -/
@[simp] theorem box_apply
    (x y z : J) :
    T.box x y z = T.triple x y z :=
  rfl

/-- A zero-on-one-side restatement of the Jordan triple identity. -/
theorem triple_identity_eq_zero
    (u v x y z : J) :
      T.triple u v (T.triple x y z) -
          T.triple x y (T.triple u v z) -
          (T.triple (T.triple u v x) y z -
            T.triple x (T.triple v u y) z)
        = 0 := by
  rw [T.triple_identity u v x y z]
  simp

end JordanTripleSystem

/-! ## 2. Abstract Lie socket and TKK grades -/

/-- TKK grading labels. -/
inductive TKKGrade where
  | negative
  | zero
  | positive
deriving DecidableEq, Repr

namespace TKKGrade

/-- Inversion swaps the two outer grades and fixes grade zero. -/
def mirror : TKKGrade → TKKGrade
  | negative => positive
  | zero => zero
  | positive => negative

@[simp]
theorem mirror_mirror
    (g : TKKGrade) :
    mirror (mirror g) = g := by
  cases g <;> rfl

end TKKGrade

/--
A lightweight Lie algebra socket.

This avoids committing the repository to a concrete `LieAlgebra` realization at
this owner layer.  Downstream modules can replace it by Mathlib's Lie algebra
API once the concrete carrier is chosen.
-/
structure LieSocket
    (L : Type*) [AddCommGroup L] [Module ℝ L] where
  bracket : L → L → L

  bracket_skew :
    ∀ x y : L, bracket x y = - bracket y x

  bracket_add_left :
    ∀ x y z : L, bracket (x + y) z = bracket x z + bracket y z

  bracket_smul_left :
    ∀ (c : ℝ) (x y : L), bracket (c • x) y = c • bracket x y

  jacobi :
    ∀ x y z : L,
      bracket x (bracket y z) +
          bracket y (bracket z x) +
          bracket z (bracket x y)
        = 0

namespace LieSocket

variable
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (𝔤 : LieSocket L)

/-!
The socket laws determine a genuine Mathlib `LieRing`.  The adapter is kept
separate from `TKKLieClosure` so existing projection-based callers remain
source-compatible while downstream concrete models can use native Lie APIs.
-/
def toLieRing : LieRing L where
  bracket := 𝔤.bracket
  add_lie := 𝔤.bracket_add_left
  lie_add := by
    intro x y z
    calc
      𝔤.bracket x (y + z) = -𝔤.bracket (y + z) x := 𝔤.bracket_skew _ _
      _ = -(𝔤.bracket y x + 𝔤.bracket z x) := by
        rw [𝔤.bracket_add_left]
      _ = -𝔤.bracket y x + -𝔤.bracket z x := neg_add _ _
      _ = 𝔤.bracket x y + 𝔤.bracket x z := by
        rw [𝔤.bracket_skew y x, 𝔤.bracket_skew z x]
        simp only [neg_neg]
  lie_self := by
    intro x
    have h := 𝔤.bracket_skew x x
    have hz : 𝔤.bracket x x + 𝔤.bracket x x = 0 :=
      (eq_neg_iff_add_eq_zero.mp h)
    have htwo : (2 : ℝ) • 𝔤.bracket x x = 0 := by
      simpa [two_smul] using hz
    calc
      𝔤.bracket x x = (1 : ℝ) • 𝔤.bracket x x := by rw [one_smul]
      _ = ((2 : ℝ)⁻¹ * 2) • 𝔤.bracket x x := by norm_num
      _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • 𝔤.bracket x x) := by rw [mul_smul]
      _ = 0 := by rw [htwo, smul_zero]
  leibniz_lie := by
    have bracket_neg_left : ∀ x y : L, 𝔤.bracket (-x) y = -𝔤.bracket x y := by
      intro x y
      simpa using 𝔤.bracket_smul_left (-1 : ℝ) x y
    have bracket_neg_right : ∀ x y : L, 𝔤.bracket x (-y) = -𝔤.bracket x y := by
      intro x y
      rw [𝔤.bracket_skew, bracket_neg_left]
      simpa only [neg_neg] using 𝔤.bracket_skew y x
    intro x y z
    have h := 𝔤.jacobi x y z
    rw [𝔤.bracket_skew z x, bracket_neg_right,
      𝔤.bracket_skew z (𝔤.bracket x y)] at h
    apply eq_of_sub_eq_zero
    convert h using 1 <;> abel

end LieSocket

/-! ## 3. TKK Lie closure -/

/--
Tits-Kantor-Koecher closure of a Jordan triple system.

The conventional picture is

`g = g₋₁ ⊕ g₀ ⊕ g₊₁`,

with `g₋₁` carrying the original triple system, `g₀` carrying the structure
operators, and `g₊₁` carrying the inversion-conjugate/special-conformal copy.
-/
structure TKKLieClosure
    (J L : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] where
  jordan : JordanTripleSystem J
  lie : LieSocket L

  /-- Negative grade, interpreted as translations/system states. -/
  neg : J →ₗ[ℝ] L

  /-- Positive grade, interpreted as special-conformal/mirror states. -/
  pos : J →ₗ[ℝ] L

  /-- Grade-zero structure operator generated by a pair of Jordan elements. -/
  zero : J → J → L

  gradeSet : TKKGrade → Set L

  neg_mem :
    ∀ x : J, neg x ∈ gradeSet TKKGrade.negative

  pos_mem :
    ∀ x : J, pos x ∈ gradeSet TKKGrade.positive

  zero_mem :
    ∀ x y : J, zero x y ∈ gradeSet TKKGrade.zero

  /-- Negative grade is abelian. -/
  neg_abelian :
    ∀ x y : J, lie.bracket (neg x) (neg y) = 0

  /-- Positive grade is abelian. -/
  pos_abelian :
    ∀ x y : J, lie.bracket (pos x) (pos y) = 0

  /-- Cross-bracket closes into the structure grade. -/
  neg_pos_bracket :
    ∀ x y : J, lie.bracket (neg x) (pos y) = zero x y

  /-- Grade zero acts on the negative grade by the triple product. -/
  zero_neg_action :
    ∀ x y z : J,
      lie.bracket (zero x y) (neg z) =
        neg (jordan.triple x y z)

  /-- Grade zero acts contragrediently on the positive grade. -/
  zero_pos_action :
    ∀ x y z : J,
      lie.bracket (zero x y) (pos z) =
        -pos (jordan.triple y x z)

  /-- Bracket of two grade-zero generators remains in grade zero. -/
  zero_zero_bracket :
    ∀ x y u v : J, ∃ a b : J, lie.bracket (zero x y) (zero u v) = zero a b

  /-- The three grades generate the declared TKK Lie algebra. -/
  span_grades :
    Submodule.span ℝ
        (gradeSet TKKGrade.negative ∪
          gradeSet TKKGrade.zero ∪
          gradeSet TKKGrade.positive)
      = ⊤

namespace TKKLieClosure

variable
    {J L : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : TKKLieClosure J L)

/-- Re-export: the negative grade is abelian. -/
theorem bracket_neg_neg
    (x y : J) :
    T.lie.bracket (T.neg x) (T.neg y) = 0 :=
  T.neg_abelian x y

/-- Re-export: the positive grade is abelian. -/
theorem bracket_pos_pos
    (x y : J) :
    T.lie.bracket (T.pos x) (T.pos y) = 0 :=
  T.pos_abelian x y

/-- Re-export: the cross-bracket is the grade-zero structure element. -/
theorem bracket_neg_pos
    (x y : J) :
    T.lie.bracket (T.neg x) (T.pos y) = T.zero x y :=
  T.neg_pos_bracket x y

/-- Re-export: the opposite cross-bracket is the negative of the grade-zero
structure element, by Lie-socket skew symmetry. -/
theorem bracket_pos_neg
    (x y : J) :
    T.lie.bracket (T.pos y) (T.neg x) = -T.zero x y := by
  rw [T.lie.bracket_skew]
  rw [T.bracket_neg_pos]

/-- Re-export: structure-grade action on translations. -/
theorem bracket_zero_neg
    (x y z : J) :
    T.lie.bracket (T.zero x y) (T.neg z) =
      T.neg (T.jordan.triple x y z) :=
  T.zero_neg_action x y z

/-- Re-export: the opposite translation/structure bracket is the negative of
the induced triple action, by Lie-socket skew symmetry. -/
theorem bracket_neg_zero
    (x y z : J) :
    T.lie.bracket (T.neg z) (T.zero x y) =
      -T.neg (T.jordan.triple x y z) := by
  rw [T.lie.bracket_skew]
  rw [T.bracket_zero_neg]

/-- Re-export: structure-grade action on special conformal elements. -/
theorem bracket_zero_pos
    (x y z : J) :
    T.lie.bracket (T.zero x y) (T.pos z) =
      -T.pos (T.jordan.triple y x z) :=
  T.zero_pos_action x y z

/-- Re-export: the opposite special-conformal/structure bracket removes the
leading minus sign from the contragredient action. -/
theorem bracket_pos_zero
    (x y z : J) :
    T.lie.bracket (T.pos z) (T.zero x y) =
      T.pos (T.jordan.triple y x z) := by
  rw [T.lie.bracket_skew]
  rw [T.bracket_zero_pos]
  simp

end TKKLieClosure

/-! ## 4. TKK inversion closure -/

/--
Inversion closure of a TKK algebra.

This is the infinitesimal algebraic form of the Möbius fact that inversion
conjugates translations into special conformal transformations.
-/
structure TKKInversionClosure
    (J L : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : TKKLieClosure J L) where
  /-- Algebraic inversion on the TKK Lie carrier. -/
  inversion : L ≃ₗ[ℝ] L

  /-- Inversion is involutive. -/
  inversion_involutive :
    ∀ x : L, inversion (inversion x) = x

  /-- Negative grade is sent to positive grade. -/
  maps_neg_to_pos :
    ∀ x : J, inversion (T.neg x) = T.pos x

  /-- Positive grade is sent back to negative grade. -/
  maps_pos_to_neg :
    ∀ x : J, inversion (T.pos x) = T.neg x

  /-- Grade zero is preserved or reflected according to the concrete model. -/
  zero_grade_compatibility :
    ∀ x y : J, inversion (T.zero x y) = -T.zero x y

namespace TKKInversionClosure

variable
    {J L : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    {T : TKKLieClosure J L}
    (I : TKKInversionClosure J L T)

/-- Inversion sends a translation generator to its special-conformal mirror. -/
theorem neg_to_pos
    (x : J) :
    I.inversion (T.neg x) = T.pos x :=
  I.maps_neg_to_pos x

/-- Inversion sends a special-conformal generator back to a translation. -/
theorem pos_to_neg
    (x : J) :
    I.inversion (T.pos x) = T.neg x :=
  I.maps_pos_to_neg x

/-- Inversion reflects grade-zero generators according to the supplied model. -/
theorem zero_to_neg_zero
    (x y : J) :
    I.inversion (T.zero x y) = -T.zero x y :=
  I.zero_grade_compatibility x y

end TKKInversionClosure

/-! ## 5. Projective Möbius group closure -/

/--
A projective null state in the ambient conformal `(5,5)` model.
-/
structure TKKProjectiveNullState
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) where
  ray : ProjectiveRay W
  null : Q.q ray.vec = 0

/--
Reflection-sensitive TKK group closure.

The base linear symmetry is `O(4,4)`/`Pin(4,4)`.  The full projective Möbius
closure lives upstairs in the conformal ambient `O(5,5)`/`Pin(5,5)` model.
-/
structure TKKMobiusGroupClosure
    (J L V W PinBase PinConf : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf] where
  tkk : TKKLieClosure J L
  inversionClosure : TKKInversionClosure J L tkk

  /-- The reflection-sensitive projective conformal stack. -/
  pinMobius : PinMobiusProjective44 V W PinBase PinConf

  /-- The imported Pin/Möbius owner certifies lifting base Pin data upstairs. -/
  basePin_lift :
    PinLiftDatum V W PinBase PinConf pinMobius.mobius pinMobius.basePin
      pinMobius.conformalPin

  /-- The imported Pin/Möbius owner certifies action on projective null rays. -/
  projective_null_ray_action :
    ∀ r : ProjectiveRay W,
      r.IsAmbientNullRay pinMobius.mobius.ambientQ →
        ((pinMobius.conformalPin.cover pinMobius.conformalPin.inversionPin
          pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
            pinMobius.mobius.ambientQ

namespace TKKMobiusGroupClosure

variable
    {J L V W PinBase PinConf : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf]
    (G : TKKMobiusGroupClosure J L V W PinBase PinConf)

/-- Negative-grade generators lie in the declared negative TKK grade. -/
theorem negative_grade_mem
    (x : J) :
    G.tkk.neg x ∈ G.tkk.gradeSet TKKGrade.negative :=
  G.tkk.neg_mem x

/-- Grade-zero structure generators lie in the declared zero TKK grade. -/
theorem zero_grade_mem
    (x y : J) :
    G.tkk.zero x y ∈ G.tkk.gradeSet TKKGrade.zero :=
  G.tkk.zero_mem x y

/-- Positive-grade generators are the inversion-conjugates of negative generators. -/
theorem positive_is_inversion_conjugate
    (x : J) :
    G.inversionClosure.inversion (G.tkk.neg x) = G.tkk.pos x :=
  G.inversionClosure.maps_neg_to_pos x

/-- The conformal Pin/Möbius owner supplies the projective-null-ray action. -/
theorem acts_on_projective_null_states :
    ∀ r : ProjectiveRay W,
      r.IsAmbientNullRay G.pinMobius.mobius.ambientQ →
        ((G.pinMobius.conformalPin.cover G.pinMobius.conformalPin.inversionPin
          G.pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
            G.pinMobius.mobius.ambientQ :=
  G.projective_null_ray_action

/-- The imported Pin/Möbius owner retains both base-to-conformal lift and ray action data. -/
theorem reflection_sensitive :
  (∀ (a : PinBase) (ha : G.pinMobius.basePin.isPin a),
    G.pinMobius.conformalPin.cover
        (G.pinMobius.basePin_lifts_to_conformalPin.pinMap a)
        (G.pinMobius.basePin_lifts_to_conformalPin.pinMap_isPin a ha) =
      G.pinMobius.mobius.base_orthogonal_lift
        (G.pinMobius.basePin.cover a ha)) ∧
      (∀ r : ProjectiveRay W,
        r.IsAmbientNullRay G.pinMobius.mobius.ambientQ →
          ((G.pinMobius.conformalPin.cover G.pinMobius.conformalPin.inversionPin
            G.pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
              G.pinMobius.mobius.ambientQ) :=
  ⟨G.pinMobius.basePin_lifts_to_conformalPin.cover_compatibility,
    G.projective_null_ray_action⟩

end TKKMobiusGroupClosure

/-! ## 6. Stinespring-Tomita/TKK clinch -/

/--
The Stinespring-Tomita interpretation of TKK closure.

The negative grade is the system/observable side, the positive grade is the
commutant/environment mirror side, and inversion is the algebraic gear shift
that swaps them.  This is a compatibility socket, not a theorem of bare TKK.
-/
structure StinespringTomitaTKKClinch
    (Op J L : Type*)
    [Ring Op]
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] where
  tomita : TomitaCartanSplit.TomitaCommutantDatum Op
  tkk : TKKLieClosure J L
  inversionClosure : TKKInversionClosure J L tkk

/-! ## 7. Owner target -/

/--
Compatibility data for constructing a TKK/Möbius closure.

This is the non-vacuous replacement for the former compatibility socket: a
compatible model carries exactly the Jordan triple, three-graded Lie closure,
inversion closure, reflection-sensitive Pin/Möbius projective action, and group
closure certificates required to build `TKKMobiusGroupClosure`.
-/
structure TKKClosureCompatibility
    (J L V W PinBase PinConf : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf] where
  /-- The Tits-Kantor-Koecher Lie closure of the Jordan triple system. -/
  tkk : TKKLieClosure J L

  /-- Algebraic inversion swapping the negative and positive grades. -/
  inversionClosure : TKKInversionClosure J L tkk

  /-- Reflection-sensitive projective conformal Pin/Möbius stack. -/
  pinMobius : PinMobiusProjective44 V W PinBase PinConf

  /-- The imported Pin/Möbius owner certifies lifting base Pin data upstairs. -/
  basePin_lift :
    PinLiftDatum V W PinBase PinConf pinMobius.mobius pinMobius.basePin
      pinMobius.conformalPin

  /-- The imported Pin/Möbius owner certifies action on projective null rays. -/
  projective_null_ray_action :
    ∀ r : ProjectiveRay W,
      r.IsAmbientNullRay pinMobius.mobius.ambientQ →
        ((pinMobius.conformalPin.cover pinMobius.conformalPin.inversionPin
          pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
            pinMobius.mobius.ambientQ

namespace TKKClosureCompatibility

variable
    {J L V W PinBase PinConf : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf]

/-- Construct the TKK/Möbius group closure from explicit compatibility data. -/
def toTKKMobiusGroupClosure
    (C : TKKClosureCompatibility J L V W PinBase PinConf) :
    TKKMobiusGroupClosure J L V W PinBase PinConf where
  tkk := C.tkk
  inversionClosure := C.inversionClosure
  pinMobius := C.pinMobius
  basePin_lift := C.basePin_lift
  projective_null_ray_action := C.projective_null_ray_action

end TKKClosureCompatibility

/--
Construct the TKK closure layer from explicit compatibility data.

Concrete modules must supply the Jordan triple system, the three-grade Lie
closure, and the conformal/projective Pin-Möbius action.
-/
theorem tkkClosureOwnerTarget :
  ∀ (J L V W PinBase PinConf : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf],
    ∀ C : TKKClosureCompatibility J L V W PinBase PinConf,
    ∀ x y : J,
      C.tkk.neg x ∈ C.tkk.gradeSet TKKGrade.negative ∧
        C.tkk.zero x y ∈ C.tkk.gradeSet TKKGrade.zero ∧
        C.tkk.pos y ∈ C.tkk.gradeSet TKKGrade.positive ∧
        C.inversionClosure.inversion (C.tkk.neg x) = C.tkk.pos x ∧
        C.inversionClosure.inversion (C.tkk.pos y) = C.tkk.neg y ∧
        (∀ (a : PinBase) (ha : C.pinMobius.basePin.isPin a),
          C.pinMobius.conformalPin.cover
              (C.pinMobius.basePin_lifts_to_conformalPin.pinMap a)
              (C.pinMobius.basePin_lifts_to_conformalPin.pinMap_isPin a ha) =
            C.pinMobius.mobius.base_orthogonal_lift
              (C.pinMobius.basePin.cover a ha)) ∧
        (∀ r : ProjectiveRay W,
          r.IsAmbientNullRay C.pinMobius.mobius.ambientQ →
            ((C.pinMobius.conformalPin.cover C.pinMobius.conformalPin.inversionPin
              C.pinMobius.conformalPin.inversionPin_isPin).actRay r).IsAmbientNullRay
                C.pinMobius.mobius.ambientQ) := by
  intro J L V W PinBase PinConf _ _ _ _ _ _ _ _ _ _ C x y
  exact ⟨C.tkk.neg_mem x,
    C.tkk.zero_mem x y,
    C.tkk.pos_mem y,
    C.inversionClosure.maps_neg_to_pos x,
    C.inversionClosure.maps_pos_to_neg y,
    C.pinMobius.basePin_lifts_to_conformalPin.cover_compatibility,
    C.projective_null_ray_action⟩

end InfoGeometry.OperatorAlgebra
