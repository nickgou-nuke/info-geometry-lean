/-
InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean

O(4,4), Pin(4,4), and the projective/Möbius extension.

This module records the correct hierarchy:

* `O(4,4)` is the linear split-orthogonal group on the real doubled carrier.
  It keeps the reflection components that `SO(4,4)` discards.

* `Pin(4,4)` is the Clifford-level cover of `O(4,4)`.  Odd Pin elements
  implement reflections and may flip chirality; this is precisely the data lost
  by restricting too early to `Spin(4,4)`.

* Projectivizing the base carrier `V` gives rays and the projective null
  quadric.  The linear `O(4,4)` action descends to these rays.

* The radial inversion `x ↦ x / Q(x)` is projectively trivial on rays of `V`
  itself, because it only rescales `x`.  To make inversion a genuine Möbius
  transformation one passes to the conformal/projective compactification, whose
  ambient split signature is `(5,5)`.  The conformal group is then modeled by
  projective `O(5,5)`/`Pin(5,5)` data.

The file is an owner-level socket.  It does not construct concrete Clifford
algebras; it keeps the reflection/projective/conformal dependency graph honest.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.SplitCliffordZ2Four
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Split quadratic carrier and projective rays -/

/--
A real quadratic carrier intended to have split signature `(4,4)`.

The signature assertion is carried as a certificate so this file can remain
independent of a concrete matrix model.
-/
structure SplitQuadratic44
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Quadratic form. -/
  q : V → ℝ

  /-- Polar/symmetric bilinear pairing, left abstract at this layer. -/
  polar : V → V → ℝ

  /-- Quadratic scaling law. -/
  q_smul :
    ∀ (r : ℝ) (v : V), q (r • v) = r ^ 2 * q v

  /-- Symmetry of the polar pairing. -/
  polar_symm :
    ∀ v w : V, polar v w = polar w v

  /-- Nondegeneracy certificate. -/
  nondegenerate : Prop

  /-- Signature `(4,4)` certificate. -/
  signature44 : Prop

namespace SplitQuadratic44

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : SplitQuadratic44 V)

/-- Null/isotropic vectors for the split quadratic form. -/
def IsNull
    (v : V) : Prop :=
  Q.q v = 0

/-- Regular/non-null vectors. -/
def IsRegular
    (v : V) : Prop :=
  Q.q v ≠ 0

/-- Two nonzero representatives determine the same real projective ray. -/
def SameRay
    (v w : V) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ w = c • v

/-- Nullity is invariant under nonzero rescaling. -/
theorem isNull_of_sameRay
    {v w : V}
    (hvw : SameRay v w)
    (hv : Q.IsNull v) :
    Q.IsNull w := by
  rcases hvw with ⟨c, _hc, rfl⟩
  dsimp [IsNull]
  rw [Q.q_smul, hv]
  ring

/-- Regularity is invariant under nonzero rescaling. -/
theorem isRegular_of_sameRay
    {v w : V}
    (hvw : SameRay v w)
    (hv : Q.IsRegular v) :
    Q.IsRegular w := by
  rcases hvw with ⟨c, hc, rfl⟩
  dsimp [IsRegular]
  rw [Q.q_smul]
  exact mul_ne_zero (pow_ne_zero 2 hc) hv

end SplitQuadratic44

/--
A projective ray represented by a nonzero vector.

This is intentionally a representative-level socket rather than a quotient.
The equivalence relation is `SameProjectiveRay`.
-/
structure ProjectiveRay
    (V : Type*) [Zero V] where
  vec : V
  nonzero : vec ≠ 0

namespace ProjectiveRay

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Equality of represented projective rays by nonzero real scaling. -/
def SameProjectiveRay
    (r s : ProjectiveRay V) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ s.vec = c • r.vec

/-- A represented projective ray lies on the projective null quadric. -/
def IsNullRay
    (Q : SplitQuadratic44 V)
    (r : ProjectiveRay V) : Prop :=
  Q.IsNull r.vec

/-- A represented projective ray is regular/non-null. -/
def IsRegularRay
    (Q : SplitQuadratic44 V)
    (r : ProjectiveRay V) : Prop :=
  Q.IsRegular r.vec

/-- Null-ray membership is independent of nonzero representative. -/
theorem isNullRay_of_same
    (Q : SplitQuadratic44 V)
    {r s : ProjectiveRay V}
    (hrs : SameProjectiveRay r s)
    (hr : IsNullRay Q r) :
    IsNullRay Q s :=
  Q.isNull_of_sameRay hrs hr

end ProjectiveRay

/-! ## 2. O(4,4), components, and projective action -/

/-- A sign bit for orientation-like component data. -/
inductive OrientationBit where
  | preserves
  | reverses
deriving DecidableEq, Repr

/--
The four component labels of an indefinite orthogonal group.

For `O(4,4)` this is the abstract `V₄ ≃ Z₂ × Z₂` bookkeeping: one bit may be
read as ordinary determinant/orientation, the other as the complementary
positive/negative-plane orientation or time-orientation convention.
-/
structure O44Component where
  orientation : OrientationBit
  coorientation : OrientationBit
deriving DecidableEq, Repr

namespace O44Component

/-- Identity component label. -/
def identity : O44Component :=
  { orientation := OrientationBit.preserves
    coorientation := OrientationBit.preserves }

/-- A reflection-like component label. -/
def reflection : O44Component :=
  { orientation := OrientationBit.reverses
    coorientation := OrientationBit.preserves }

/-- A complementary/time-reflection-like component label. -/
def coreflection : O44Component :=
  { orientation := OrientationBit.preserves
    coorientation := OrientationBit.reverses }

/-- The total inversion/PT-like component label. -/
def totalInversion : O44Component :=
  { orientation := OrientationBit.reverses
    coorientation := OrientationBit.reverses }

end O44Component

/--
An element of the full split orthogonal group `O(4,4)`.

This deliberately uses the full orthogonal group rather than `SO(4,4)` so that
reflections, PT components, and chirality-flipping transformations remain
visible.
-/
structure Orthogonal44
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : SplitQuadratic44 V) where
  toLinearEquiv : V ≃ₗ[ℝ] V

  preserves_q :
    ∀ v : V, Q.q (toLinearEquiv v) = Q.q v

  component : O44Component

namespace Orthogonal44

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : SplitQuadratic44 V}

/-- Action of `O(4,4)` on represented projective rays. -/
def actRay
    (g : Orthogonal44 Q)
    (r : ProjectiveRay V) : ProjectiveRay V :=
  { vec := g.toLinearEquiv r.vec
    nonzero := by
      intro h
      apply r.nonzero
      have hsymm := congrArg g.toLinearEquiv.symm h
      simpa using hsymm }

/-- The `O(4,4)` action preserves the projective null quadric. -/
theorem actRay_preserves_null
    (g : Orthogonal44 Q)
    (r : ProjectiveRay V)
    (hr : r.IsNullRay Q) :
    (g.actRay r).IsNullRay Q := by
  dsimp [actRay, ProjectiveRay.IsNullRay, SplitQuadratic44.IsNull] at *
  rw [g.preserves_q]
  exact hr

/-- The `O(4,4)` action preserves regular/non-null projective rays. -/
theorem actRay_preserves_regular
    (g : Orthogonal44 Q)
    (r : ProjectiveRay V)
    (hr : r.IsRegularRay Q) :
    (g.actRay r).IsRegularRay Q := by
  dsimp [actRay, ProjectiveRay.IsRegularRay, SplitQuadratic44.IsRegular] at *
  rw [g.preserves_q]
  exact hr

/-- The projective action respects nonzero rescaling of ray representatives. -/
theorem actRay_respects_same
    (g : Orthogonal44 Q)
    {r s : ProjectiveRay V}
    (hrs : r.SameProjectiveRay s) :
    (g.actRay r).SameProjectiveRay (g.actRay s) := by
  rcases hrs with ⟨c, hc, hs⟩
  refine ⟨c, hc, ?_⟩
  dsimp [actRay]
  rw [hs]
  simp

end Orthogonal44

/-! ## 3. Pin(4,4) cover and chirality bridge -/

/-- Pin parity: even elements preserve Clifford chirality; odd elements may flip it. -/
inductive PinParity where
  | even
  | odd
deriving DecidableEq, Repr

/--
Abstract Pin cover of the full `O(4,4)` group.

Concrete Clifford modules should instantiate this socket with the actual Pin
group in `Cℓ(4,4)`.  The important architectural point is that this cover is
for the full orthogonal group, not just the special/identity component.
-/
structure Pin44CoverDatum
    {V PinEl : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl]
    (Q : SplitQuadratic44 V) where
  /-- The set of Pin elements. -/
  isPin : PinEl → Prop

  /-- Pin parity/grade bookkeeping. -/
  parity : PinEl → PinParity

  /-- The induced linear split-orthogonal transformation. -/
  cover : ∀ a : PinEl, isPin a → Orthogonal44 Q

  /-- Odd Pin elements are available; this is what Spin would lose. -/
  odd_reflection_socket : Prop

  /-- Even Pin elements form the Spin-like subcover. -/
  even_spin_subcover_socket : Prop

/--
A chiral volume/sign operator attached to the Pin cover.

This records the expected determinant/parity law as explicit data: even Pin
elements preserve chirality, odd/reflection elements flip chirality.
-/
structure PinChiralityActionDatum
    {V PinEl End : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl]
    [Monoid End] [Neg End]
    (Q : SplitQuadratic44 V)
    (Pin : Pin44CoverDatum (V := V) (PinEl := PinEl) Q) where
  chi : End

  chi_square :
    chi * chi = 1

  actionOnChi :
    PinEl → End

  /-- Even Pin elements preserve the chiral sign. -/
  even_preserves_chi :
    ∀ a : PinEl,
      Pin.isPin a → Pin.parity a = PinParity.even →
        actionOnChi a * chi = chi * actionOnChi a

  /-- Odd Pin elements reverse the chiral sign. -/
  odd_flips_chi :
    ∀ a : PinEl,
      Pin.isPin a → Pin.parity a = PinParity.odd →
        actionOnChi a * chi = -(chi * actionOnChi a)

/-! ## 4. Radial inversion and why base projectivization is not enough -/

namespace SplitQuadratic44

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : SplitQuadratic44 V)

/--
Radial/sphere inversion on the regular locus, written algebraically.

This is `x ↦ x / Q(x)` for the quadratic form normalization.
-/
def radialInversion
    (v : V) : V :=
  (Q.q v)⁻¹ • v

/--
On the base projective space `P(V)`, radial inversion is the same ray whenever
`Q(v) ≠ 0`.  Hence Möbius inversion is invisible if one only projectivizes the
base carrier `V`.
-/
theorem radialInversion_same_base_ray
    {v : V}
    (hv : Q.q v ≠ 0) :
    SameRay v (Q.radialInversion v) := by
  refine ⟨(Q.q v)⁻¹, inv_ne_zero hv, rfl⟩

end SplitQuadratic44

/-! ## 5. Conformal/projective Möbius extension -/

/--
An ambient split quadratic space for the conformal compactification.

For a base `(4,4)` carrier the conformal ambient signature is `(5,5)`.  The
Möbius inversion is linear/projective only in this ambient model.
-/
structure SplitQuadratic55
    (W : Type*) [AddCommGroup W] [Module ℝ W] where
  q : W → ℝ
  polar : W → W → ℝ

  q_smul :
    ∀ (r : ℝ) (w : W), q (r • w) = r ^ 2 * q w

  polar_symm :
    ∀ v w : W, polar v w = polar w v

  nondegenerate : Prop
  signature55 : Prop

/-- An element of the full ambient conformal orthogonal group `O(5,5)`. -/
structure Orthogonal55
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) where
  toLinearEquiv : W ≃ₗ[ℝ] W

  preserves_q :
    ∀ w : W, Q.q (toLinearEquiv w) = Q.q w

  component : O44Component

namespace Orthogonal55

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}

/-- Ambient `O(5,5)` action on represented projective rays. -/
def actRay
    (g : Orthogonal55 Q)
    (r : ProjectiveRay W) : ProjectiveRay W :=
  { vec := g.toLinearEquiv r.vec
    nonzero := by
      intro h
      apply r.nonzero
      have hsymm := congrArg g.toLinearEquiv.symm h
      simpa using hsymm }

end Orthogonal55

/--
A conformal compactification socket for the `(4,4)` base carrier.

The image of the base space lies in the projective null cone of the ambient
`(5,5)` space.  The distinguished `inversion` is an ambient orthogonal
transformation that implements Möbius/sphere inversion on the affine chart.
-/
structure ConformalMobius44Extension
    (V W : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] where
  baseQ : SplitQuadratic44 V
  ambientQ : SplitQuadratic55 W

  /-- Affine chart embedding into the ambient conformal model. -/
  embed : V → W

  /-- The embedded affine chart is null in the ambient quadratic form. -/
  embed_is_null :
    ∀ v : V, ambientQ.q (embed v) = 0

  /-- Projective ray of the embedded affine point. -/
  projectivePoint : V → ProjectiveRay W

  /-- Compatibility of the projective point representative with `embed`. -/
  projectivePoint_vec_eq :
    ∀ v : V, (projectivePoint v).vec = embed v

  /-- Ambient Möbius inversion, linear only after conformal extension. -/
  inversion : Orthogonal55 ambientQ

  /-- Certificate that the ambient inversion realizes affine sphere inversion. -/
  inversion_realizes_sphere_inversion : Prop

  /-- The base `O(4,4)` embeds into the conformal `O(5,5)` model. -/
  base_orthogonal_lift :
    Orthogonal44 baseQ → Orthogonal55 ambientQ

  /-- Translations/dilations/special conformal transformations may be added here. -/
  full_mobius_generation_certificate : Prop

/--
Abstract Pin cover of the ambient conformal group.

For Möbius inversion in signature `(4,4)`, the relevant Clifford cover is the
ambient `Pin(5,5)`, not merely the base `Pin(4,4)`.
-/
structure Pin55CoverDatum
    {W PinEl : Type*}
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinEl]
    (Q : SplitQuadratic55 W) where
  isPin : PinEl → Prop
  parity : PinEl → PinParity
  cover : ∀ a : PinEl, isPin a → Orthogonal55 Q

  /-- Ambient Pin element implementing the Möbius inversion. -/
  inversionPin : PinEl

  inversionPin_isPin :
    isPin inversionPin

  inversion_is_reflection_or_null_swap : Prop

/--
Combined base/conformal Pin architecture.

This is the precise formal replacement for saying "extend `Pin(4,4)` by
Möbius inversion": the base Pin data remains `Pin(4,4)`, while inversion lives
in the conformal ambient `Pin(5,5)` acting on projective null rays.
-/
structure PinMobiusProjective44
    (V W PinBase PinConf : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf] where
  mobius : ConformalMobius44Extension V W
  basePin : Pin44CoverDatum (V := V) (PinEl := PinBase) mobius.baseQ
  conformalPin : Pin55CoverDatum (W := W) (PinEl := PinConf) mobius.ambientQ

  /-- Compatibility certificate for embedding base Pin transformations upstairs. -/
  basePin_lifts_to_conformalPin : Prop

  /-- Projective states/rays are the declared target of the conformal action. -/
  acts_on_projective_null_rays : Prop

  /-- Reflection/chiral classification is retained by using Pin rather than Spin. -/
  reflection_and_chiral_classification_certificate : Prop

/-! ## 6. Owner target -/

/-- Compatibility predicate for constructing the O/Pin/Möbius projective stack. -/
def O44PinMobiusProjectiveCompatibility
    (V W PinBase PinConf : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf] : Prop :=
  True

/-- Owner target for the full reflection-sensitive projective conformal stack. -/
def O44PinMobiusProjectiveOwnerTarget : Prop :=
  ∀ (V W PinBase PinConf : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinBase] [Monoid PinConf],
    O44PinMobiusProjectiveCompatibility V W PinBase PinConf →
      Nonempty (PinMobiusProjective44 V W PinBase PinConf)

end InfoGeometry.OperatorAlgebra
