import Mathlib.Algebra.Group.Subgroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.PositiveHomogeneousBarrier

/-!
# Scale, topology, and shape readouts

This module packages `scale`, path-level `topology`/monodromy, and `shape` as
independent readouts of a common carrier.  It does **not** claim that every
geometric carrier canonically decomposes as an orthogonal product of these
three factors.

The generic interface records only maps and optional compatibility data.  A
product-coordinate equivalence is constructed only when bijectivity of the
joint readout is supplied explicitly.

A concrete specialization to the existing positive two-lane cone separates
two distinct motions:

* common positive scaling changes the logarithmic barrier coordinate and leaves
  the logarithmic shape ratio fixed;
* the existing reciprocal Cartan flow preserves the barrier coordinate and
  translates the logarithmic shape ratio.

No topological fibration, Cartan-decomposition theorem, geodesic-dynamics
claim, or identification of the operator square trichotomy with a symmetric
space is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ScaleTopologyShapeDatum

universe u v w z u' v' w' z'

/-- Three independent readouts on a common carrier.

`TopologyState` is intentionally abstract.  In intended applications it may be
an Artin/monodromy state, but the structure itself assumes no topology or
fibration. -/
structure ScaleTopologyShapeDatum
    (X : Type u)
    (ScaleState : Type v)
    (TopologyState : Type w)
    (ShapeState : Type z) where
  scale : X → ScaleState
  topology : X → TopologyState
  shape : X → ShapeState

namespace ScaleTopologyShapeDatum

variable {X : Type u}
variable {ScaleState : Type v}
variable {TopologyState : Type w}
variable {ShapeState : Type z}

/-- The simultaneous scale/topology/shape readout. -/
def jointReadout
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState) :
    X → ScaleState × (TopologyState × ShapeState) :=
  fun x => (D.scale x, (D.topology x, D.shape x))

/-- The three readouts distinguish points of the source carrier. -/
def IsJointlySeparating
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState) : Prop :=
  Function.Injective D.jointReadout

/-- Every formal triple of readout values is realized by the source carrier. -/
def IsJointlySurjective
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState) : Prop :=
  Function.Surjective D.jointReadout

/-- The joint readout is a genuine product-coordinate system. -/
def IsProductCoordinateSystem
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState) : Prop :=
  Function.Bijective D.jointReadout

/-- A genuine product equivalence, available only from an explicit bijectivity
proof. -/
def equivProduct
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState)
    (hD : D.IsProductCoordinateSystem) :
    X ≃ ScaleState × (TopologyState × ShapeState) :=
  Equiv.ofBijective D.jointReadout hD

/-- Pull readouts back along a map of source carriers. -/
def pullback
    {Y : Type u'}
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState)
    (f : Y → X) :
    ScaleTopologyShapeDatum Y ScaleState TopologyState ShapeState where
  scale := D.scale ∘ f
  topology := D.topology ∘ f
  shape := D.shape ∘ f

/-- Postcompose the three readouts independently. -/
def mapReadouts
    {ScaleState' : Type v'}
    {TopologyState' : Type w'}
    {ShapeState' : Type z'}
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState)
    (fScale : ScaleState → ScaleState')
    (fTopology : TopologyState → TopologyState')
    (fShape : ShapeState → ShapeState') :
    ScaleTopologyShapeDatum X ScaleState' TopologyState' ShapeState' where
  scale := fScale ∘ D.scale
  topology := fTopology ∘ D.topology
  shape := fShape ∘ D.shape

/-- A theorem-safe compatibility condition between the three outputs.

No compatibility is built into `ScaleTopologyShapeDatum`; concrete owners add
only the predicates they can prove. -/
def Satisfies
    (D : ScaleTopologyShapeDatum X ScaleState TopologyState ShapeState)
    (P : ScaleState → TopologyState → ShapeState → Prop) : Prop :=
  ∀ x, P (D.scale x) (D.topology x) (D.shape x)

/-- The tautological product-coordinate datum. -/
def productDatum :
    ScaleTopologyShapeDatum
      (ScaleState × (TopologyState × ShapeState))
      ScaleState TopologyState ShapeState where
  scale := fun x => x.1
  topology := fun x => x.2.1
  shape := fun x => x.2.2

@[simp]
theorem productDatum_jointReadout
    (x : ScaleState × (TopologyState × ShapeState)) :
    (productDatum
      (ScaleState := ScaleState)
      (TopologyState := TopologyState)
      (ShapeState := ShapeState)).jointReadout x = x := by
  rfl

/-- The tautological product datum is a genuine product-coordinate system. -/
theorem productDatum_isProductCoordinateSystem :
    (productDatum
      (ScaleState := ScaleState)
      (TopologyState := TopologyState)
      (ShapeState := ShapeState)).IsProductCoordinateSystem := by
  constructor
  · intro x y h
    simpa using h
  · intro y
    exact ⟨y, rfl⟩

end ScaleTopologyShapeDatum

/-! ## Optional Artin-to-Weyl compatibility -/

/-- A surjective path-level Artin/monodromy readout onto a discrete Weyl
carrier.  This is the algebraic datum behind

`1 → pure → Artin → Weyl → 1`,

without asserting a configuration-space realization. -/
structure ArtinWeylProjection
    (ArtinState : Type u)
    (WeylState : Type v)
    [Group ArtinState]
    [Group WeylState] where
  toWeyl : ArtinState →* WeylState
  surjective : Function.Surjective toWeyl

namespace ArtinWeylProjection

variable {ArtinState : Type u}
variable {WeylState : Type v}
variable [Group ArtinState]
variable [Group WeylState]

/-- The pure Artin subgroup is the native kernel of the Weyl projection. -/
def pureSubgroup
    (P : ArtinWeylProjection ArtinState WeylState) :
    Subgroup ArtinState :=
  P.toWeyl.ker

@[simp]
theorem mem_pureSubgroup_iff
    (P : ArtinWeylProjection ArtinState WeylState)
    (a : ArtinState) :
    a ∈ P.pureSubgroup ↔ P.toWeyl a = 1 :=
  Iff.rfl

end ArtinWeylProjection

/-- Optional compatibility when the shape output contains both a discrete Weyl
coordinate and an independent continuous-shape coordinate. -/
structure WeylShapeCompatible
    {X : Type u}
    {ScaleState : Type v}
    {ArtinState : Type w}
    {WeylState : Type z}
    {ContinuousShape : Type u'}
    [Group ArtinState]
    [Group WeylState]
    (D : ScaleTopologyShapeDatum
      X ScaleState ArtinState (WeylState × ContinuousShape))
    (P : ArtinWeylProjection ArtinState WeylState) : Prop where
  discreteShape_eq :
    ∀ x, (D.shape x).1 = P.toWeyl (D.topology x)

/-! ## Positive two-lane cone example -/

open InfoGeometry.Canonical.PositiveHomogeneousBarrier

/-- The existing positive homogeneous two-lane cone. -/
abbrev PositiveCone := PositiveHomogeneousCone

/-- Common positive scaling of both homogeneous lanes.

This is distinct from `reciprocalScale`, which scales the lanes inversely. -/
def commonScale
    (lambda : ℝ)
    (x : PositiveCone)
    (hlambda : 0 < lambda) : PositiveCone :=
  ⟨(lambda * x.1.1, lambda * x.1.2),
    ⟨mul_pos hlambda x.2.1, mul_pos hlambda x.2.2⟩⟩

@[simp]
theorem commonScale_one (x : PositiveCone) :
    commonScale 1 x one_pos = x := by
  apply Subtype.ext
  ext <;> simp [commonScale]

/-- Common positive scalings compose multiplicatively. -/
theorem commonScale_mul
    (lambda mu : ℝ)
    (x : PositiveCone)
    (hlambda : 0 < lambda)
    (hmu : 0 < mu) :
    commonScale (lambda * mu) x (mul_pos hlambda hmu) =
      commonScale lambda (commonScale mu x hmu) hlambda := by
  apply Subtype.ext
  ext <;> dsimp [commonScale] <;> ring

/-- Logarithmic shape coordinate: the difference of the two lane logs. -/
def logShape (x : PositiveCone) : ℝ :=
  Real.log x.1.1 - Real.log x.1.2

/-- The logarithmic barrier is a scale coordinate: common scaling changes it
by the expected degree-two logarithmic cocycle. -/
theorem barrier_commonScale
    (lambda : ℝ)
    (x : PositiveCone)
    (hlambda : 0 < lambda) :
    barrier (commonScale lambda x hlambda) =
      barrier x - 2 * Real.log lambda := by
  change
    -Real.log (lambda * x.1.1) - Real.log (lambda * x.1.2) =
      (-Real.log x.1.1 - Real.log x.1.2) - 2 * Real.log lambda
  rw [Real.log_mul (ne_of_gt hlambda) (ne_of_gt x.2.1)]
  rw [Real.log_mul (ne_of_gt hlambda) (ne_of_gt x.2.2)]
  ring

/-- The logarithmic shape ratio descends through common positive scaling. -/
theorem logShape_commonScale
    (lambda : ℝ)
    (x : PositiveCone)
    (hlambda : 0 < lambda) :
    logShape (commonScale lambda x hlambda) = logShape x := by
  change
    Real.log (lambda * x.1.1) - Real.log (lambda * x.1.2) =
      Real.log x.1.1 - Real.log x.1.2
  rw [Real.log_mul (ne_of_gt hlambda) (ne_of_gt x.2.1)]
  rw [Real.log_mul (ne_of_gt hlambda) (ne_of_gt x.2.2)]
  ring

/-- The positive cone as scale + trivial topology + shape readouts.

The trivial topology component is intentional: this concrete owner proves only
the radial/shape split.  Artin or Coxeter data must be supplied by a separate
carrier bridge. -/
def positiveConeDatum :
    ScaleTopologyShapeDatum PositiveCone ℝ Unit ℝ where
  scale := barrier
  topology := fun _ => ()
  shape := logShape

/-- Joint readout under common positive scaling: only the scale coordinate
changes. -/
theorem positiveCone_jointReadout_commonScale
    (lambda : ℝ)
    (x : PositiveCone)
    (hlambda : 0 < lambda) :
    positiveConeDatum.jointReadout (commonScale lambda x hlambda) =
      (barrier x - 2 * Real.log lambda, ((), logShape x)) := by
  change
    (barrier (commonScale lambda x hlambda),
      ((), logShape (commonScale lambda x hlambda))) =
      (barrier x - 2 * Real.log lambda, ((), logShape x))
  rw [barrier_commonScale, logShape_commonScale]

/-- The reciprocal Cartan flow translates the shape coordinate by `2t`. -/
theorem logShape_cartanFlow
    (t : ℝ)
    (x : PositiveCone) :
    logShape (cartanFlow t x) = logShape x + 2 * t := by
  change
    Real.log (Real.exp t * x.1.1) -
        Real.log (Real.exp (-t) * x.1.2) =
      (Real.log x.1.1 - Real.log x.1.2) + 2 * t
  rw [Real.log_mul (ne_of_gt (Real.exp_pos t)) (ne_of_gt x.2.1)]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos (-t))) (ne_of_gt x.2.2)]
  rw [Real.log_exp, Real.log_exp]
  ring

/-- Joint readout under the reciprocal Cartan flow: scale is fixed and only
shape moves. -/
theorem positiveCone_jointReadout_cartanFlow
    (t : ℝ)
    (x : PositiveCone) :
    positiveConeDatum.jointReadout (cartanFlow t x) =
      (barrier x, ((), logShape x + 2 * t)) := by
  change
    (barrier (cartanFlow t x), ((), logShape (cartanFlow t x))) =
      (barrier x, ((), logShape x + 2 * t))
  rw [barrier_cartanFlow_invariant, logShape_cartanFlow]

end InfoGeometry.Canonical.ScaleTopologyShapeDatum
