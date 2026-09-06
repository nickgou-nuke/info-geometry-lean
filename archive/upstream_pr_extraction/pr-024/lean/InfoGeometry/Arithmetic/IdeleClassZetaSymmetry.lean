import Mathlib
import InfoGeometry.Canonical.BostConnesGalois
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

Algebraic symmetry layers for the coordinate-independent zeta/Bost--Connes
story.

The actual idele class group of `ℚ`,

`C_ℚ = 𝔸_ℚˣ / ℚˣ`,

is not constructed in this file.  Instead this module formalizes the
kernel-checkable layer decomposition used by the existing Bost--Connes owners:

* a positive real scale layer, represented by its additive log coordinate;
* an arithmetic/Galois layer, represented abstractly by the existing
  `GaloisActionData` owner for `Zhat^* ≃ Gal(ℚᵃᵇ/ℚ)`;
* an external Fourier/Pontryagin `Z₂` duality, acting by inversion on the
  scale and arithmetic layers and by the critical mirror on centered zeta
  coordinates.

No RH statement, KMS-state classification, Tate thesis, class-field-theory
isomorphism, or full adelic quotient theorem is proved here.  Those can be
supplied through the explicit decomposition packet below.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

open InfoGeometry.Canonical.BostConnesGalois
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-! ## Positive scale layer -/

/-- Positive real scale, the multiplicative `ℝ^*_+` layer. -/
structure PositiveScale where
  val : ℝ
  pos : 0 < val

namespace PositiveScale

@[ext] theorem ext {a b : PositiveScale} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp_all

/-- Identity positive scale. -/
def one : PositiveScale :=
  ⟨1, by norm_num⟩

/-- Multiplication of positive scales. -/
def mul (a b : PositiveScale) : PositiveScale :=
  ⟨a.val * b.val, mul_pos a.pos b.pos⟩

/-- Inverse positive scale. -/
def inv (a : PositiveScale) : PositiveScale :=
  ⟨a.val⁻¹, inv_pos.mpr a.pos⟩

@[simp] theorem one_val : one.val = 1 := rfl

@[simp] theorem mul_val (a b : PositiveScale) :
    (mul a b).val = a.val * b.val := rfl

@[simp] theorem inv_val (a : PositiveScale) :
    (inv a).val = a.val⁻¹ := rfl

theorem one_mul (a : PositiveScale) :
    mul one a = a := by
  ext
  simp [mul, one]

theorem mul_one (a : PositiveScale) :
    mul a one = a := by
  ext
  simp [mul, one]

theorem mul_assoc (a b c : PositiveScale) :
    mul (mul a b) c = mul a (mul b c) := by
  ext
  simp [mul]
  ring

theorem mul_inv (a : PositiveScale) :
    mul a (inv a) = one := by
  ext
  exact mul_inv_cancel₀ (ne_of_gt a.pos)

theorem inv_mul (a : PositiveScale) :
    mul (inv a) a = one := by
  ext
  exact inv_mul_cancel₀ (ne_of_gt a.pos)

/-- Additive logarithmic coordinate of the positive scale layer. -/
def logCoord (a : PositiveScale) : ℝ :=
  Real.log a.val

/-- Multiplication of positive scales becomes addition in log coordinates. -/
theorem logCoord_mul (a b : PositiveScale) :
    logCoord (mul a b) = logCoord a + logCoord b := by
  unfold logCoord
  simp [mul, Real.log_mul (ne_of_gt a.pos) (ne_of_gt b.pos)]

end PositiveScale

/-! ## Log-coordinate idele class layer -/

/--
Layer decomposition shadow for `C_ℚ`.

`logScale` is the additive coordinate of `ℝ^*_+`; `arithmetic` is the
profinite/Galois layer.  For the rational field this is the layer structure
behind `C_ℚ ≃ ℝ^*_+ × Zhat^*`, with the actual adelic quotient supplied by
`RationalIdeleClassDecomposition` when needed.
-/
structure IdeleClassLayer (G : Type*) where
  logScale : ℝ
  arithmetic : G

namespace IdeleClassLayer

variable {G : Type*}

@[ext] theorem ext {A B : IdeleClassLayer G}
    (hlog : A.logScale = B.logScale) (harith : A.arithmetic = B.arithmetic) :
    A = B := by
  cases A
  cases B
  simp_all

section Group

variable [Group G]

/-- Identity layer. -/
def identity : IdeleClassLayer G :=
  ⟨0, 1⟩

/-- Componentwise product: log-scales add and arithmetic symmetries multiply. -/
def compose (A B : IdeleClassLayer G) : IdeleClassLayer G :=
  ⟨A.logScale + B.logScale, A.arithmetic * B.arithmetic⟩

/-- Componentwise inverse. -/
def inverse (A : IdeleClassLayer G) : IdeleClassLayer G :=
  ⟨-A.logScale, A.arithmetic⁻¹⟩

@[simp] theorem identity_compose (A : IdeleClassLayer G) :
    compose identity A = A := by
  ext <;> simp [compose, identity]

@[simp] theorem compose_identity (A : IdeleClassLayer G) :
    compose A identity = A := by
  ext <;> simp [compose, identity]

theorem compose_assoc (A B C : IdeleClassLayer G) :
    compose (compose A B) C = compose A (compose B C) := by
  ext
  · simp [compose, add_assoc]
  · simp [compose, mul_assoc]

@[simp] theorem compose_inverse (A : IdeleClassLayer G) :
    compose A (inverse A) = identity := by
  ext
  · simp [compose, inverse, identity]
  · simp [compose, inverse, identity]

@[simp] theorem inverse_compose (A : IdeleClassLayer G) :
    compose (inverse A) A = identity := by
  ext
  · simp [compose, inverse, identity]
  · simp [compose, inverse, identity]

/-- Positive-scale action on a real inverse-temperature/log-temperature coordinate. -/
def actOnLogTemperature (A : IdeleClassLayer G) (beta : ℝ) : ℝ :=
  beta + A.logScale

/-- The scale action composes according to the layer product. -/
theorem actOnLogTemperature_compose
    (A B : IdeleClassLayer G) (beta : ℝ) :
    actOnLogTemperature (compose A B) beta =
      actOnLogTemperature A (actOnLogTemperature B beta) := by
  simp [actOnLogTemperature, compose]
  ring

end Group

/-! ## Bost--Connes arithmetic readout -/

section BostConnes

universe u

variable
    {C_comm : Type u} [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm)
    {G : Type u} [GaloisActionData G]
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G))

/--
Cyclotomic generator action of the arithmetic layer.  The scale coordinate is
irrelevant for this finite Bost--Connes boundary readout.
-/
def arithmeticGeneratorAction
    (A : IdeleClassLayer G) (r : ℚ) : C_comm :=
  e_rep.e (GaloisActionData.actOnQ A.arithmetic r)

/-- The arithmetic layer action is exactly the existing Bost--Connes Galois action. -/
theorem galoisAut_on_generator_eq_arithmeticGeneratorAction
    (A : IdeleClassLayer G) (r : ℚ) :
    galoisAut.galoisAut A.arithmetic (e_rep.e r) =
      arithmeticGeneratorAction e_rep A r := by
  simp [arithmeticGeneratorAction, galoisAut.galoisAut_on_generator]

/-- Changing only the scale coordinate does not change the cyclotomic generator action. -/
theorem arithmeticGeneratorAction_eq_of_same_arithmetic
    {A B : IdeleClassLayer G} (h : A.arithmetic = B.arithmetic) (r : ℚ) :
    arithmeticGeneratorAction e_rep A r =
      arithmeticGeneratorAction e_rep B r := by
  simp [arithmeticGeneratorAction, h]

end BostConnes

end IdeleClassLayer

/-! ## Fourier/Pontryagin `Z₂` duality -/

/-- External Fourier/Pontryagin duality label. -/
inductive FourierParity where
  | identity
  | dual
  deriving DecidableEq

namespace FourierParity

variable {G : Type*}

/-- Group law on the external `Z₂` Fourier/Pontryagin parity. -/
def compose : FourierParity → FourierParity → FourierParity
  | FourierParity.identity, q => q
  | p, FourierParity.identity => p
  | FourierParity.dual, FourierParity.dual => FourierParity.identity

@[simp] theorem identity_compose (p : FourierParity) :
    compose FourierParity.identity p = p := by
  cases p <;> rfl

@[simp] theorem compose_identity (p : FourierParity) :
    compose p FourierParity.identity = p := by
  cases p <;> rfl

@[simp] theorem compose_self (p : FourierParity) :
    compose p p = FourierParity.identity := by
  cases p <;> rfl

theorem compose_assoc (p q r : FourierParity) :
    compose (compose p q) r = compose p (compose q r) := by
  cases p <;> cases q <;> cases r <;> rfl

/--
Fourier duality on the idele-class layers:
`(log λ, g) ↦ (-log λ, g⁻¹)`.
-/
def actOnIdele [Group G] :
    FourierParity → IdeleClassLayer G → IdeleClassLayer G
  | FourierParity.identity, A => A
  | FourierParity.dual, A => IdeleClassLayer.inverse A

/-- The Fourier layer is involutive on idele layers. -/
theorem actOnIdele_involutive [Group G] (p : FourierParity) :
    Function.Involutive (actOnIdele (G := G) p) := by
  intro A
  cases p <;> cases A <;>
    ext <;> simp [actOnIdele, IdeleClassLayer.inverse]

/-- The parity action respects the `Z₂` composition law. -/
theorem actOnIdele_compose_parity [Group G]
    (p q : FourierParity) (A : IdeleClassLayer G) :
    actOnIdele (compose p q) A = actOnIdele p (actOnIdele q A) := by
  cases p <;> cases q <;> cases A <;>
    ext <;> simp [compose, actOnIdele, IdeleClassLayer.inverse]

/--
For the abelian arithmetic layer `Zhat^*`, Fourier duality is a homomorphism
on the product decomposition.
-/
theorem dual_actOnIdele_compose [CommGroup G]
    (A B : IdeleClassLayer G) :
    actOnIdele FourierParity.dual (IdeleClassLayer.compose A B) =
      IdeleClassLayer.compose
        (actOnIdele FourierParity.dual A)
        (actOnIdele FourierParity.dual B) := by
  ext
  · simp [actOnIdele, IdeleClassLayer.compose, IdeleClassLayer.inverse]
    ring
  · simp [actOnIdele, IdeleClassLayer.compose, IdeleClassLayer.inverse, mul_comm]

/-- Fourier duality on centered zeta coordinates is the critical mirror. -/
def actOnCentered :
    FourierParity → ZetaCenteredChart → ZetaCenteredChart
  | FourierParity.identity, x => x
  | FourierParity.dual, x => criticalMirror x

/-- The Fourier layer is involutive on centered zeta coordinates. -/
theorem actOnCentered_involutive (p : FourierParity) :
    Function.Involutive (actOnCentered p) := by
  intro x
  cases p
  · rfl
  · exact criticalMirror_involutive x

/-- The centered-coordinate parity action respects the `Z₂` composition law. -/
theorem actOnCentered_compose_parity
    (p q : FourierParity) (x : ZetaCenteredChart) :
    actOnCentered (compose p q) x = actOnCentered p (actOnCentered q x) := by
  cases p <;> cases q <;> ext <;>
    simp [compose, actOnCentered, criticalMirror]

/-- The fixed locus of Fourier duality in centered coordinates is `u = 0`. -/
theorem dual_fixed_iff_centeredCriticalLine (x : ZetaCenteredChart) :
    actOnCentered FourierParity.dual x = x ↔ x.u = 0 := by
  constructor
  · intro h
    have hu := congrArg ZetaCenteredChart.u h
    simp [actOnCentered, criticalMirror] at hu
    linarith
  · intro h
    ext <;> simp [actOnCentered, criticalMirror, h]

end FourierParity

/-! ## Three-layer idele-class symmetry shadow -/

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
This section proves the finite algebra of the three-layer shadow:

* additive positive-scale/log layer;
* arithmetic/Galois layer;
* Fourier/Pontryagin `Z₂` layer acting by inversion.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`StrictUnitaryBinding` and `BostConnesTraceRealizesZeta` below are explicit
predicates.  They name the analytic/spectral claims rather than proving them.

#### BUCKET 3: OPEN CLOSURE DEBT
Full ideles, class-field theory, Bost--Connes KMS classification, absorption
spectrum, and RH are outside this finite algebraic corridor.
-/

/--
Three-layer symmetry element:

* `layer.logScale` models the continuous `ℝ⁎₊` scale in additive log
  coordinates;
* `layer.arithmetic` models the profinite arithmetic/Galois unit;
* `parity` models the Fourier/Pontryagin `Z₂` involution.
-/
structure ThreeLayerIdeleSymmetry (G : Type*) where
  layer : IdeleClassLayer G
  parity : FourierParity

namespace ThreeLayerIdeleSymmetry

variable {G : Type*}

@[ext] theorem ext {A B : ThreeLayerIdeleSymmetry G}
    (hlayer : A.layer = B.layer) (hparity : A.parity = B.parity) : A = B := by
  cases A
  cases B
  simp_all

section CommGroup

variable [CommGroup G]

/-- Identity element of the three-layer semidirect product shadow. -/
def identity : ThreeLayerIdeleSymmetry G :=
  ⟨IdeleClassLayer.identity, FourierParity.identity⟩

/--
Semidirect product composition.  A nontrivial Fourier parity on the left
inverts the right idele layer before multiplication.
-/
def compose (A B : ThreeLayerIdeleSymmetry G) : ThreeLayerIdeleSymmetry G :=
  ⟨IdeleClassLayer.compose A.layer
      (FourierParity.actOnIdele A.parity B.layer),
    FourierParity.compose A.parity B.parity⟩

@[simp] theorem identity_compose (A : ThreeLayerIdeleSymmetry G) :
    compose identity A = A := by
  cases A with
  | mk layer parity =>
    cases layer
    cases parity <;>
      ext <;>
      simp [compose, identity, IdeleClassLayer.compose, IdeleClassLayer.identity,
        FourierParity.actOnIdele]

@[simp] theorem compose_identity (A : ThreeLayerIdeleSymmetry G) :
    compose A identity = A := by
  cases A with
  | mk layer parity =>
    cases layer
    cases parity <;>
      ext <;>
      simp [compose, identity, IdeleClassLayer.compose, IdeleClassLayer.identity,
        FourierParity.actOnIdele, IdeleClassLayer.inverse]

end CommGroup

/-- Action on centered zeta coordinates remembers only the Fourier parity layer. -/
def actOnCentered (A : ThreeLayerIdeleSymmetry G) (x : ZetaCenteredChart) :
    ZetaCenteredChart :=
  FourierParity.actOnCentered A.parity x

/-- Action on log-temperature remembers the continuous scale layer. -/
def actOnLogTemperature (A : ThreeLayerIdeleSymmetry G) (beta : ℝ) : ℝ :=
  beta + A.layer.logScale

/-- The Fourier-dual element reflects centered coordinates across the critical line. -/
theorem dual_reflects_centered
    (A : ThreeLayerIdeleSymmetry G) (h : A.parity = FourierParity.dual)
    (x : ZetaCenteredChart) :
    actOnCentered A x = criticalMirror x := by
  simp [actOnCentered, h, FourierParity.actOnCentered]

/-- Fixed points of a Fourier-dual three-layer element are exactly on `u = 0`. -/
theorem dual_fixed_iff_centeredCriticalLine
    (A : ThreeLayerIdeleSymmetry G) (h : A.parity = FourierParity.dual)
    (x : ZetaCenteredChart) :
    actOnCentered A x = x ↔ x.u = 0 := by
  simp [actOnCentered, h, FourierParity.dual_fixed_iff_centeredCriticalLine]

/--
Conservative RH-style binding predicate.

It says that every zero/spectral point supplied by a model lies on the fixed
surface of the Fourier-dual involution.  This is a definition, not a proof of
RH or of a spectral realization.
-/
def StrictUnitaryBinding (IsZero : ZetaCenteredChart → Prop) : Prop :=
  ∀ z, IsZero z → z.u = 0

/-- Under `StrictUnitaryBinding`, a zero cannot sit off the critical fixed line. -/
theorem no_off_critical_zero
    {IsZero : ZetaCenteredChart → Prop}
    (hbind : StrictUnitaryBinding IsZero)
    {z : ZetaCenteredChart}
    (hz : IsZero z) :
    z.u = 0 :=
  hbind z hz

/--
Trace/partition predicate for a Bost--Connes model realizing a zeta readout.

The actual analytic trace-class theorem is not asserted here; callers must
supply this predicate for their concrete operator algebra.
-/
def BostConnesTraceRealizesZeta
    {State : Type*}
    (tracePartition : State → ℂ)
    (zetaReadout : ℂ → ℂ)
    (temperature : State → ℂ) : Prop :=
  ∀ s, tracePartition s = zetaReadout (temperature s)

/-- A supplied trace-realization predicate gives the corresponding readout equality. -/
theorem tracePartition_eq_zetaReadout
    {State : Type*}
    {tracePartition : State → ℂ}
    {zetaReadout : ℂ → ℂ}
    {temperature : State → ℂ}
    (h : BostConnesTraceRealizesZeta tracePartition zetaReadout temperature)
    (s : State) :
    tracePartition s = zetaReadout (temperature s) :=
  h s

end ThreeLayerIdeleSymmetry

/-! ## Proof-carrying adelic quotient socket -/

/--
Proof-carrying decomposition packet for a concrete construction of the rational
idele class group.

Supplying this packet is the precise place where a future full adelic owner can
prove that its quotient model is equivalent to the product of the positive-scale
and arithmetic/Galois layers.  This module only consumes that equivalence.
-/
structure RationalIdeleClassDecomposition (ClassGroup G : Type*) where
  toLayers : ClassGroup → IdeleClassLayer G
  fromLayers : IdeleClassLayer G → ClassGroup
  left_inv : ∀ c : ClassGroup, fromLayers (toLayers c) = c
  right_inv : ∀ x : IdeleClassLayer G, toLayers (fromLayers x) = x

namespace RationalIdeleClassDecomposition

variable {ClassGroup G : Type*}
variable (D : RationalIdeleClassDecomposition ClassGroup G)

/-- Round-trip from an idele class to the layer decomposition and back. -/
theorem from_to (c : ClassGroup) :
    D.fromLayers (D.toLayers c) = c :=
  D.left_inv c

/-- Round-trip from layer data to the class-group model and back. -/
theorem to_from (x : IdeleClassLayer G) :
    D.toLayers (D.fromLayers x) = x :=
  D.right_inv x

end RationalIdeleClassDecomposition

end InfoGeometry.Arithmetic.IdeleClassZetaSymmetry
