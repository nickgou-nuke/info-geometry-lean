/-
InfoGeometry/Geometry/BilingualPoincareMetric.lean

Invariant Poincare metric layer for the bilingual upper half-plane.

The metric is local: it pairs tangent operators at a point.  It is not defined
from the raw point commutator `[Z₁,Z₂]`, since scalar-chart upper-half-plane
points commute.

The central invariant object is the quadratic form on phase-linear tangent
operators and its covariance under the derivative of the operator Mobius
action.
-/

import Mathlib.Tactic
import InfoGeometry.Geometry.BilingualUpperHalfPlane
import InfoGeometry.Geometry.KreinIsotropicCone
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Geometry

open scoped InnerProductSpace

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Quantum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => DoubledEnd E

namespace BilingualUpperHalfPlane

variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}

/-! ## Phase-linear endomorphism closures -/

namespace PhaseLinear

/--
The zero endomorphism is phase-linear.
-/
theorem zero :
    PhaseLinear D (0 : EndH) := by
  apply ContinuousLinearMap.ext
  intro v
  simp

/--
The identity endomorphism is phase-linear.
-/
theorem one :
    PhaseLinear D (1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro v
  simp

/--
The negative of a phase-linear endomorphism is phase-linear.
-/
theorem neg
    {T : EndH}
    (hT : PhaseLinear D T) :
    PhaseLinear D (-T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [PhaseLinear.map_K hT v]

/--
The difference of phase-linear endomorphisms is phase-linear.
-/
theorem sub
    {S T : EndH}
    (hS : PhaseLinear D S)
    (hT : PhaseLinear D T) :
    PhaseLinear D (S - T) := by
  simpa [sub_eq_add_neg] using PhaseLinear.add hS (PhaseLinear.neg hT)

/--
Real scalar multiples of phase-linear endomorphisms are phase-linear.
-/
theorem smul
    (a : ℝ)
    {T : EndH}
    (hT : PhaseLinear D T) :
    PhaseLinear D (a • T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [PhaseLinear.map_K hT v]

end PhaseLinear

/--
The defining phase-linearity field of an upper-half-plane point, re-exported
as a `PhaseLinear` proof.
-/
theorem tau_phaseLinear
    (Z : BilingualUpperHalfPlane D) :
    PhaseLinear D Z.tau :=
  Z.phase_linear

/-! ## Native K-height form -/

/--
The native Krein-Hestenes height form attached to an upper-half-plane point.

In the scalar shadow `τ = x I + y K`, this is the operatorial replacement for
the positive height `y`.
-/
def kHeightForm
    (Z : BilingualUpperHalfPlane D)
    (v w : H₂) : ℝ :=
  -⟪v, D.K (Z.tau w)⟫_ℝ

/--
The height form is strictly positive on nonzero diagonal vectors.
-/
theorem kHeightForm_pos
    (Z : BilingualUpperHalfPlane D)
    (v : H₂)
    (hv : v ≠ 0) :
    0 < kHeightForm Z v v := by
  dsimp [kHeightForm]
  exact neg_pos.mpr (Z.K_positivity v hv)

/--
The diagonal height observable.
-/
def kHeightQuadratic
    (Z : BilingualUpperHalfPlane D)
    (v : H₂) : ℝ :=
  kHeightForm Z v v

/--
The diagonal height observable is positive on nonzero vectors.
-/
theorem kHeightQuadratic_pos
    (Z : BilingualUpperHalfPlane D)
    (v : H₂)
    (hv : v ≠ 0) :
    0 < kHeightQuadratic Z v :=
  kHeightForm_pos Z v hv

/-! ## Coordinate-free imaginary-height surface -/

/--
The positive imaginary quadratic form attached to an operatorial upper-half-plane
point.

This is the coordinate-free replacement for the scalar condition `Im z = y > 0`.
-/
def imaginaryQuadratic (Z : BilingualUpperHalfPlane D) (v : H₂) : ℝ :=
  -⟪v, D.K (Z.tau v)⟫_ℝ

/-- The imaginary quadratic form is the diagonal `K`-height quadratic form. -/
@[simp]
theorem imaginaryQuadratic_eq_kHeightQuadratic
    (Z : BilingualUpperHalfPlane D)
    (v : H₂) :
    imaginaryQuadratic Z v = kHeightQuadratic Z v :=
  rfl

/--
The positivity ax!om of the upper half-plane says exactly that
`imaginaryQuadratic Z` is strictly positive away from zero.
-/
theorem imaginaryQuadratic_pos
    (Z : BilingualUpperHalfPlane D)
    {v : H₂} (hv : v ≠ 0) :
    0 < imaginaryQuadratic Z v := by
  rw [imaginaryQuadratic_eq_kHeightQuadratic]
  exact kHeightQuadratic_pos (D := D) Z v hv

/--
The symmetric bilinear imaginary form associated to `Z`.

This is the polarization of the real quadratic condition visible to the metric.
It avoids assuming, prematurely, that `K ∘ τ` is self-adjoint.
-/
def imaginaryForm (Z : BilingualUpperHalfPlane D) (v w : H₂) : ℝ :=
  - (1 / 2 : ℝ) *
    (⟪v, D.K (Z.tau w)⟫_ℝ +
      ⟪w, D.K (Z.tau v)⟫_ℝ)

/-- On the diagonal, the symmetric imaginary form is the positive quadratic form. -/
theorem imaginaryForm_diag
    (Z : BilingualUpperHalfPlane D)
    (v : H₂) :
    imaginaryForm Z v v = imaginaryQuadratic Z v := by
  unfold imaginaryForm imaginaryQuadratic
  ring

/-- Hence the imaginary form is strictly positive on nonzero diagonal vectors. -/
theorem imaginaryForm_pos
    (Z : BilingualUpperHalfPlane D)
    {v : H₂} (hv : v ≠ 0) :
    0 < imaginaryForm Z v v := by
  rw [imaginaryForm_diag]
  exact imaginaryQuadratic_pos Z hv

/--
Riesz/operator representative of the imaginary form.

This is intentionally packaged as structure rather than inferred automatically:
in infinite dimension, strict positivity of the quadratic form does not by
itself supply a bounded inverse operator.
-/
structure ImaginaryRiesz (Z : BilingualUpperHalfPlane D) where
  /-- Invertible positive operator representing the imaginary form. -/
  unit : Units EndH
  /-- The unit value represents the imaginary form by the real inner product. -/
  form_eq :
    ∀ v w : H₂,
      imaginaryForm Z v w = ⟪v, unit.val w⟫_ℝ
  /-- Strict positivity of the representing operator. -/
  positive :
    ∀ v : H₂, v ≠ 0 → 0 < ⟪v, unit.val v⟫_ℝ

namespace ImaginaryRiesz

variable {Z : BilingualUpperHalfPlane D}

/-- Positive imaginary operator derived from the invertible owner. -/
abbrev Y (R : ImaginaryRiesz Z) : DoubledEnd E :=
  R.unit.val

@[simp]
theorem unit_eq (R : ImaginaryRiesz Z) : R.unit.val = Y R :=
  rfl

end ImaginaryRiesz

/--
A coordinate-free trace datum.

Concrete instances can later be supplied from finite-dimensional trace,
Hilbert-Schmidt trace, or a Krein-compatible renormalized trace.
-/
structure TraceDatum where
  /-- Trace functional on endomorphisms of the doubled carrier. -/
  tr : EndH → ℝ
  /-- Cyclicity, the essential invariant property needed for metric symmetry. -/
  cyclic : ∀ A B : EndH, tr (A.comp B) = tr (B.comp A)

/-! ## Operator Mobius data -/

/--
Phase-linear block coefficients for an operator Mobius transformation.

The block usually denoted `D` is called `Dop` to avoid shadowing the datum `D`.
-/
structure PhaseLinearMobiusCoefficients
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) where
  A : EndH
  B : EndH
  C : EndH
  Dop : EndH

  A_phase : PhaseLinear D A
  B_phase : PhaseLinear D B
  C_phase : PhaseLinear D C
  D_phase : PhaseLinear D Dop

/--
Numerator of the operator Mobius expression:

`A τ + B`.
-/
def mobiusNumerator
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D) : EndH :=
  M.A.comp Z.tau + M.B

/--
Denominator of the operator Mobius expression:

`C τ + D`.
-/
def mobiusDenominator
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D) : EndH :=
  M.C.comp Z.tau + M.Dop

/--
The numerator is phase-linear.
-/
theorem mobiusNumerator_phaseLinear
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D) :
    PhaseLinear D (mobiusNumerator M Z) := by
  dsimp [mobiusNumerator]
  exact PhaseLinear.add
    (PhaseLinear.comp M.A_phase Z.tau_phaseLinear)
    M.B_phase

/--
The denominator is phase-linear.
-/
theorem mobiusDenominator_phaseLinear
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D) :
    PhaseLinear D (mobiusDenominator M Z) := by
  dsimp [mobiusDenominator]
  exact PhaseLinear.add
    (PhaseLinear.comp M.C_phase Z.tau_phaseLinear)
    M.D_phase

/--
Explicit inverse datum for the Mobius denominator.

The inverse is packaged as data because, in infinite dimension, positivity or
injectivity does not automatically provide a bounded inverse.
-/
structure MobiusDenominatorInverse
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D) where
  inv : EndH

  denom_inv :
    (mobiusDenominator M Z).comp inv = 1

  inv_denom :
    inv.comp (mobiusDenominator M Z) = 1

  inv_phase_linear :
    PhaseLinear D inv

/--
The upper-half-plane positivity predicate for an arbitrary candidate operator.
-/
def KHalfPlanePositive
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (T : EndH) : Prop :=
  ∀ v : H₂, v ≠ 0 →
    ⟪v, D.K (T v)⟫_ℝ < (0 : ℝ)

/--
The raw operator underlying the Mobius action:

`(Aτ + B) (Cτ + D)⁻¹`.
-/
def moebiusActionOperator
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z) : EndH :=
  (mobiusNumerator M Z).comp hInv.inv

/--
The raw Mobius action operator is phase-linear.
-/
theorem moebiusActionOperator_phaseLinear
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z) :
    PhaseLinear D (moebiusActionOperator M Z hInv) := by
  dsimp [moebiusActionOperator]
  exact PhaseLinear.comp
    (mobiusNumerator_phaseLinear M Z)
    hInv.inv_phase_linear

/--
The proof-carrying Mobius action on the bilingual upper half-plane.

The positivity proof is supplied as a property. A later group-level theorem
should prove it from the appropriate Krein/symplectic block conditions.
-/
def moebiusAction
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z)
    (hPos : KHalfPlanePositive D (moebiusActionOperator M Z hInv)) :
    BilingualUpperHalfPlane D where
  tau := moebiusActionOperator M Z hInv
  phase_linear := moebiusActionOperator_phaseLinear M Z hInv
  K_positivity := hPos

/-! ## Tangent operators -/

/--
A tangent operator at a bilingual upper-half-plane point.

The upper half-plane is modeled as an open positivity region inside the
phase-linear endomorphisms, so tangent directions are phase-linear operator
variations.
-/
structure TangentAt
    (Z : BilingualUpperHalfPlane D) where
  op : EndH
  phase_linear : PhaseLinear D op

namespace TangentAt

variable {Z : BilingualUpperHalfPlane D}

/-- Extensionality for tangent operators. -/
@[ext]
theorem ext
    {V W : TangentAt Z}
    (h : V.op = W.op) :
    V = W := by
  cases V
  cases W
  cases h
  rfl

/--
The zero tangent operator.
-/
def zero (Z : BilingualUpperHalfPlane D) : TangentAt Z where
  op := 0
  phase_linear := PhaseLinear.zero

instance (Z : BilingualUpperHalfPlane D) : Zero (TangentAt Z) where
  zero := zero Z

@[simp]
theorem zero_op
    (Z : BilingualUpperHalfPlane D) :
    (0 : TangentAt Z).op = 0 :=
  rfl

/--
Addition of tangent operators.
-/
def add
    (V W : TangentAt Z) : TangentAt Z where
  op := V.op + W.op
  phase_linear := PhaseLinear.add V.phase_linear W.phase_linear

instance (Z : BilingualUpperHalfPlane D) : Add (TangentAt Z) where
  add := add

@[simp]
theorem add_op
    (V W : TangentAt Z) :
    (V + W).op = V.op + W.op :=
  rfl

/--
Negation of tangent operators.
-/
def neg
    (V : TangentAt Z) : TangentAt Z where
  op := -V.op
  phase_linear := PhaseLinear.neg V.phase_linear

instance (Z : BilingualUpperHalfPlane D) : Neg (TangentAt Z) where
  neg := neg

@[simp]
theorem neg_op
    (V : TangentAt Z) :
    (-V).op = -V.op :=
  rfl

/--
Subtraction of tangent operators.
-/
def sub
    (V W : TangentAt Z) : TangentAt Z where
  op := V.op - W.op
  phase_linear := PhaseLinear.sub V.phase_linear W.phase_linear

instance (Z : BilingualUpperHalfPlane D) : Sub (TangentAt Z) where
  sub := sub

@[simp]
theorem sub_op
    (V W : TangentAt Z) :
    (V - W).op = V.op - W.op :=
  rfl

/--
Real scalar multiplication of tangent operators.
-/
def smul
    (a : ℝ)
    (V : TangentAt Z) : TangentAt Z where
  op := a • V.op
  phase_linear := PhaseLinear.smul a V.phase_linear

instance (Z : BilingualUpperHalfPlane D) : SMul ℝ (TangentAt Z) where
  smul := smul

@[simp]
theorem smul_op
    (a : ℝ)
    (V : TangentAt Z) :
    (a • V).op = a • V.op :=
  rfl

end TangentAt

/-! ## Mobius tangent pushforward -/

/--
The derivative of the operator Mobius action

`Z ↦ (A Z + B) (C Z + D)⁻¹`

applied to a tangent operator `V`.

In noncommutative operator notation:

`dM_Z(V) = (A - M(Z) C) V (C Z + D)⁻¹`.

This is the correct local object for metric invariance.
-/
def moebiusTangentPushForward
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z)
    (hPos : KHalfPlanePositive D (moebiusActionOperator M Z hInv))
    (V : TangentAt Z) :
    TangentAt (moebiusAction M Z hInv hPos) where
  op :=
    ((M.A - (moebiusActionOperator M Z hInv).comp M.C).comp V.op).comp hInv.inv
  phase_linear := by
    apply PhaseLinear.comp
    · apply PhaseLinear.comp
      · apply PhaseLinear.sub
        · exact M.A_phase
        · exact PhaseLinear.comp
            (moebiusActionOperator_phaseLinear M Z hInv)
            M.C_phase
      · exact V.phase_linear
    · exact hInv.inv_phase_linear

@[simp]
theorem moebiusTangentPushForward_op
    (M : PhaseLinearMobiusCoefficients D)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z)
    (hPos : KHalfPlanePositive D (moebiusActionOperator M Z hInv))
    (V : TangentAt Z) :
    (moebiusTangentPushForward M Z hInv hPos V).op =
      ((M.A - (moebiusActionOperator M Z hInv).comp M.C).comp V.op).comp
        hInv.inv :=
  rfl

/-! ## Admissible Mobius/isometry blocks -/

/--
Placeholder predicate for the Mobius blocks that are genuine Poincare
isometries.

A future concrete version should encode the appropriate real Krein/symplectic
conditions on the block matrix

`[[A, B], [C, D]]`.

Phase-linearity and denominator invertibility alone are not enough to guarantee
metric invariance.
-/
def IsPoincareMobiusBlock
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (M : PhaseLinearMobiusCoefficients D) : Prop :=
  PhaseLinear D M.A ∧
    PhaseLinear D M.B ∧
      PhaseLinear D M.C ∧
        PhaseLinear D M.Dop

/-- Every phase-linear Mobius coefficient packet satisfies the admissible block carrier. -/
theorem isPoincareMobiusBlock_of_phaseLinear
    (M : PhaseLinearMobiusCoefficients D) :
    IsPoincareMobiusBlock D M := by
  exact ⟨M.A_phase, M.B_phase, M.C_phase, M.D_phase⟩

/-! ## Poincare metric datum -/

/--
An invariant Poincare metric datum on the bilingual upper half-plane.

The construction is property-based.  A later file can instantiate `innerAt`
using the operator height, inverse height operator, and trace/Hilbert-Schmidt
or renormalized-trace pairing.
-/
structure PoincareMetricDatum
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) where
  /-- Metric pairing at a point. -/
  innerAt :
    (Z : BilingualUpperHalfPlane D) →
      TangentAt Z → TangentAt Z → ℝ

  /-- Symmetry. -/
  symmetric :
    ∀ (Z : BilingualUpperHalfPlane D) (V W : TangentAt Z),
      innerAt Z V W = innerAt Z W V

  /-- Left additivity. -/
  add_left :
    ∀ (Z : BilingualUpperHalfPlane D) (U V W : TangentAt Z),
      innerAt Z (U + V) W =
        innerAt Z U W + innerAt Z V W

  /-- Left scalar compatibility. -/
  smul_left :
    ∀ (Z : BilingualUpperHalfPlane D) (a : ℝ) (V W : TangentAt Z),
      innerAt Z (a • V) W =
        a * innerAt Z V W

  /-- Nonnegativity. -/
  positive :
    ∀ (Z : BilingualUpperHalfPlane D) (V : TangentAt Z),
      0 ≤ innerAt Z V V

  /-- Definiteness at the operator level. -/
  definite :
    ∀ (Z : BilingualUpperHalfPlane D) (V : TangentAt Z),
      innerAt Z V V = 0 → V.op = 0

  /--
  Mobius invariance under the differential of admissible operator
  fractional-linear transformations.
  -/
  moebius_invariant :
    ∀ (M : PhaseLinearMobiusCoefficients D),
      IsPoincareMobiusBlock D M →
      ∀ (Z : BilingualUpperHalfPlane D)
      (hInv : MobiusDenominatorInverse M Z)
      (hPos : KHalfPlanePositive D (moebiusActionOperator M Z hInv))
      (V W : TangentAt Z),
      innerAt
          (moebiusAction M Z hInv hPos)
          (moebiusTangentPushForward M Z hInv hPos V)
          (moebiusTangentPushForward M Z hInv hPos W)
        =
      innerAt Z V W

namespace PoincareMetricDatum

variable
    (G : PoincareMetricDatum D)
    {Z : BilingualUpperHalfPlane D}

/--
Right additivity follows from symmetry and left additivity.
-/
theorem add_right
    (U V W : TangentAt Z) :
    G.innerAt Z U (V + W) =
      G.innerAt Z U V + G.innerAt Z U W := by
  calc
    G.innerAt Z U (V + W)
        = G.innerAt Z (V + W) U := G.symmetric Z U (V + W)
    _ = G.innerAt Z V U + G.innerAt Z W U := G.add_left Z V W U
    _ = G.innerAt Z U V + G.innerAt Z U W := by
      rw [G.symmetric Z V U, G.symmetric Z W U]

/--
Right scalar compatibility follows from symmetry and left scalar compatibility.
-/
theorem smul_right
    (a : ℝ)
    (V W : TangentAt Z) :
    G.innerAt Z V (a • W) =
      a * G.innerAt Z V W := by
  calc
    G.innerAt Z V (a • W)
        = G.innerAt Z (a • W) V := G.symmetric Z V (a • W)
    _ = a * G.innerAt Z W V := G.smul_left Z a W V
    _ = a * G.innerAt Z V W := by
      rw [G.symmetric Z W V]

/--
Named re-export of Mobius invariance for admissible Mobius blocks.
-/
theorem metric_mobius_invariant
    (M : PhaseLinearMobiusCoefficients D)
    (hM : IsPoincareMobiusBlock D M)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z)
    (hPos : KHalfPlanePositive D (moebiusActionOperator M Z hInv))
    (V W : TangentAt Z) :
    G.innerAt
        (moebiusAction M Z hInv hPos)
        (moebiusTangentPushForward M Z hInv hPos V)
        (moebiusTangentPushForward M Z hInv hPos W)
      =
    G.innerAt Z V W :=
  G.moebius_invariant M hM Z hInv hPos V W

/--
Metric invariance under an admissible operator Mobius transformation.

This is the canonical isometry-facing alias used by downstream modular and
automorphic layers.
-/
theorem moebius_isometry
    (M : PhaseLinearMobiusCoefficients D)
    (hM : IsPoincareMobiusBlock D M)
    (Z : BilingualUpperHalfPlane D)
    (hInv : MobiusDenominatorInverse M Z)
    (hPos : KHalfPlanePositive D (moebiusActionOperator M Z hInv))
    (V W : TangentAt Z) :
    G.innerAt
        (moebiusAction M Z hInv hPos)
        (moebiusTangentPushForward M Z hInv hPos V)
        (moebiusTangentPushForward M Z hInv hPos W)
      =
    G.innerAt Z V W :=
  G.metric_mobius_invariant M hM Z hInv hPos V W

end PoincareMetricDatum

/-! ## Secondary commutator readout -/

/--
Operator commutator.

This is not the primitive local Poincare metric. It is retained as a secondary
noncommutative invariant.
-/
def operatorCommutator
    (S T : EndH) : EndH :=
  S.comp T - T.comp S

omit [CompleteSpace E] in
@[simp]
theorem operatorCommutator_self
    (T : EndH) :
    operatorCommutator T T = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [operatorCommutator]

/--
The commutator of phase-linear endomorphisms is phase-linear.
-/
theorem operatorCommutator_phaseLinear
    {S T : EndH}
    (hS : PhaseLinear D S)
    (hT : PhaseLinear D T) :
    PhaseLinear D (operatorCommutator S T) := by
  dsimp [operatorCommutator]
  exact
    PhaseLinear.sub
      (PhaseLinear.comp hS hT)
      (PhaseLinear.comp hT hS)

/--
The commutator invariant of two operatorial upper-half-plane points.

This is kept as a genuinely noncommutative invariant. It vanishes on the scalar
upper-half-plane shadow, so it is not the primary Poincare metric.
-/
def commutator
    (Z W : BilingualUpperHalfPlane D) : EndH :=
  operatorCommutator Z.tau W.tau

@[simp]
theorem commutator_self
    (Z : BilingualUpperHalfPlane D) :
    commutator Z Z = 0 := by
  simp [commutator, operatorCommutator_self]

/--
The algebraic core of the operatorial Poincare metric.

Schematic classical analogue:

`g_Z(ξ,η) = Tr(Y_Z⁻¹ ξ Y_Z⁻¹ η)`.

Depending on the eventual Hilbert/Krein convention, an adjoint or symmetrized
variant may replace this exact expression. The point is that the metric is
built from the inverse imaginary operator, not from coordinates.
-/
def poincareMetricCore
    (Z : BilingualUpperHalfPlane D)
    (Y : ImaginaryRiesz Z)
    (Tr : TraceDatum (E := E))
    (ξ η : TangentAt Z) : ℝ :=
  let Yinv : EndH := (Y.unit⁻¹).val
  Tr.tr ((Yinv.comp ξ.op).comp (Yinv.comp η.op))

end BilingualUpperHalfPlane

namespace BilingualPoincareMetric

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit

/-! ## Abstract positive-interior metric interface -/

/-! ### Krein quadratic geometry -/

/--
A homogeneous Krein quadratic readout on a real carrier.

Morally this is `q(v) = ⟪v, η v⟫`.
-/
abbrev KreinQuadraticDatum
    (H : Type*) [AddCommGroup H] [Module ℝ H] :=
  InfoGeometry.Geometry.KreinIsotropicCone.KreinQuadraticDatum H

/--
The isotropic/null cone.

This is the projective boundary/absolute, not the metric interior.
-/
abbrev IsotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  InfoGeometry.Geometry.KreinIsotropicCone.IsotropicCone Q

/--
The strict isotropic cone excludes the zero vector.
-/
abbrev StrictIsotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  InfoGeometry.Geometry.KreinIsotropicCone.StrictIsotropicCone Q

/--
The positive Krein cone.

This is one possible interior domain for hyperbolic/Poincare geometry.
-/
abbrev PositiveKreinCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  InfoGeometry.Geometry.KreinIsotropicCone.PositiveKreinCone Q

/--
The negative Krein cone.
-/
abbrev NegativeKreinCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  InfoGeometry.Geometry.KreinIsotropicCone.NegativeKreinCone Q

/--
The isotropic cone is stable under scalar multiplication.
-/
theorem smul_mem_isotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H)
    {v : H}
    (hv : v ∈ IsotropicCone Q)
    (a : ℝ) :
    a • v ∈ IsotropicCone Q := by
  change Q.q (a • v) = 0
  change Q.q v = 0 at hv
  rw [Q.q_smul, hv, mul_zero]

/--
Projective ray equivalence.

This is the scale/Weyl quotient relation on nonzero states.
-/
def SameProjectiveRay
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (v w : H) : Prop :=
  ∃ lam : ℝ, lam ≠ 0 ∧ w = lam • v

/-! ### Bilingual upper-half-plane points -/

/--
A bilingual upper-half-plane point is a point in the positive Krein cone.

The isotropic cone `q = 0` is its boundary.
-/
structure BilingualUpperHalfPlanePoint
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) where
  /-- Underlying carrier point/state. -/
  val : H

  /-- The point lies in the positive interior. -/
  positive :
    val ∈ PositiveKreinCone Q

namespace BilingualUpperHalfPlanePoint

variable
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {Q : KreinQuadraticDatum H}

/--
Positive height/readout of a bilingual upper-half-plane point.
-/
def height
    (Z : BilingualUpperHalfPlanePoint H Q) : ℝ :=
  Q.q Z.val

/--
The height is positive.
-/
theorem height_pos
    (Z : BilingualUpperHalfPlanePoint H Q) :
    0 < Z.height := by
  simpa [height, PositiveKreinCone] using Z.positive

end BilingualUpperHalfPlanePoint

/-! ### Tangent data -/

/--
A tangent vector at a bilingual upper-half-plane point.

At this structural layer the tangent is just a carrier vector. Later files may
restrict it by phase-linearity, horizontality, gauge-fixing, or projective
slice conditions.
-/
structure TangentAt
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {Q : KreinQuadraticDatum H}
    (_Z : BilingualUpperHalfPlanePoint H Q) where
  /-- Tangent velocity. -/
  vel : H

namespace TangentAt

variable
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {Q : KreinQuadraticDatum H}
    {Z : BilingualUpperHalfPlanePoint H Q}

instance : Zero (TangentAt Z) where
  zero := ⟨0⟩

instance : Add (TangentAt Z) where
  add U V := ⟨U.vel + V.vel⟩

instance : Neg (TangentAt Z) where
  neg U := ⟨-U.vel⟩

instance : Sub (TangentAt Z) where
  sub U V := ⟨U.vel - V.vel⟩

instance : SMul ℝ (TangentAt Z) where
  smul a U := ⟨a • U.vel⟩

@[simp]
theorem zero_vel :
    (0 : TangentAt Z).vel = 0 :=
  rfl

@[simp]
theorem add_vel
    (U V : TangentAt Z) :
    (U + V).vel = U.vel + V.vel :=
  rfl

@[simp]
theorem neg_vel
    (U : TangentAt Z) :
    (-U).vel = -U.vel :=
  rfl

@[simp]
theorem sub_vel
    (U V : TangentAt Z) :
    (U - V).vel = U.vel - V.vel :=
  rfl

@[simp]
theorem smul_vel
    (a : ℝ)
    (U : TangentAt Z) :
    (a • U).vel = a • U.vel :=
  rfl

end TangentAt

/-! ### Poincare metric datum -/

/--
A structural Poincare metric datum on the bilingual upper-half-plane interior.

This is not yet a formula. A later spectral/cyclic module can instantiate
`innerAt` using commutators, traces, weights, residues, or cyclic cocycles.
-/
structure PoincareMetricDatum
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) where
  /-- Metric pairing on tangent vectors at an interior point. -/
  innerAt :
    (Z : BilingualUpperHalfPlanePoint H Q) →
      TangentAt Z → TangentAt Z → ℝ

  /-- Symmetry. -/
  symmetric :
    ∀ (Z : BilingualUpperHalfPlanePoint H Q)
      (U V : TangentAt Z),
        innerAt Z U V = innerAt Z V U

  /-- Left additivity. -/
  add_left :
    ∀ (Z : BilingualUpperHalfPlanePoint H Q)
      (U V W : TangentAt Z),
        innerAt Z (U + V) W =
          innerAt Z U W + innerAt Z V W

  /-- Left scalar compatibility. -/
  smul_left :
    ∀ (Z : BilingualUpperHalfPlanePoint H Q)
      (a : ℝ)
      (U V : TangentAt Z),
        innerAt Z (a • U) V =
          a * innerAt Z U V

  /-- Nonnegativity. -/
  nonnegative :
    ∀ (Z : BilingualUpperHalfPlanePoint H Q)
      (U : TangentAt Z),
        0 ≤ innerAt Z U U

  /-- Definiteness. -/
  definite :
    ∀ (Z : BilingualUpperHalfPlanePoint H Q)
      (U : TangentAt Z),
        innerAt Z U U = 0 → U.vel = 0

namespace PoincareMetricDatum

variable
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {Q : KreinQuadraticDatum H}

variable (G : PoincareMetricDatum H Q)

variable {Z : BilingualUpperHalfPlanePoint H Q}

/--
Right additivity follows from symmetry and left additivity.
-/
theorem add_right
    (U V W : TangentAt Z) :
    G.innerAt Z U (V + W) =
      G.innerAt Z U V + G.innerAt Z U W := by
  calc
    G.innerAt Z U (V + W)
        = G.innerAt Z (V + W) U := G.symmetric Z U (V + W)
    _ = G.innerAt Z V U + G.innerAt Z W U := G.add_left Z V W U
    _ = G.innerAt Z U V + G.innerAt Z U W := by
      rw [G.symmetric Z V U, G.symmetric Z W U]

/--
Right scalar compatibility follows from symmetry and left scalar compatibility.
-/
theorem smul_right
    (a : ℝ)
    (U V : TangentAt Z) :
    G.innerAt Z U (a • V) =
      a * G.innerAt Z U V := by
  calc
    G.innerAt Z U (a • V)
        = G.innerAt Z (a • V) U := G.symmetric Z U (a • V)
    _ = a * G.innerAt Z V U := G.smul_left Z a V U
    _ = a * G.innerAt Z U V := by
      rw [G.symmetric Z V U]

/--
Squared norm of a tangent vector.
-/
def normSq
    (Z : BilingualUpperHalfPlanePoint H Q)
    (U : TangentAt Z) : ℝ :=
  G.innerAt Z U U

/--
The squared norm is nonnegative.
-/
theorem normSq_nonnegative
    (Z : BilingualUpperHalfPlanePoint H Q)
    (U : TangentAt Z) :
    0 ≤ G.normSq Z U :=
  G.nonnegative Z U

/--
Zero squared norm implies zero velocity.
-/
theorem normSq_eq_zero_implies_vel_zero
    (Z : BilingualUpperHalfPlanePoint H Q)
    (U : TangentAt Z)
    (hU : G.normSq Z U = 0) :
    U.vel = 0 :=
  G.definite Z U hU

end PoincareMetricDatum

/-! ### Automorphisms and isometry covariance -/

/--
An automorphism of the bilingual upper-half-plane interior.

The map must preserve the positive domain. Its tangent pushforward is supplied
explicitly because this file does not build a differentiable-manifold API.
-/
structure BilingualAutomorphism
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) where
  /-- Map on interior points. -/
  map :
    BilingualUpperHalfPlanePoint H Q →
      BilingualUpperHalfPlanePoint H Q

  /-- Tangent pushforward. -/
  pushTangent :
    ∀ Z : BilingualUpperHalfPlanePoint H Q,
      TangentAt Z → TangentAt (map Z)

/--
A bilingual automorphism is an isometry of the Poincare metric.
-/
def IsPoincareIsometry
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {Q : KreinQuadraticDatum H}
    (G : PoincareMetricDatum H Q)
    (φ : BilingualAutomorphism H Q) : Prop :=
  ∀ (Z : BilingualUpperHalfPlanePoint H Q)
    (U V : TangentAt Z),
      G.innerAt (φ.map Z) (φ.pushTangent Z U) (φ.pushTangent Z V) =
        G.innerAt Z U V

/--
Admissible Mobius/Erlanger symmetry class.

This is intentionally abstract. Later files should instantiate it using
phase-preserving, Krein-metric-preserving, positivity-preserving operator
Mobius transformations.
-/
structure BilingualMobiusSymmetry
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) where
  aut :
    BilingualAutomorphism H Q

/--
Metric covariance under an admissible Mobius/Erlanger symmetry.
-/
def MobiusIsometryLaw
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {Q : KreinQuadraticDatum H}
    (G : PoincareMetricDatum H Q)
    (M : BilingualMobiusSymmetry H Q) : Prop :=
  IsPoincareIsometry G M.aut

/-! ### Spectral reconstruction socket -/

/--
A spectral or cyclic reconstruction backend for the Poincare metric.

This is the bridge to a later `SpectralCyclicPairing.lean` module. It states
that the metric pairing is recovered from an operator/spectral readout, without
asserting a concrete Connes-distance theorem here.
-/
structure PoincareMetricSpectralBackend
    (H Op : Type*)
    [AddCommGroup H] [Module ℝ H]
    [Ring Op]
    (Q : KreinQuadraticDatum H)
    (G : PoincareMetricDatum H Q) where
  /-- Representation of carrier/tangent data into operators. -/
  tangentOperator :
    ∀ Z : BilingualUpperHalfPlanePoint H Q,
      TangentAt Z → Op

  /-- Pairing/readout on operators. -/
  spectralPairing :
    Op → Op → ℝ

  /-- The metric is recovered from the spectral pairing. -/
  metric_eq_spectralPairing :
    ∀ (Z : BilingualUpperHalfPlanePoint H Q)
      (U V : TangentAt Z),
        G.innerAt Z U V =
          spectralPairing (tangentOperator Z U) (tangentOperator Z V)

end BilingualPoincareMetric

end InfoGeometry.Geometry
