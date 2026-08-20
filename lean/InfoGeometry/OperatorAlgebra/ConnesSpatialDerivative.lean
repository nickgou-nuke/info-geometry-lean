/-
InfoGeometry/OperatorAlgebra/ConnesSpatialDerivative.lean

Connes spatial derivative and unnormalized modular comparison.

This module replaces normalized-state geometry and trace-based shortcuts with
weight comparison data.

The abstract Type III layer records only explicit algebraic cocycle / spatial
derivative laws. Analytic normality, support, and affiliated-operator
regularity are not encoded here.

The scalar positive-cone branch is fully constructive and proves:

  dφ/dω = mφ / mω
  (dφ/dω)(dω/dη) = dφ/dη
  dφ/dφ = 1
  log(dφ/dφ) = 0
  scalar BKM metric X²/m ≥ 0

No trace normalization is used.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import Mathlib.Data.ENNReal.Basic

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative

set_option linter.dupNamespace false

/-! ## 1. Unnormalized weights -/

/--
A weight-like object.

There is deliberately no normalization field.
-/
structure OperatorWeight
    (A : Type*) where
  /-- Positive cone/domain. -/
  positiveCone : Set A

  /-- Extended nonnegative weight readout. -/
  weight : A → ℝ≥0∞

namespace OperatorWeight

variable {A : Type*}
variable (φ : OperatorWeight A)

/--
Mass of a chosen unit-like element.

This is not required to be `1`.
-/
def mass
    (unitLike : A) : ℝ≥0∞ :=
  φ.weight unitLike

end OperatorWeight

/-! ## 2. Modular flow data -/

/--
Algebraic modular flow.

Analytic continuity, normality, and KMS-strip data belong to later concrete
modules.
-/
abbrev ModularFlow
    (A : Type*) [Monoid A] :=
  InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow A

namespace ModularFlow

variable {A : Type*} [Monoid A]
variable (σ : ModularFlow A)

@[simp]
theorem flow_zero_apply
    (x : A) :
    σ.flow 0 x = x :=
  σ.flow_zero x

@[simp]
theorem flow_one_apply
    (t : ℝ) :
    σ.flow t 1 = 1 :=
  (σ.flow t).map_one

theorem flow_mul_apply
    (t : ℝ)
    (x y : A) :
    σ.flow t (x * y) = σ.flow t x * σ.flow t y :=
  (σ.flow t).map_mul x y

theorem flow_one
    (t : ℝ) :
    σ.flow t 1 = 1 :=
  flow_one_apply σ t

theorem flow_mul
    (t : ℝ)
    (x y : A) :
    σ.flow t (x * y) = σ.flow t x * σ.flow t y :=
  flow_mul_apply σ t x y

theorem flow_commute
    (s t : ℝ) (x : A) :
    σ.flow s (σ.flow t x) = σ.flow t (σ.flow s x) := by
  exact InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow.flow_commute σ s t x

theorem flow_neg_apply'
    (t : ℝ) (x : A) :
    σ.flow t (σ.flow (-t) x) = x := by
  exact InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow.flow_neg_apply' σ t x

end ModularFlow

/-! ## 3. Connes cocycle derivative data -/

/--
Connes cocycle derivative datum.

The intended object is `[Dφ : Dψ]_t`.

The key laws are carried explicitly because their analytic proof depends on
the von Neumann algebra representation and weight hypotheses.
-/
structure ConnesCocycleDerivative
    (A Weight : Type*) [Ring A] where
  /-- Modular flow associated to a weight. -/
  modularFlow : Weight → ModularFlow A

  /-- Connes cocycle derivative `[Dφ : Dψ]_t`. -/
  cocycle : Weight → Weight → ℝ → A

  /-- Same-weight cocycle is trivial. -/
  same_weight :
    ∀ φ t, cocycle φ φ t = 1

  /-- Chain rule between weights. -/
  chain_rule :
    ∀ φ ψ η t,
      cocycle φ ψ t * cocycle ψ η t = cocycle φ η t


namespace ConnesCocycleDerivative

variable {A Weight : Type*} [Ring A]
variable (C : ConnesCocycleDerivative A Weight)

/--
The same-weight cocycle is trivial.
-/
theorem same_weight_apply
    (φ : Weight)
    (t : ℝ) :
    C.cocycle φ φ t = 1 :=
  C.same_weight φ t

/--
The Connes cocycle satisfies the supplied chain rule.
-/
theorem chain_rule_apply
    (φ ψ η : Weight)
    (t : ℝ) :
    C.cocycle φ ψ t * C.cocycle ψ η t =
      C.cocycle φ η t :=
  C.chain_rule φ ψ η t

end ConnesCocycleDerivative

/-! ## 4. Spatial derivative data -/

/--
Connes spatial derivative datum.

The intended object is `dφ/dψ`, represented in some affiliated/positive
operator carrier `Deriv`.

This is the correct primitive for comparing unnormalized weights.
-/
structure ConnesSpatialDerivative
    (Weight Deriv : Type*) [One Deriv] [Mul Deriv] where
  /-- Spatial derivative `dφ/dψ`. -/
  spatialDerivative : Weight → Weight → Deriv

  /-- Same-weight derivative is identity. -/
  same_weight :
    ∀ φ, spatialDerivative φ φ = 1

  /-- Chain rule. -/
  chain_rule :
    ∀ φ ψ η,
      spatialDerivative φ ψ * spatialDerivative ψ η =
        spatialDerivative φ η


namespace ConnesSpatialDerivative

variable {Weight Deriv : Type*} [One Deriv] [Mul Deriv]
variable (D : ConnesSpatialDerivative Weight Deriv)

/--
Same-weight spatial derivative is identity.
-/
theorem same_weight_apply
    (φ : Weight) :
    D.spatialDerivative φ φ = 1 :=
  D.same_weight φ

/--
Spatial derivative chain rule.
-/
theorem chain_rule_apply
    (φ ψ η : Weight) :
    D.spatialDerivative φ ψ * D.spatialDerivative ψ η =
      D.spatialDerivative φ η :=
  D.chain_rule φ ψ η

end ConnesSpatialDerivative

/-! ## 5. Symmetric Hamiltonian is derived, not primitive -/

/--
Symmetric relative modular Hamiltonian calibration.

This is a derived response readout from spatial derivative data.  It is not the
foundational primitive.
-/
structure SymmetricRelativeHamiltonianCalibration
    (Weight Deriv SymHam : Type*)
    [One Deriv] [Mul Deriv] where
  spatial :
    ConnesSpatialDerivative Weight Deriv

  /-- Symmetric Hamiltonian / logarithmic response readout. -/
  symHamiltonian :
    Weight → Weight → SymHam

/-! ## 6. Abstract BKM data from spatial derivative -/

/--
BKM metric datum on the unnormalized positive cone.

Positivity is not proved from an arbitrary `metric` field; it is an explicit
law of this datum and is supplied by each concrete modular model.

The scalar constructive branch below proves the first model explicitly.
-/
structure BKMMetricDatum
    (Weight Tangent : Type*) [AddCommGroup Tangent] [Module ℝ Tangent] where
  metric : Weight → Tangent → Tangent → ℝ

  symmetric :
    ∀ φ X Y, metric φ X Y = metric φ Y X

  nonnegative :
    ∀ φ X, 0 ≤ metric φ X X

namespace BKMMetricDatum

variable {Weight Tangent : Type*} [AddCommGroup Tangent] [Module ℝ Tangent]
variable (B : BKMMetricDatum Weight Tangent)

theorem nonnegative_apply
    (φ : Weight)
    (X : Tangent) :
    0 ≤ B.metric φ X X :=
  B.nonnegative φ X

theorem symmetric_apply
    (φ : Weight)
    (X Y : Tangent) :
    B.metric φ X Y = B.metric φ Y X :=
  B.symmetric φ X Y

end BKMMetricDatum

/-! ## 7. Fully constructive scalar positive-cone model -/

/--
Positive scalar weight.

This is the one-dimensional unnormalized cone model.
-/
abbrev PositiveScalarWeight := {mass : ℝ // 0 < mass}

namespace PositiveScalarWeight

abbrev mass (φ : PositiveScalarWeight) : ℝ := φ.1

abbrev mass_pos (φ : PositiveScalarWeight) : 0 < φ.mass := φ.2

/--
Connes spatial derivative in the positive scalar cone:

`dφ/dψ = mφ / mψ`.
-/
def spatialDerivative
    (φ ψ : PositiveScalarWeight) : ℝ :=
  φ.mass / ψ.mass

/--
The scalar spatial derivative is positive.
-/
theorem spatialDerivative_pos
    (φ ψ : PositiveScalarWeight) :
    0 < spatialDerivative φ ψ := by
  dsimp [spatialDerivative]
  exact div_pos φ.mass_pos ψ.mass_pos

/--
Same-weight derivative is `1`.
-/
theorem spatialDerivative_self
    (φ : PositiveScalarWeight) :
    spatialDerivative φ φ = 1 := by
  dsimp [spatialDerivative]
  exact div_self (ne_of_gt φ.mass_pos)

/--
Chain rule:

`(dφ/dψ)(dψ/dη)=dφ/dη`.
-/
theorem spatialDerivative_chain
    (φ ψ η : PositiveScalarWeight) :
    spatialDerivative φ ψ * spatialDerivative ψ η =
      spatialDerivative φ η := by
  dsimp [spatialDerivative]
  field_simp [
    ne_of_gt φ.mass_pos,
    ne_of_gt ψ.mass_pos,
    ne_of_gt η.mass_pos
  ]

/--
Inverse law:

`(dφ/dψ)(dψ/dφ)=1`.
-/
theorem spatialDerivative_inverse
    (φ ψ : PositiveScalarWeight) :
    spatialDerivative φ ψ * spatialDerivative ψ φ = 1 := by
  rw [spatialDerivative_chain φ ψ φ]
  exact spatialDerivative_self φ

/--
Logarithmic spatial derivative.
-/
def logSpatialDerivative
    (φ ψ : PositiveScalarWeight) : ℝ :=
  Real.log (spatialDerivative φ ψ)

/--
Same-weight log derivative vanishes.
-/
theorem logSpatialDerivative_self
    (φ : PositiveScalarWeight) :
    logSpatialDerivative φ φ = 0 := by
  dsimp [logSpatialDerivative]
  rw [spatialDerivative_self]
  exact Real.log_one

/--
Scalar BKM metric on the unnormalized positive ray.

For tangent values `X,Y`, the metric at mass `m` is:

`g_m(X,Y)=XY/m`.
-/
def scalarBKMMetric
    (φ : PositiveScalarWeight)
    (X Y : ℝ) : ℝ :=
  (X * Y) / φ.mass

/--
Scalar BKM metric is symmetric.
-/
theorem scalarBKMMetric_symmetric
    (φ : PositiveScalarWeight)
    (X Y : ℝ) :
    scalarBKMMetric φ X Y =
      scalarBKMMetric φ Y X := by
  dsimp [scalarBKMMetric]
  rw [mul_comm X Y]

/--
Scalar BKM metric is nonnegative on the diagonal.
-/
theorem scalarBKMMetric_nonnegative
    (φ : PositiveScalarWeight)
    (X : ℝ) :
    0 ≤ scalarBKMMetric φ X X := by
  dsimp [scalarBKMMetric]
  exact div_nonneg (mul_self_nonneg X) (le_of_lt φ.mass_pos)

/--
Scalar BKM metric datum, fully constructive.
-/
def scalarBKMMetricDatum :
    BKMMetricDatum PositiveScalarWeight ℝ where
  metric := scalarBKMMetric
  symmetric := scalarBKMMetric_symmetric
  nonnegative := scalarBKMMetric_nonnegative

/--
Scalar spatial derivative as a constructive `ConnesSpatialDerivative` datum.
-/
def scalarSpatialDerivativeDatum :
    ConnesSpatialDerivative PositiveScalarWeight ℝ where
  spatialDerivative := spatialDerivative
  same_weight := spatialDerivative_self
  chain_rule := spatialDerivative_chain

end PositiveScalarWeight

end InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
