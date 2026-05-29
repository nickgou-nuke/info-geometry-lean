import InfoGeometry.Canonical.GeneratedFlow

namespace InfoGeometry.Canonical

/-!
# Weyl Gauge Field

Canonical Weyl-gauge extension of the relative-geometry spine.

This file introduces an explicit local scale-connection object

`WeylGaugeField`

together with:

- local gauge parameters,
- local gauge transformations,
- canonical lift/readout maps into the existing
  `LogGenerator -> GeneratedFlow -> GeometricResponse` pipeline.
-/

/-- Abstract local Weyl gauge boson/connection field. -/
structure WeylGaugeField (X A : Type*) where
  gaugeOf : X → A

/-- Local Weyl gauge parameter (additive shift data). -/
structure WeylGaugeParameter (X A : Type*) where
  shiftOf : X → A

/-- Weyl field-strength/curvature object induced by a gauge field. -/
structure WeylFieldStrength (X A : Type*) where
  strengthOf : X → A

/--
Abstract first-order differential interface for local Weyl data.

This is the minimal operator-level API needed for:
- covariant derivative construction,
- gauge compensation law,
- curvature/field-strength invariance under exact shifts.
-/
structure WeylDifferentialOperator (K X A : Type*) [Ring K] [AddCommGroup A] [Module K A] where
  diff : (X → A) → X → A
  map_add : ∀ f g x, diff (fun y => f y + g y) x = diff f x + diff g x
  map_smul : ∀ (k : K) f x, diff (fun y => k • f y) x = k • diff f x
  nilpotent : ∀ f x, diff (fun y => diff f y) x = 0

attribute [spine_object] WeylGaugeField WeylGaugeParameter WeylFieldStrength

namespace WeylDifferentialOperator

variable {K X A : Type*} [Ring K] [AddCommGroup A] [Module K A]

/-- Pointwise additive linearity of the Weyl differential operator. -/
@[simp] theorem map_add_apply (Δ : WeylDifferentialOperator K X A)
    (f g : X → A) (x : X) :
    Δ.diff (fun y => f y + g y) x = Δ.diff f x + Δ.diff g x :=
  Δ.map_add f g x

/-- Pointwise module-linearity of the Weyl differential operator. -/
@[simp] theorem map_smul_apply (Δ : WeylDifferentialOperator K X A)
    (k : K) (f : X → A) (x : X) :
    Δ.diff (fun y => k • f y) x = k • Δ.diff f x :=
  Δ.map_smul k f x

/-- Pointwise differential nilpotency (`d ∘ d = 0`). -/
@[simp] theorem nilpotent_apply (Δ : WeylDifferentialOperator K X A)
    (f : X → A) (x : X) :
    Δ.diff (fun y => Δ.diff f y) x = 0 :=
  Δ.nilpotent f x

/-- Differential of pointwise negation. -/
@[simp] theorem map_neg (Δ : WeylDifferentialOperator K X A)
    (f : X → A) (x : X) :
    Δ.diff (fun y => -f y) x = -Δ.diff f x := by
  simpa using Δ.map_smul (-1 : K) f x

/-- Differential of pointwise subtraction. -/
@[simp] theorem map_sub (Δ : WeylDifferentialOperator K X A)
    (f g : X → A) (x : X) :
    Δ.diff (fun y => f y - g y) x = Δ.diff f x - Δ.diff g x := by
  simp [sub_eq_add_neg, Δ.map_add, Δ.map_neg]

/-- Differential of the zero field. -/
@[simp] theorem map_zero (Δ : WeylDifferentialOperator K X A) (x : X) :
    Δ.diff (fun _ => (0 : A)) x = 0 := by
  simpa using Δ.map_smul (0 : K) (fun _ => (0 : A)) x

end WeylDifferentialOperator

namespace WeylGaugeField

variable {W X A R : Type*}

/-- Pull a Weyl gauge field along a logarithmic generator. -/
def along (B : WeylGaugeField X A) (L : LogGenerator W X) : W → A :=
  fun w => B.gaugeOf (L.logGen w)

/-- Pointwise expansion of `WeylGaugeField.along`. -/
@[simp] theorem along_apply (B : WeylGaugeField X A) (L : LogGenerator W X) (w : W) :
    B.along L w = B.gaugeOf (L.logGen w) := by
  rfl

/-- Read a geometric response through a Weyl gauge field. -/
def respond (B : WeylGaugeField X A) (resp : GeometricResponse A R) (L : LogGenerator W X) :
    W → R :=
  fun w => resp.responseOf (B.gaugeOf (L.logGen w))

/-- Pointwise expansion of `WeylGaugeField.respond`. -/
@[simp] theorem respond_apply
    (B : WeylGaugeField X A) (resp : GeometricResponse A R) (L : LogGenerator W X) (w : W) :
    B.respond resp L w = resp.responseOf (B.gaugeOf (L.logGen w)) := by
  rfl

section GaugeTransform

variable [AddMonoid A]

/-- Local Weyl gauge transformation: additive shift of the gauge field. -/
def transform (B : WeylGaugeField X A) (σ : WeylGaugeParameter X A) : WeylGaugeField X A where
  gaugeOf x := B.gaugeOf x + σ.shiftOf x

/-- Pointwise expansion of `transform`. -/
@[simp] theorem transform_apply
    (B : WeylGaugeField X A) (σ : WeylGaugeParameter X A) (x : X) :
    (B.transform σ).gaugeOf x = B.gaugeOf x + σ.shiftOf x := by
  rfl

/-- Identity gauge transform (`σ = 0`) leaves the field unchanged. -/
@[simp] theorem transform_zero (B : WeylGaugeField X A) :
    B.transform ⟨fun _ => 0⟩ = B := by
  cases B
  simp [transform]

/-- Successive gauge transforms compose by pointwise addition of shifts. -/
theorem transform_comp
    (B : WeylGaugeField X A)
    (σ₁ σ₂ : WeylGaugeParameter X A) :
    (B.transform σ₁).transform σ₂ =
      B.transform ⟨fun x => σ₁.shiftOf x + σ₂.shiftOf x⟩ := by
  cases B
  cases σ₁
  cases σ₂
  simp [transform, add_assoc]

/-- A response is gauge-invariant if additive local shifts do not change readout. -/
def IsGaugeInvariant (resp : GeometricResponse A R) : Prop :=
  ∀ a δ : A, resp.responseOf (a + δ) = resp.responseOf a

/-- Gauge-invariant responses are unchanged by local Weyl gauge transformation. -/
theorem respond_transform_eq_of_isGaugeInvariant
    (B : WeylGaugeField X A)
    (σ : WeylGaugeParameter X A)
    (resp : GeometricResponse A R)
    (L : LogGenerator W X)
    (hInv : IsGaugeInvariant resp) :
    (B.transform σ).respond resp L = B.respond resp L := by
  funext w
  exact hInv (B.gaugeOf (L.logGen w)) (σ.shiftOf (L.logGen w))

end GaugeTransform

section Curvature

variable {K : Type*} [Ring K]
variable [AddCommGroup A] [Module K A]

/--
Weyl gauge transformation written in local-potential form:
`W ↦ W - dα`.
-/
def transformByPotential
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A) : WeylGaugeField X A where
  gaugeOf x := B.gaugeOf x - Δ.diff α.shiftOf x

/-- Pointwise expansion of `transformByPotential`. -/
@[simp] theorem transformByPotential_apply
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A)
    (x : X) :
    (B.transformByPotential Δ α).gaugeOf x = B.gaugeOf x - Δ.diff α.shiftOf x := by
  rfl

/-- Direct field-strength object associated to a Weyl gauge field. -/
def fieldStrength
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A) : WeylFieldStrength X A where
  strengthOf := Δ.diff B.gaugeOf

/-- Pointwise expansion of `fieldStrength`. -/
@[simp] theorem fieldStrength_apply
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (x : X) :
    (B.fieldStrength Δ).strengthOf x = Δ.diff B.gaugeOf x := by
  rfl

/--
Scale-covariant derivative of a charged section `ψ` with Weyl charge `q`:
`Dψ = dψ + q • W`.
-/
def covariantDerivative
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A) : X → A :=
  fun x => Δ.diff ψ x + q • B.gaugeOf x

/-- Pointwise expansion of `covariantDerivative`. -/
@[simp] theorem covariantDerivative_apply
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (x : X) :
    B.covariantDerivative Δ q ψ x = Δ.diff ψ x + q • B.gaugeOf x := by
  rfl

/-- Charged section transformation under local Weyl potential `α`. -/
def transformSection (q : K) (ψ : X → A) (α : WeylGaugeParameter X A) : X → A :=
  fun x => ψ x + q • α.shiftOf x

/-- Pointwise expansion of `transformSection`. -/
@[simp] theorem transformSection_apply
    (q : K)
    (ψ : X → A)
    (α : WeylGaugeParameter X A)
    (x : X) :
    transformSection q ψ α x = ψ x + q • α.shiftOf x := by
  rfl

/-- Flatness predicate: vanishing Weyl field strength at all points. -/
def IsFlat (Δ : WeylDifferentialOperator K X A) (B : WeylGaugeField X A) : Prop :=
  ∀ x : X, (B.fieldStrength Δ).strengthOf x = 0

/-- Gauge-transformed field has the same curvature (`d(W - dα) = dW`). -/
theorem fieldStrength_transformByPotential_eq
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A) :
    (B.transformByPotential Δ α).fieldStrength Δ = B.fieldStrength Δ := by
  cases B
  cases α
  apply congrArg WeylFieldStrength.mk
  funext x
  simp [transformByPotential, WeylDifferentialOperator.map_sub]

/--
Gauge-invariant responses are unchanged by local potential gauge
transformation as well.
-/
theorem respond_transformByPotential_eq_of_isGaugeInvariant
    (Δ : WeylDifferentialOperator K X A)
    (B : WeylGaugeField X A)
    (α : WeylGaugeParameter X A)
    (resp : GeometricResponse A R)
    (L : LogGenerator W X)
    (hInv : IsGaugeInvariant resp) :
    (B.transformByPotential Δ α).respond resp L = B.respond resp L := by
  funext w
  simpa [sub_eq_add_neg] using
    hInv (B.gaugeOf (L.logGen w)) (-Δ.diff α.shiftOf (L.logGen w))

/-- Covariant derivative obeys the Weyl compensation law. -/
theorem covariantDerivative_transformSection_eq
    (Δ : WeylDifferentialOperator K X A)
    (q : K)
    (B : WeylGaugeField X A)
    (ψ : X → A)
    (α : WeylGaugeParameter X A) :
    (B.transformByPotential Δ α).covariantDerivative Δ q (transformSection q ψ α) =
      B.covariantDerivative Δ q ψ := by
  funext x
  change Δ.diff (fun y => ψ y + q • α.shiftOf y) x +
      q • (B.gaugeOf x - Δ.diff α.shiftOf x) =
      Δ.diff ψ x + q • B.gaugeOf x
  rw [Δ.map_add ψ (fun y => q • α.shiftOf y) x, Δ.map_smul q α.shiftOf x, smul_sub]
  simp [sub_eq_add_neg, add_assoc, add_comm]

end Curvature

attribute [spine_functor, spine_functor_lift] WeylGaugeField.along
attribute [spine_functor, spine_functor_responder] WeylGaugeField.respond
attribute [spine_functor, spine_functor_lift] WeylGaugeField.covariantDerivative
attribute [spine_functor, spine_functor_responder] WeylGaugeField.fieldStrength

end WeylGaugeField

end InfoGeometry.Canonical
