/-
InfoGeometry/Thermo/KMSDetailedBalance.lean

KMS detailed balance as a closed bilingual/Stokes form.

This module does not construct imaginary-time integration from scratch and does
not assert a global KMS theorem from prose.  It records the finite theorem
surface that is already constructive:

* a KMS boundary datum supplies the algebraic strip-boundary identity;
* a closed geometric one-form supplies vanishing boundary integral by Stokes;
* a detailed-balance packet packages both readouts without identifying them
  unless a concrete model supplies that bridge.
-/

import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Dynamics.ModularThermalState

noncomputable section

namespace InfoGeometry.Thermo.KMSDetailedBalance

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Dynamics

/-! ## 1. Thermal strip/cylinder bookkeeping -/

/--
The KMS strip at inverse temperature `β`.

This is only the geometric bookkeeping layer: lower boundary `t`, upper
boundary `t + iβ`, and the closed horizontal strip.
-/
structure KMSRegion (β : ℝ) where
  /-- The closed strip `0 ≤ Im z ≤ β`. -/
  strip : Set ℂ
  /-- Lower real-time boundary. -/
  lowerBoundary : ℝ → ℂ
  /-- Upper imaginary-time boundary. -/
  upperBoundary : ℝ → ℂ

/-- The standard closed KMS strip model. -/
def standardKMSRegion
    (β : ℝ) :
    KMSRegion β where
  strip := {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}
  lowerBoundary := fun t => (t : ℂ)
  upperBoundary := fun t => complexClockPoint t β

@[simp]
theorem standardKMSRegion_lowerBoundary
    (β t : ℝ) :
    (standardKMSRegion β).lowerBoundary t = (t : ℂ) :=
  rfl

@[simp]
theorem standardKMSRegion_upperBoundary
    (β t : ℝ) :
    (standardKMSRegion β).upperBoundary t = complexClockPoint t β :=
  rfl

/-! ## 2. KMS boundary identities as detailed balance -/

/-- The lower KMS two-point correlation form at real time `t`. -/
def lowerKMSCorrelation
    {A : Type*} [Mul A]
    (K : KMSBoundaryData A)
    (t : ℝ)
    (a b : A) : ℝ :=
  K.omega_eval a (K.modular.sigma t b)

/-- The upper KMS two-point correlation form at shifted modular time `t + β`. -/
def upperKMSCorrelation
    {A : Type*} [Mul A]
    (K : KMSBoundaryData A)
    (t : ℝ)
    (a b : A) : ℝ :=
  K.omega_eval (K.modular.sigma (t + K.beta) b) a

/--
The KMS boundary identity is the algebraic detailed-balance identity between
the lower and upper strip correlations.
-/
theorem lowerKMSCorrelation_eq_upper
    {A : Type*} [Mul A]
    (K : KMSBoundaryData A)
    (t : ℝ)
    (a b : A) :
    lowerKMSCorrelation K t a b =
      upperKMSCorrelation K t a b := by
  exact K.kms_boundary t a b

/--
Thermal Wilson transport through one inverse-temperature period, at real
modular time `t`.

This is only the modular-flow transport readout; no path-ordered exponential is
asserted at this abstract layer.
-/
def thermalWilsonHolonomyAt
    {A : Type*} [Mul A]
    (K : KMSBoundaryData A)
    (t : ℝ) :
    A → A :=
  fun x => K.modular.sigma (t + K.beta) x

/-- KMS detailed balance expressed through the thermal Wilson transport. -/
theorem lowerKMSCorrelation_eq_wilsonHolonomy
    {A : Type*} [Mul A]
    (K : KMSBoundaryData A)
    (t : ℝ)
    (a b : A) :
    lowerKMSCorrelation K t a b =
      K.omega_eval (thermalWilsonHolonomyAt K t b) a := by
  exact K.kms_boundary t a b

/-! ## 3. Detailed balance as Stokes closure -/

/--
A KMS/detailed-balance geometric form.

The form is operator/thermal-model specific.  The only constructive theorem
claimed here is that closedness of the form forces vanishing boundary integral
through the supplied Stokes backend.
-/
structure KMSDetailedBalanceForm
    (Region Point Tangent Value : Type*)
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) where
  /-- Thermal/KMS correlation one-form. -/
  modularForm :
    OperatorOneForm Point Tangent Value
  /-- Detailed balance as closedness/monogenicity of the modular form. -/
  closed_modularForm :
    I.IsClosedGeometricForm modularForm

namespace KMSDetailedBalanceForm

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (D : KMSDetailedBalanceForm Region Point Tangent Value I)

/--
Detailed balance implies the thermal boundary integral vanishes.
-/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω D.modularForm = 0 :=
  I.boundaryIntegral_eq_zero_of_closed Ω D.modularForm D.closed_modularForm

end KMSDetailedBalanceForm

/-! ## 4. KMS/Stokes bridge packet -/

set_option linter.dupNamespace false

/--
KMS detailed-balance packet.

It packages:

* the algebraic KMS boundary identity;
* a geometric closed-form/Stokes readout;
* an explicit calibration law relating the chosen geometric form to the KMS
  correlation form.

The calibration law remains model-specific; the boundary identity and Stokes
vanishing theorems are constructive consequences.
-/
structure KMSDetailedBalance
    (A Region Point Tangent Value : Type*)
    [Mul A]
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) where
  /-- Algebraic KMS boundary data. -/
  kms :
    KMSBoundaryData A
  /-- Closed geometric/Stokes detailed-balance form. -/
  form :
    KMSDetailedBalanceForm Region Point Tangent Value I
  /-- Model-specific identification of geometric form with thermal readout. -/
  form_calibration : Prop

namespace KMSDetailedBalance

/--
A reduced KMS detailed-balance packet that omits the calibration law and its certificate.
It carries only the algebraic KMS boundary data and the geometric form.
-/
structure KMSDetailedBalanceCore
    (A Region Point Tangent Value : Type*)
    [Mul A]
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) where
  kms : KMSBoundaryData A
  form : KMSDetailedBalanceForm Region Point Tangent Value I

/-- Construct a `KMSDetailedBalanceCore` from a full `KMSDetailedBalance` packet, discarding
the calibration law and its proof. -/
@[simp] def KMSDetailedBalance.toCore
    {A Region Point Tangent Value : Type*}
    [Mul A] [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    (D : KMSDetailedBalance A Region Point Tangent Value I) :
    KMSDetailedBalanceCore A Region Point Tangent Value I :=
  { kms := D.kms,
    form := D.form }
variable
    {A Region Point Tangent Value : Type*}
    [Mul A]
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (D : KMSDetailedBalance A Region Point Tangent Value I)

/-- The stored calibration proposition. -/
def form_calibration_holds : Prop :=
  D.form_calibration

/-- Algebraic KMS/detailed-balance boundary identity. -/
theorem kms_boundary
    (t : ℝ)
    (a b : A) :
    lowerKMSCorrelation D.kms t a b =
      upperKMSCorrelation D.kms t a b :=
  lowerKMSCorrelation_eq_upper D.kms t a b

/-- KMS boundary identity through thermal Wilson transport. -/
theorem kms_boundary_wilson
    (t : ℝ)
    (a b : A) :
    lowerKMSCorrelation D.kms t a b =
      D.kms.omega_eval (thermalWilsonHolonomyAt D.kms t b) a :=
  lowerKMSCorrelation_eq_wilsonHolonomy D.kms t a b

/-- Stokes/detailed-balance boundary integral vanishes. -/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω D.form.modularForm = 0 :=
  D.form.boundaryIntegral_eq_zero Ω

/-! ## 5. Owner target -/

/--
Owner target for the constructive KMS/Stokes bridge.

This target records only the kernel-checked consequences already proved from the
stored algebraic KMS data and the closed-form/Stokes backend. It does not keep
the model-specific calibration proposition as theorem force.
-/
def KMSDetailedBalanceOwnerTarget
    (A Region Point Tangent Value : Type*)
    [Mul A]
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) : Prop :=
  ∀ (D : KMSDetailedBalance A Region Point Tangent Value I)
    (t : ℝ) (a b : A) (Ω : Region),
      lowerKMSCorrelation D.kms t a b = upperKMSCorrelation D.kms t a b ∧
      lowerKMSCorrelation D.kms t a b =
        D.kms.omega_eval (thermalWilsonHolonomyAt D.kms t b) a ∧
      I.boundaryIntegral Ω D.form.modularForm = 0

/--
Any installed KMS detailed-balance packet satisfies the owner-side KMS boundary,
thermal Wilson, and Stokes vanishing laws proved in this file.
-/
theorem kmsDetailedBalanceOwnerTarget
    (A Region Point Tangent Value : Type*)
    [Mul A]
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value) :
    ∀ (D : KMSDetailedBalance A Region Point Tangent Value I)
      (t : ℝ) (a b : A) (Ω : Region),
        lowerKMSCorrelation D.kms t a b = upperKMSCorrelation D.kms t a b ∧
        lowerKMSCorrelation D.kms t a b =
          D.kms.omega_eval (thermalWilsonHolonomyAt D.kms t b) a ∧
        I.boundaryIntegral Ω D.form.modularForm = 0 := by
  intro D t a b Ω
  exact ⟨D.kms_boundary t a b, D.kms_boundary_wilson t a b, D.boundaryIntegral_eq_zero Ω⟩

end KMSDetailedBalance

end InfoGeometry.Thermo.KMSDetailedBalance
