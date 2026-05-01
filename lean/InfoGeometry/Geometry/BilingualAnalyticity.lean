import Mathlib

noncomputable section

namespace InfoGeometry.Geometry.BilingualAnalyticity

/-! ## 1. Phase structures -/

/--
A real-linear phase structure.

This is the real doubled replacement for multiplication by `i`.
-/
structure PhaseStructure
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- Phase axis / complex structure. -/
  K : X →L[ℝ] X

  /-- `K² = -1`. -/
  K_square :
    K.comp K = -(ContinuousLinearMap.id ℝ X)

namespace PhaseStructure

variable
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (J : PhaseStructure X)

/--
Phase-linearity of a bounded real-linear map between phase spaces.
-/
def IsPhaseLinearMap
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y)
    (Ktar : PhaseStructure Y) : Prop :=
  L.comp J.K = Ktar.K.comp L

variable
    {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The identity map is phase-linear. -/
theorem id_phaseLinear
    (KX : PhaseStructure X) :
    KX.IsPhaseLinearMap (ContinuousLinearMap.id ℝ X) KX := by
  ext v
  simp

/-- Composition of phase-linear maps is phase-linear. -/
theorem comp_phaseLinear
    (KX : PhaseStructure X)
    (KY : PhaseStructure Y)
    (KZ : PhaseStructure Z)
    {L : X →L[ℝ] Y}
    {M : Y →L[ℝ] Z}
    (hL : KX.IsPhaseLinearMap L KY)
    (hM : KY.IsPhaseLinearMap M KZ) :
    KX.IsPhaseLinearMap (M.comp L) KZ := by
  dsimp [IsPhaseLinearMap] at hL hM ⊢
  calc
    (M.comp L).comp KX.K = M.comp (L.comp KX.K) := by
      ext v
      simp [ContinuousLinearMap.comp_apply]
    _ = M.comp (KY.K.comp L) := by rw [hL]
    _ = (M.comp KY.K).comp L := by
      ext v
      simp [ContinuousLinearMap.comp_apply]
    _ = (KZ.K.comp M).comp L := by rw [hM]
    _ = KZ.K.comp (M.comp L) := by
      ext v
      simp [ContinuousLinearMap.comp_apply]

end PhaseStructure

/-! ## 2. Cauchy analyticity -/

/--
Cauchy analyticity at a point, in real phase-linear form.

The function is real-Fréchet differentiable, and its derivative commutes with
the phase structures.
-/
structure CauchyAnalyticAt
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (F : X → Y)
    (x : X) where

  /-- Real Fréchet derivative. -/
  deriv : X →L[ℝ] Y

  /-- Real differentiability witness. -/
  has_fderiv_at :
    HasFDerivAt F deriv x

  /--
  Cauchy-Riemann law in phase form:

  `dF_x ∘ Kdom = Ktar ∘ dF_x`.
  -/
  phase_linear_deriv :
    deriv.comp Kdom.K = Ktar.K.comp deriv

namespace CauchyAnalyticAt

variable
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Y}
    {F : X → Y}
    {x : X}

variable (A : CauchyAnalyticAt Kdom Ktar F x)

/--
Pointwise Cauchy-Riemann law.
-/
theorem cauchyRiemann_apply
    (v : X) :
    A.deriv (Kdom.K v) = Ktar.K (A.deriv v) := by
  have h :=
    congrArg
      (fun T : X →L[ℝ] Y => T v)
      A.phase_linear_deriv
  simpa [ContinuousLinearMap.comp_apply] using h

/-- The derivative is phase-linear. -/
theorem deriv_phaseLinear :
    Kdom.IsPhaseLinearMap A.deriv Ktar :=
  A.phase_linear_deriv

end CauchyAnalyticAt

/-! ## 2A. Constructive Cauchy-analytic constructors -/

namespace CauchyAnalyticAt

variable
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/--
The identity map is Cauchy-analytic for any phase structure.
-/
def id
    (K : PhaseStructure X)
    (x : X) :
    CauchyAnalyticAt K K (fun y : X => y) x where
  deriv := ContinuousLinearMap.id ℝ X
  has_fderiv_at := by
    simpa using
      (hasFDerivAt_id x :
        HasFDerivAt (fun y : X => y) (ContinuousLinearMap.id ℝ X) x)
  phase_linear_deriv := by
    ext v
    simp

/--
A constant map is Cauchy-analytic, with zero derivative.
-/
def const
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (y0 : Y)
    (x : X) :
    CauchyAnalyticAt Kdom Ktar (fun _ : X => y0) x where
  deriv := 0
  has_fderiv_at := by
    simpa using
      (hasFDerivAt_const (c := y0) (x := x) :
        HasFDerivAt (fun _ : X => y0) (0 : X →L[ℝ] Y) x)
  phase_linear_deriv := by
    ext v
    simp

/--
A continuous real-linear map whose operator commutes with the source and target
phase structures is Cauchy-analytic everywhere.
-/
def ofContinuousLinearMap
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (L : X →L[ℝ] Y)
    (hL : L.comp Kdom.K = Ktar.K.comp L)
    (x : X) :
    CauchyAnalyticAt Kdom Ktar (fun y : X => L y) x where
  deriv := L
  has_fderiv_at := L.hasFDerivAt
  phase_linear_deriv := hL

/--
Composition of Cauchy-analytic maps is Cauchy-analytic.

This is the constructive phase-form Cauchy-Riemann chain rule.
-/
def comp
    {KX : PhaseStructure X}
    {KY : PhaseStructure Y}
    {KZ : PhaseStructure Z}
    {F : X → Y}
    {G : Y → Z}
    {x : X}
    (A : CauchyAnalyticAt KX KY F x)
    (B : CauchyAnalyticAt KY KZ G (F x)) :
    CauchyAnalyticAt KX KZ (fun u : X => G (F u)) x where
  deriv := B.deriv.comp A.deriv
  has_fderiv_at := B.has_fderiv_at.comp x A.has_fderiv_at
  phase_linear_deriv := by
    ext v
    simp [ContinuousLinearMap.comp_apply]
    rw [A.cauchyRiemann_apply v]
    rw [B.cauchyRiemann_apply (A.deriv v)]

/--
The derivative of the composition is the expected composite derivative.
-/
theorem comp_deriv
    {KX : PhaseStructure X}
    {KY : PhaseStructure Y}
    {KZ : PhaseStructure Z}
    {F : X → Y}
    {G : Y → Z}
    {x : X}
    (A : CauchyAnalyticAt KX KY F x)
    (B : CauchyAnalyticAt KY KZ G (F x)) :
    (comp A B).deriv = B.deriv.comp A.deriv :=
  rfl

end CauchyAnalyticAt

/-! ## 3. Operator-valued one-forms -/

/--
An abstract operator-valued one-form.

`Point` is the geometric point space.
`Tangent` is the tangent direction type.
`Value` is the noncommutative target/readout type.
-/
abbrev OperatorOneForm
    (Point Tangent Value : Type*) :=
  Point → Tangent → Value

/--
Left Cauchy form.

In a concrete operator model this is morally

`ω_F(Z,V) = F(Z) ∘ V`.

The multiplication/order is supplied by `leftAction`.
-/
def leftCauchyForm
    {Point Tangent Value : Type*}
    (F : Point → Value)
    (leftAction : Value → Tangent → Value) :
    OperatorOneForm Point Tangent Value :=
  fun Z V => leftAction (F Z) V

/--
Right Cauchy form.

In a concrete operator model this is morally

`ω_F(Z,V) = V ∘ F(Z)`.

The multiplication/order is supplied by `rightAction`.
-/
def rightCauchyForm
    {Point Tangent Value : Type*}
    (F : Point → Value)
    (rightAction : Tangent → Value → Value) :
    OperatorOneForm Point Tangent Value :=
  fun Z V => rightAction V (F Z)

/-! ## 4. Hestenes/Stokes geometric integral backend -/

/--
A geometric integral calculus backend.

This is the Hestenes generalized Stokes/Gauss layer.

It does not pretend to construct integration from scratch. A concrete model
supplies path, boundary, volume, and geometric-derivative data.

The key law is:

`boundaryIntegral Ω ω = volumeIntegral Ω (geometricDerivative ω)`.
-/
structure GeometricIntegralBackend
    (Region Point Tangent Value : Type*)
    [AddCommGroup Value] [Module ℝ Value] where

  /-- Boundary integral of an operator-valued one-form. -/
  boundaryIntegral :
    Region → OperatorOneForm Point Tangent Value → Value

  /-- Volume integral of a value-valued density/readout. -/
  volumeIntegral :
    Region → (Point → Value) → Value

  /--
  Geometric derivative / exterior derivative / Hestenes vector derivative of
  a one-form.
  -/
  geometricDerivative :
    OperatorOneForm Point Tangent Value → Point → Value

  /-- Generalized Stokes/Gauss theorem. -/
  stokes_law :
    ∀ Ω ω,
      boundaryIntegral Ω ω =
        volumeIntegral Ω (geometricDerivative ω)

  /--
  If a density vanishes pointwise on the relevant region, its volume integral
  vanishes.

  The precise support/membership condition is model-dependent, so this socket
  uses a global pointwise-zero form.
  -/
  volumeIntegral_zero_of_pointwise_zero :
    ∀ Ω f,
      (∀ p : Point, f p = 0) →
        volumeIntegral Ω f = 0

namespace GeometricIntegralBackend

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]

variable (I : GeometricIntegralBackend Region Point Tangent Value)

/--
A one-form is Hestenes-closed / monogenic when its geometric derivative
vanishes.
-/
def IsClosedGeometricForm
    (ω : OperatorOneForm Point Tangent Value) : Prop :=
  ∀ p : Point, I.geometricDerivative ω p = 0

/--
Constructive Cauchy-Stokes theorem:

if the Hestenes/geometric derivative of the form vanishes, then the boundary
integral vanishes.
-/
theorem boundaryIntegral_eq_zero_of_closed
    (Ω : Region)
    (ω : OperatorOneForm Point Tangent Value)
    (hclosed : I.IsClosedGeometricForm ω) :
    I.boundaryIntegral Ω ω = 0 := by
  rw [I.stokes_law Ω ω]
  exact I.volumeIntegral_zero_of_pointwise_zero Ω
    (I.geometricDerivative ω)
    hclosed

end GeometricIntegralBackend

/-! ## 5. Hestenes analyticity -/

/--
Hestenes analyticity on a region.

A function is Hestenes-analytic relative to a chosen Cauchy form if the
associated geometric one-form is closed/monogenic.
-/
structure HestenesAnalyticOn
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (F : Point → Value) where

  /-- The Cauchy/geometric one-form associated to `F`. -/
  cauchyForm :
    OperatorOneForm Point Tangent Value

  /-- The form is closed/monogenic. -/
  closed_form :
    I.IsClosedGeometricForm cauchyForm

namespace HestenesAnalyticOn

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {F : Point → Value}

variable (A : HestenesAnalyticOn I F)

/--
Cauchy theorem in Hestenes-Stokes form:

the integral of the analytic Cauchy form around a boundary vanishes.
-/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω A.cauchyForm = 0 :=
  I.boundaryIntegral_eq_zero_of_closed Ω A.cauchyForm A.closed_form

/-- Construct a Hestenes-analytic datum from a closed geometric form. -/
def ofClosedForm
    (ω : OperatorOneForm Point Tangent Value)
    (hω : I.IsClosedGeometricForm ω) :
    HestenesAnalyticOn I F where
  cauchyForm := ω
  closed_form := hω

/-- The boundary integral of a closed form vanishes. -/
theorem boundaryIntegral_eq_zero_of_closedForm
    (Ω : Region)
    (ω : OperatorOneForm Point Tangent Value)
    (hω : I.IsClosedGeometricForm ω) :
    I.boundaryIntegral Ω ω = 0 :=
  I.boundaryIntegral_eq_zero_of_closed Ω ω hω

end HestenesAnalyticOn

/-! ## 6. Bilingual analyticity -/

/--
Bilingual analyticity.

This packages:

* Cauchy side: phase-linear real derivative;
* Hestenes side: closed geometric one-form.

The bridge between the derivative and the geometric form is model-dependent
and is therefore carried as law/certificate data.
-/
structure BilingualAnalyticAt
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (F : X → Y)
    (Fgeo : Point → Value)
    (x : X) where

  /-- Cauchy/phase derivative analyticity. -/
  cauchy :
    CauchyAnalyticAt Kdom Ktar F x

  /-- Hestenes/Stokes analyticity. -/
  hestenes :
    HestenesAnalyticOn I Fgeo

  /--
  Compatibility law between the phase-linear derivative and the geometric
  Stokes form.

  In a concrete model this says that the geometric derivative of the Cauchy
  form is exactly the Cauchy-Riemann obstruction.
  -/
  cauchy_hestenes_compatibility_law : Prop

  /-- Proof/certificate of the compatibility law. -/
  cauchy_hestenes_compatibility_certificate :
    cauchy_hestenes_compatibility_law

namespace BilingualAnalyticAt

variable
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Y}
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {F : X → Y}
    {Fgeo : Point → Value}
    {x : X}

variable (A : BilingualAnalyticAt Kdom Ktar I F Fgeo x)

/--
Cauchy-Riemann law from the bilingual analytic datum.
-/
theorem cauchyRiemann_apply
    (v : X) :
    A.cauchy.deriv (Kdom.K v) =
      Ktar.K (A.cauchy.deriv v) :=
  A.cauchy.cauchyRiemann_apply v

/--
Hestenes boundary Cauchy theorem from the bilingual analytic datum.
-/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω A.hestenes.cauchyForm = 0 :=
  A.hestenes.boundaryIntegral_eq_zero Ω

/-- The stored Cauchy/Hestenes compatibility law is available as a proof. -/
theorem compatibility_valid :
    A.cauchy_hestenes_compatibility_law :=
  A.cauchy_hestenes_compatibility_certificate

end BilingualAnalyticAt

/-! ## 7. Operator target specialization sockets -/

/--
A noncommutative operator analyticity side.

Left and right forms are distinct in a noncommutative algebra. A model may
choose one side or require both.
-/
inductive OperatorAnalyticSide where
  | left
  | right
  | twoSided
deriving DecidableEq, Repr

/--
A noncommutative Cauchy-form calibration.

This states how to build left and right Cauchy forms from an operator-valued
function.
-/
structure NoncommutativeCauchyFormCalibration
    (Point Tangent Value : Type*) where

  /-- Left action, morally `F(Z) ∘ dZ`. -/
  leftAction :
    Value → Tangent → Value

  /-- Right action, morally `dZ ∘ F(Z)`. -/
  rightAction :
    Tangent → Value → Value

  /--
  Optional law relating left and right forms on the phase-linear/central
  subalgebra.
  -/
  left_right_compatibility_law : Prop

  /-- Proof/certificate of compatibility. -/
  left_right_compatibility_certificate :
    left_right_compatibility_law

namespace NoncommutativeCauchyFormCalibration

variable {Point Tangent Value : Type*}
variable (C : NoncommutativeCauchyFormCalibration Point Tangent Value)

/-- Left operator Cauchy form of `F`. -/
def leftForm
    (F : Point → Value) :
    OperatorOneForm Point Tangent Value :=
  leftCauchyForm F C.leftAction

/-- Right operator Cauchy form of `F`. -/
def rightForm
    (F : Point → Value) :
    OperatorOneForm Point Tangent Value :=
  rightCauchyForm F C.rightAction

/-- The stored left/right compatibility law is available as a proof. -/
theorem left_right_compatibility_valid :
    C.left_right_compatibility_law :=
  C.left_right_compatibility_certificate

end NoncommutativeCauchyFormCalibration

/-! ## 8. Cauchy integral formula socket -/

/--
A noncommutative Cauchy kernel datum.

In classical complex analysis the Cauchy kernel is `(ζ - z)⁻¹`.

In an operator algebra, order matters. A concrete model must specify whether
the kernel acts on the left, on the right, or in a two-sided calibrated way.
-/
structure NoncommutativeCauchyKernel
    (Point Value Kernel : Type*) where

  /-- Kernel readout, morally `(ζ - z)⁻¹`. -/
  kernel :
    Point → Point → Kernel

  /-- Left application of the kernel to a value. -/
  applyLeft :
    Kernel → Value → Value

  /-- Right application of the kernel to a value. -/
  applyRight :
    Value → Kernel → Value

  /-- Resolvent/kernel existence law. -/
  resolvent_law : Prop

  /-- Proof/certificate of the resolvent law. -/
  resolvent_certificate :
    resolvent_law

namespace NoncommutativeCauchyKernel

variable {Point Value Kernel : Type*}
variable (K : NoncommutativeCauchyKernel Point Value Kernel)

/-- The stored resolvent/kernel existence law is available as a proof. -/
theorem resolvent_valid :
    K.resolvent_law :=
  K.resolvent_certificate

end NoncommutativeCauchyKernel

/--
Cauchy integral formula socket.

This is deliberately witness-gated. It is not a theorem of the abstract
Stokes backend alone. It needs a concrete kernel, domain, orientation,
regularity, and resolvent calculus.
-/
structure CauchyIntegralFormulaDatum
    (Region Point Tangent Value Kernel : Type*)
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (K : NoncommutativeCauchyKernel Point Value Kernel) where

  /-- Formula law, model-specific. -/
  cauchy_formula_law : Prop

  /-- Proof/certificate of the formula law. -/
  cauchy_formula_certificate :
    cauchy_formula_law

namespace CauchyIntegralFormulaDatum

variable
    {Region Point Tangent Value Kernel : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {K : NoncommutativeCauchyKernel Point Value Kernel}

variable (C : CauchyIntegralFormulaDatum Region Point Tangent Value Kernel I K)

/-- The stored Cauchy integral formula law is available as a proof. -/
theorem cauchy_formula_valid :
    C.cauchy_formula_law :=
  C.cauchy_formula_certificate

end CauchyIntegralFormulaDatum

end InfoGeometry.Geometry.BilingualAnalyticity
