import Mathlib

noncomputable section

namespace BilingualAnalyticity

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

/-- Pointwise form of phase-linearity. -/
theorem phaseLinear_apply
    {KX : PhaseStructure X}
    {KY : PhaseStructure Y}
    {L : X →L[ℝ] Y}
    (hL : KX.IsPhaseLinearMap L KY)
    (v : X) :
    L (KX.K v) = KY.K (L v) := by
  have h := congrArg (fun T : X →L[ℝ] Y => T v) hL
  simpa [IsPhaseLinearMap, ContinuousLinearMap.comp_apply] using h

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

This is pointwise Cauchy analyticity/differentiability. It is not a
power-series or open-neighborhood holomorphicity assertion.

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
  exact PhaseStructure.phaseLinear_apply A.phase_linear_deriv v

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
      (hasFDerivAt_id (𝕜 := ℝ) (E := X) x :
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
      (hasFDerivAt_const y0 x :
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
  has_fderiv_at := by
    simpa using
      (L.hasFDerivAt (x := x) :
        HasFDerivAt (fun y : X => L y) L x)
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
  has_fderiv_at := by
    simpa [Function.comp_def] using
      B.has_fderiv_at.comp x A.has_fderiv_at
  phase_linear_deriv := by
    ext v
    change B.deriv (A.deriv (KX.K v)) =
      KZ.K (B.deriv (A.deriv v))
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

/-! ## 2B. Mathlib complex analyticity bridge -/

/--
The canonical phase axis on `ℂ`, viewed as a real continuous-linear map:
multiplication by `I`.
-/
noncomputable def complexIMap : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ Complex.I

/--
The canonical real phase structure on `ℂ`.

Its phase operator is multiplication by `I`, so the square law is the usual
`I * I = -1`.
-/
noncomputable def complexPhaseStructure : PhaseStructure ℂ where
  K := complexIMap
  K_square := by
    ext z
    change Complex.I * (Complex.I * z) = -z
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/--
A complex continuous-linear map is phase-linear after restriction of scalars
to `ℝ`.
-/
theorem complexLinearMap_phaseLinear
    (L : ℂ →L[ℂ] ℂ) :
    complexPhaseStructure.IsPhaseLinearMap (L.restrictScalars ℝ)
      complexPhaseStructure := by
  ext z
  change L (Complex.I * z) = Complex.I * L z
  simpa only [smul_eq_mul] using L.map_smul Complex.I z

/--
Mathlib power-series analyticity over `ℂ` implies the repository's pointwise
Cauchy analyticity on the canonical complex phase structure.

This is only the honest one-way bridge: `AnalyticAt` supplies a complex
Fréchet derivative, and complex linearity of that derivative supplies the
phase-form Cauchy-Riemann law.
-/
def analyticAt_complex_to_cauchyAnalyticAt
    {f : ℂ → ℂ}
    {x : ℂ}
    (hf : AnalyticAt ℂ f x) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f x := by
  let dC : ℂ →L[ℂ] ℂ := fderiv ℂ f x
  refine
    { deriv := dC.restrictScalars ℝ
      has_fderiv_at := ?_
      phase_linear_deriv := ?_ }
  · exact hf.differentiableAt.hasFDerivAt.restrictScalars ℝ
  · exact complexLinearMap_phaseLinear dC

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
  stokes_eq :
    ∀ Ω ω,
      boundaryIntegral Ω ω =
        volumeIntegral Ω (geometricDerivative ω)

  /--
  If a density vanishes pointwise on the relevant region, its volume integral
  vanishes.

  The precise support/membership condition is model-dependent, so this generic
  backend uses a global pointwise-zero form.
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
  rw [I.stokes_eq Ω ω]
  exact I.volumeIntegral_zero_of_pointwise_zero Ω
    (I.geometricDerivative ω)
    hclosed

end GeometricIntegralBackend

/-! ## 5. Hestenes analyticity -/

/--
A concrete calibration assigning a geometric one-form to a function.

Using this avoids attaching an arbitrary closed form to an unrelated function:
the Hestenes form is definitionally `formOf F`.
-/
structure HestenesFormCalibration
    (Point Tangent Value : Type*) where
  /-- Geometric one-form associated to a value-valued function. -/
  formOf :
    (Point → Value) → OperatorOneForm Point Tangent Value

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

/--
Construct a Hestenes-analytic datum from a concrete function-to-form
calibration.  This is the non-vacuous constructor: the stored form is
definitionally the calibrated form of `F`.
-/
def ofCalibration
    (C : HestenesFormCalibration Point Tangent Value)
    (hclosed : I.IsClosedGeometricForm (C.formOf F)) :
    HestenesAnalyticOn I F where
  cauchyForm := C.formOf F
  closed_form := hclosed

@[simp]
theorem ofCalibration_cauchyForm
    (C : HestenesFormCalibration Point Tangent Value)
    (hclosed : I.IsClosedGeometricForm (C.formOf F)) :
    (ofCalibration (I := I) (F := F) C hclosed).cauchyForm = C.formOf F :=
  by
    rfl

end HestenesAnalyticOn

/-! ## 6A. Constructive Cauchy/Hestenes compatibility -/

/--
A constructive Cauchy/Hestenes compatibility backend.

This replaces a vague compatibility proposition by explicit data:

* `cauchyFormOf L` builds the geometric Cauchy form from a real derivative `L`;
* `obstructionOf L` is the Hestenes/geometric obstruction associated to `L`;
* phase-linearity of `L` forces that obstruction to vanish;
* the geometric derivative of the Cauchy form is exactly that obstruction.

Thus Cauchy phase-linearity constructively implies Hestenes closedness.
-/
structure CauchyHestenesCompatibility
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (I : GeometricIntegralBackend Region Point Tangent Value) where

  /-- Geometric Cauchy form associated to a real derivative. -/
  cauchyFormOf :
    (X →L[ℝ] Y) → OperatorOneForm Point Tangent Value

  /--
  Cauchy/Hestenes obstruction associated to a derivative.

  Morally this is the geometric derivative of the Cauchy form, equivalent to
  the Cauchy-Riemann obstruction.
  -/
  obstructionOf :
    (X →L[ℝ] Y) → Point → Value

  /-- If the derivative is phase-linear, the obstruction vanishes. -/
  obstruction_zero_of_phaseLinear :
    ∀ L : X →L[ℝ] Y,
      L.comp Kdom.K = Ktar.K.comp L →
        ∀ p : Point, obstructionOf L p = 0

  /-- The geometric derivative of the Cauchy form is exactly the obstruction. -/
  geometricDerivative_eq_obstruction :
    ∀ L : X →L[ℝ] Y,
      ∀ p : Point,
        I.geometricDerivative (cauchyFormOf L) p =
          obstructionOf L p

namespace CauchyHestenesCompatibility

variable
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Y}
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (B : CauchyHestenesCompatibility Kdom Ktar I)

/-- A phase-linear derivative produces a closed Hestenes Cauchy form. -/
theorem closed_form_of_phaseLinear
    (L : X →L[ℝ] Y)
    (hL : L.comp Kdom.K = Ktar.K.comp L) :
    I.IsClosedGeometricForm (B.cauchyFormOf L) := by
  intro p
  rw [B.geometricDerivative_eq_obstruction L p]
  exact B.obstruction_zero_of_phaseLinear L hL p

/-- A Cauchy-analytic derivative produces a closed Hestenes form. -/
theorem closed_form_of_cauchyAnalyticAt
    {F : X → Y}
    {x : X}
    (A : CauchyAnalyticAt Kdom Ktar F x) :
    I.IsClosedGeometricForm (B.cauchyFormOf A.deriv) :=
  B.closed_form_of_phaseLinear A.deriv A.phase_linear_deriv

/--
Construct the Hestenes analytic datum from a Cauchy analytic datum and a
compatibility backend.
-/
def hestenesAnalyticOfCauchy
    {F : X → Y}
    {Fgeo : Point → Value}
    {x : X}
    (A : CauchyAnalyticAt Kdom Ktar F x) :
    HestenesAnalyticOn I Fgeo where
  cauchyForm := B.cauchyFormOf A.deriv
  closed_form := B.closed_form_of_cauchyAnalyticAt A

/--
Constructive bilingual Cauchy theorem.

If a function is Cauchy-analytic and the model supplies a Cauchy/Hestenes
compatibility backend, then the corresponding Hestenes boundary integral
vanishes.
-/
theorem boundaryIntegral_eq_zero_of_cauchyAnalyticAt
    {F : X → Y}
    {x : X}
    (A : CauchyAnalyticAt Kdom Ktar F x)
    (Ω : Region) :
    I.boundaryIntegral Ω (B.cauchyFormOf A.deriv) = 0 :=
  I.boundaryIntegral_eq_zero_of_closed
    Ω
    (B.cauchyFormOf A.deriv)
    (B.closed_form_of_cauchyAnalyticAt A)

/--
A phase-linear derivative gives a zero boundary integral for its Cauchy form.
-/
theorem boundaryIntegral_eq_zero_of_phaseLinear
    (L : X →L[ℝ] Y)
    (hL : L.comp Kdom.K = Ktar.K.comp L)
    (Ω : Region) :
    I.boundaryIntegral Ω (B.cauchyFormOf L) = 0 :=
  I.boundaryIntegral_eq_zero_of_closed
    Ω
    (B.cauchyFormOf L)
    (B.closed_form_of_phaseLinear L hL)

end CauchyHestenesCompatibility

/-! ## 6B. Bilingual analyticity, processed -/

/--
Bilingual analyticity.

This packages:

* Cauchy side: phase-linear real derivative;
* constructive Cauchy/Hestenes compatibility.

The Hestenes closed form is now derived from the Cauchy side. It is not stored
as an independent shadow.
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

  /--
  Constructive compatibility between the Cauchy derivative and the Hestenes
  geometric form.
  -/
  compatibility :
    CauchyHestenesCompatibility Kdom Ktar I

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
The associated Hestenes analytic datum is constructed from the Cauchy side.
-/
def hestenes :
    HestenesAnalyticOn I Fgeo :=
  A.compatibility.hestenesAnalyticOfCauchy A.cauchy

/-- The Hestenes form is closed by construction from the Cauchy derivative. -/
theorem closed_form_from_cauchy :
    I.IsClosedGeometricForm
      (A.compatibility.cauchyFormOf A.cauchy.deriv) :=
  A.compatibility.closed_form_of_cauchyAnalyticAt A.cauchy

/-- The Hestenes boundary theorem follows constructively from the Cauchy side. -/
theorem boundaryIntegral_eq_zero_from_cauchy
    (Ω : Region) :
    I.boundaryIntegral Ω
      (A.compatibility.cauchyFormOf A.cauchy.deriv) = 0 :=
  A.compatibility.boundaryIntegral_eq_zero_of_cauchyAnalyticAt A.cauchy Ω

/--
Hestenes boundary Cauchy theorem from the bilingual analytic datum.

This is the short-form API theorem for downstream modules.  The form itself is
the one constructed from the Cauchy derivative by the compatibility backend.
-/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω A.hestenes.cauchyForm = 0 :=
  A.hestenes.boundaryIntegral_eq_zero Ω

end BilingualAnalyticAt

/-! ## 7. Operator target specializations -/

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

Left and right Cauchy forms differ in a noncommutative target. They agree on
values that are central for the chosen left/right actions.
-/
structure NoncommutativeCauchyFormCalibration
    (Point Tangent Value : Type*) where

  /-- Left action, morally `F(Z) ∘ dZ`. -/
  leftAction :
    Value → Tangent → Value

  /-- Right action, morally `dZ ∘ F(Z)`. -/
  rightAction :
    Tangent → Value → Value

  /-- Values for which left and right action agree. -/
  IsCentralValue :
    Value → Prop

  /-- Constructive left/right compatibility on central values. -/
  left_right_compatibility :
    ∀ (a : Value) (v : Tangent),
      IsCentralValue a →
        leftAction a v = rightAction v a

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

/-- If `F` takes central values, the left and right Cauchy forms coincide. -/
theorem leftForm_eq_rightForm_of_central
    (F : Point → Value)
    (hF : ∀ Z : Point, C.IsCentralValue (F Z)) :
    C.leftForm F = C.rightForm F := by
  apply funext
  intro Z
  apply funext
  intro V
  dsimp [leftForm, rightForm, leftCauchyForm, rightCauchyForm]
  exact C.left_right_compatibility (F Z) V (hF Z)

end NoncommutativeCauchyFormCalibration

/-! ## 7A. Multiplicative ring-valued Cauchy calibration -/

/--
Concrete multiplicative Cauchy-form calibration for ring-valued forms.

Left action is multiplication on the left.
Right action is multiplication on the right.
Centrality is literal commutation with every tangent value.
-/
def multiplicativeCauchyFormCalibration
    (Point Value : Type*)
    [Ring Value] :
    NoncommutativeCauchyFormCalibration Point Value Value where
  leftAction := fun a v => a * v
  rightAction := fun v a => v * a
  IsCentralValue := fun a => ∀ v : Value, a * v = v * a
  left_right_compatibility := by
    intro a v ha
    exact ha v

namespace multiplicativeCauchyFormCalibration

variable {Point Value : Type*}
variable [Ring Value]

/-- Centrality predicate for the multiplicative calibration. -/
theorem isCentralValue_iff
    (a : Value) :
    (multiplicativeCauchyFormCalibration Point Value).IsCentralValue a ↔
      ∀ v : Value, a * v = v * a :=
  Iff.rfl

/-- If `Value` is a complex algebra, scalar values are central. -/
theorem algebraMap_isCentralValue
    [Algebra ℂ Value]
    (ζ : ℂ) :
    (multiplicativeCauchyFormCalibration Point Value).IsCentralValue
      (algebraMap ℂ Value ζ) := by
  intro v
  exact Algebra.commutes ζ v

/--
For scalar-valued functions embedded into a complex algebra, left and right
multiplicative Cauchy forms coincide.
-/
theorem leftForm_eq_rightForm_of_scalarValued
    [Algebra ℂ Value]
    (F : Point → ℂ) :
    (multiplicativeCauchyFormCalibration Point Value).leftForm
        (fun Z : Point => algebraMap ℂ Value (F Z))
      =
    (multiplicativeCauchyFormCalibration Point Value).rightForm
        (fun Z : Point => algebraMap ℂ Value (F Z)) := by
  apply
    (multiplicativeCauchyFormCalibration Point Value).leftForm_eq_rightForm_of_central
  intro Z
  exact algebraMap_isCentralValue (Point := Point) (Value := Value) (F Z)

end multiplicativeCauchyFormCalibration

/-! ## 8. Noncommutative Cauchy kernel -/

/--
A noncommutative Cauchy kernel datum.

In classical complex analysis the Cauchy kernel is `(ζ - z)⁻¹`.

In an operator algebra, the difference element and inverse must be supplied
with explicit left and right inverse laws.

The predicate `IsAdmissible ζ z` excludes singular pairs, such as `ζ = z`
in the scalar complex model.
-/
structure NoncommutativeCauchyKernel
    (Param Point Value : Type*) [Ring Value] where

  /-- Pairs where the kernel exists. -/
  IsAdmissible :
    Param → Point → Prop

  /-- Difference element, morally `ζ - z`. -/
  diff :
    Param → Point → Value

  /-- Kernel element, morally `(ζ - z)⁻¹`. -/
  kernel :
    Param → Point → Value

  /-- Left inverse law: `(ζ-z) * (ζ-z)⁻¹ = 1`. -/
  left_inverse :
    ∀ ζ z,
      IsAdmissible ζ z →
        diff ζ z * kernel ζ z = 1

  /-- Right inverse law: `(ζ-z)⁻¹ * (ζ-z) = 1`. -/
  right_inverse :
    ∀ ζ z,
      IsAdmissible ζ z →
        kernel ζ z * diff ζ z = 1

namespace NoncommutativeCauchyKernel

variable {Param Point Value : Type*} [Ring Value]
variable (K : NoncommutativeCauchyKernel Param Point Value)

/-- The difference times the kernel is `1` on admissible pairs. -/
theorem diff_mul_kernel
    (ζ : Param)
    (z : Point)
    (h : K.IsAdmissible ζ z) :
    K.diff ζ z * K.kernel ζ z = 1 :=
  K.left_inverse ζ z h

/-- The kernel times the difference is `1` on admissible pairs. -/
theorem kernel_mul_diff
    (ζ : Param)
    (z : Point)
    (h : K.IsAdmissible ζ z) :
    K.kernel ζ z * K.diff ζ z = 1 :=
  K.right_inverse ζ z h

/-- A kernel with two-sided inverse laws is unique on admissible pairs. -/
theorem kernel_unique
    (ζ : Param)
    (z : Point)
    (hadm : K.IsAdmissible ζ z)
    (hInv : Value)
    (_h_left : K.diff ζ z * hInv = 1)
    (h_right : hInv * K.diff ζ z = 1) :
    hInv = K.kernel ζ z := by
  calc
    hInv = hInv * 1 := by
      rw [mul_one]
    _ = hInv * (K.diff ζ z * K.kernel ζ z) := by
      rw [K.left_inverse ζ z hadm]
    _ = (hInv * K.diff ζ z) * K.kernel ζ z := by
      rw [mul_assoc]
    _ = 1 * K.kernel ζ z := by
      rw [h_right]
    _ = K.kernel ζ z := by
      rw [one_mul]

end NoncommutativeCauchyKernel

/-! ## 9. Scalar complex Cauchy kernel -/

/--
The scalar complex Cauchy kernel.

Admissibility excludes the diagonal `ζ = z`, equivalently `ζ - z ≠ 0`.
-/
def scalarComplexCauchyKernel :
    NoncommutativeCauchyKernel ℂ ℂ ℂ where
  IsAdmissible := fun ζ z => ζ - z ≠ 0
  diff := fun ζ z => ζ - z
  kernel := fun ζ z => (ζ - z)⁻¹
  left_inverse := by
    intro ζ z h
    exact mul_inv_cancel₀ h
  right_inverse := by
    intro ζ z h
    exact inv_mul_cancel₀ h

namespace scalarComplexCauchyKernel

/-- Admissibility for the scalar complex kernel is exactly nonvanishing of `ζ - z`. -/
theorem admissible_iff
    (ζ z : ℂ) :
    scalarComplexCauchyKernel.IsAdmissible ζ z ↔ ζ - z ≠ 0 :=
  Iff.rfl

/-- Scalar complex difference times Cauchy kernel is `1`. -/
theorem diff_mul_kernel
    (ζ z : ℂ)
    (h : ζ - z ≠ 0) :
    scalarComplexCauchyKernel.diff ζ z *
      scalarComplexCauchyKernel.kernel ζ z = 1 :=
  scalarComplexCauchyKernel.left_inverse ζ z h

/-- Scalar complex Cauchy kernel times difference is `1`. -/
theorem kernel_mul_diff
    (ζ z : ℂ)
    (h : ζ - z ≠ 0) :
    scalarComplexCauchyKernel.kernel ζ z *
      scalarComplexCauchyKernel.diff ζ z = 1 :=
  scalarComplexCauchyKernel.right_inverse ζ z h

/-- Uniqueness of the scalar complex Cauchy kernel. -/
theorem kernel_unique
    (ζ z : ℂ)
    (h : ζ - z ≠ 0)
    (u : ℂ)
    (h_left : (ζ - z) * u = 1)
    (h_right : u * (ζ - z) = 1) :
    u = scalarComplexCauchyKernel.kernel ζ z :=
  NoncommutativeCauchyKernel.kernel_unique
    scalarComplexCauchyKernel ζ z h u h_left h_right

end scalarComplexCauchyKernel

/-! ## 11. General supplied operator resolvent kernel -/

/--
Ring-level phase linearity for an operator target.

`T` is phase-linear relative to `K` when it commutes with `K`.
-/
def PhaseLinearValue
    {Value : Type*} [Mul Value]
    (K T : Value) : Prop :=
  T * K = K * T

/-- A scalar element in a complex algebra. -/
def scalarOperator
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (ζ : ℂ) : Value :=
  algebraMap ℂ Value ζ

/-- The operator resolvent difference: `ζ • 1 - Z`. -/
def operatorResolventDiff
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (ζ : ℂ)
    (Z : Value) : Value :=
  scalarOperator ζ - Z

/-- Scalar operators commute with all elements of a complex algebra. -/
theorem scalarOperator_commutes
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (ζ : ℂ)
    (Z : Value) :
    scalarOperator ζ * Z = Z * scalarOperator ζ := by
  exact Algebra.commutes ζ Z

/-- Scalar operators are phase-linear relative to every phase axis. -/
theorem scalarOperator_phaseLinear
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (K : Value)
    (ζ : ℂ) :
    PhaseLinearValue K (scalarOperator ζ) := by
  dsimp [PhaseLinearValue]
  exact scalarOperator_commutes ζ K

/-- If `Z` commutes with `K`, then `ζ•1 - Z` also commutes with `K`. -/
theorem operatorResolventDiff_phaseLinear
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    {K Z : Value}
    (ζ : ℂ)
    (hZ : PhaseLinearValue K Z) :
    PhaseLinearValue K (operatorResolventDiff ζ Z) := by
  dsimp [PhaseLinearValue, operatorResolventDiff]
  calc
    (scalarOperator ζ - Z) * K
        = scalarOperator ζ * K - Z * K := by
          rw [sub_mul]
    _ = K * scalarOperator ζ - K * Z := by
          rw [scalarOperator_commutes ζ K, hZ]
    _ = K * (scalarOperator ζ - Z) := by
          rw [mul_sub]

/--
If `B` is invertible with inverse `Binv`, and `X` commutes with `B`, then
`X` commutes with `Binv`.
-/
theorem inverse_commutes_of_commutes
    {Value : Type*} [Monoid Value]
    {X B Binv : Value}
    (h_right : B * Binv = 1)
    (h_left : Binv * B = 1)
    (hXB : X * B = B * X) :
    X * Binv = Binv * X := by
  calc
    X * Binv
        = 1 * (X * Binv) := by
          rw [one_mul]
    _ = (Binv * B) * (X * Binv) := by
          rw [h_left]
    _ = Binv * (B * X) * Binv := by
          simp only [mul_assoc]
    _ = Binv * (X * B) * Binv := by
          rw [hXB.symm]
    _ = (Binv * X) * (B * Binv) := by
          simp only [mul_assoc]
    _ = (Binv * X) * 1 := by
          rw [h_right]
    _ = Binv * X := by
          rw [mul_one]

/-- If a phase-linear element has a two-sided inverse, its inverse is phase-linear. -/
theorem inverse_phaseLinear_of_twoSided_inverse
    {Value : Type*} [Ring Value]
    {K B Binv : Value}
    (hB : PhaseLinearValue K B)
    (h_right : B * Binv = 1)
    (h_left : Binv * B = 1) :
    PhaseLinearValue K Binv := by
  dsimp [PhaseLinearValue] at hB ⊢
  have h :
      K * Binv = Binv * K :=
    inverse_commutes_of_commutes
      (X := K)
      (B := B)
      (Binv := Binv)
      h_right
      h_left
      hB.symm
  exact h.symm

/--
A supplied operator resolvent kernel.

This is the general noncommutative operator version of `(ζ•1 - Z)⁻¹`.

The inverse is not postulated as a vague law. It is carried by explicit
left/right inverse equations.
-/
structure SuppliedOperatorResolventKernel
    (Value : Type*) [Ring Value] [Algebra ℂ Value] where

  /-- Admissible spectral parameter/operator pairs. -/
  IsAdmissible :
    ℂ → Value → Prop

  /-- The supplied resolvent inverse. -/
  kernel :
    ℂ → Value → Value

  /-- Left inverse law. -/
  left_inverse :
    ∀ ζ Z,
      IsAdmissible ζ Z →
        operatorResolventDiff ζ Z * kernel ζ Z = 1

  /-- Right inverse law. -/
  right_inverse :
    ∀ ζ Z,
      IsAdmissible ζ Z →
        kernel ζ Z * operatorResolventDiff ζ Z = 1

namespace SuppliedOperatorResolventKernel

variable {Value : Type*} [Ring Value] [Algebra ℂ Value]
variable (R : SuppliedOperatorResolventKernel Value)

/-- Convert a supplied operator resolvent into a noncommutative Cauchy kernel. -/
def toCauchyKernel :
    NoncommutativeCauchyKernel ℂ Value Value where
  IsAdmissible := R.IsAdmissible
  diff := operatorResolventDiff
  kernel := R.kernel
  left_inverse := R.left_inverse
  right_inverse := R.right_inverse

/-- Difference times resolvent kernel is identity on admissible pairs. -/
theorem diff_mul_kernel
    (ζ : ℂ)
    (Z : Value)
    (h : R.IsAdmissible ζ Z) :
    operatorResolventDiff ζ Z * R.kernel ζ Z = 1 :=
  R.left_inverse ζ Z h

/-- Resolvent kernel times difference is identity on admissible pairs. -/
theorem kernel_mul_diff
    (ζ : ℂ)
    (Z : Value)
    (h : R.IsAdmissible ζ Z) :
    R.kernel ζ Z * operatorResolventDiff ζ Z = 1 :=
  R.right_inverse ζ Z h

/-- Uniqueness of the supplied operator resolvent kernel. -/
theorem kernel_unique
    (ζ : ℂ)
    (Z : Value)
    (h : R.IsAdmissible ζ Z)
    (U : Value)
    (h_left : operatorResolventDiff ζ Z * U = 1)
    (h_right : U * operatorResolventDiff ζ Z = 1) :
    U = R.kernel ζ Z :=
  NoncommutativeCauchyKernel.kernel_unique
    R.toCauchyKernel ζ Z h U h_left h_right

/--
If `Z` is phase-linear relative to `K`, then its supplied resolvent kernel is
also phase-linear.
-/
theorem kernel_phaseLinear_of_phaseLinear
    {K Z : Value}
    (ζ : ℂ)
    (h : R.IsAdmissible ζ Z)
    (hZ : PhaseLinearValue K Z) :
    PhaseLinearValue K (R.kernel ζ Z) := by
  have hdiff :
      PhaseLinearValue K (operatorResolventDiff ζ Z) :=
    operatorResolventDiff_phaseLinear ζ hZ
  exact
    inverse_phaseLinear_of_twoSided_inverse
      hdiff
      (R.left_inverse ζ Z h)
      (R.right_inverse ζ Z h)

end SuppliedOperatorResolventKernel

end BilingualAnalyticity
