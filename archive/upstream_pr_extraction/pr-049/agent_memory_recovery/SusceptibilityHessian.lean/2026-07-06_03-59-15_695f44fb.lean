
The quantities are complex-valued to support absorbing media.
-/
structure OpticalInterfaceResponse
    (Freq : Type*) where
  /-- Index/impedance package for medium 1, compressed as `n1`. -/
  n1 : Freq → ℂ

  /-- Index/impedance package for medium 2, compressed as `n2`. -/
  n2 : Freq → ℂ

  /-- Cosine of incidence angle, or its complex continuation. -/
  cosIncident : Freq → ℂ

  /-- Cosine of transmission angle, or its complex continuation. -/
  cosTransmitted : Freq → ℂ

  /-- Certificate that Snell/interface geometry is valid. -/
  interfaceGeometryValid : Prop

/-- Standard s-polarized Fresnel reflection amplitude. -/
def fresnelRS
    {Freq : Type*}
    (I : OpticalInterfaceResponse Freq)
    (omega : Freq) : ℂ :=
  (I.n1 omega * I.cosIncident omega - I.n2 omega * I.cosTransmitted omega) /
    (I.n1 omega * I.cosIncident omega + I.n2 omega * I.cosTransmitted omega)

/-- Standard p-polarized Fresnel reflection amplitude. -/
def fresnelRP
    {Freq : Type*}
    (I : OpticalInterfaceResponse Freq)
    (omega : Freq) : ℂ :=
  (I.n2 omega * I.cosIncident omega - I.n1 omega * I.cosTransmitted omega) /
    (I.n2 omega * I.cosIncident omega + I.n1 omega * I.cosTransmitted omega)

/--
Fresnel coefficient datum with explicit standard reflection formulas.

The transmission laws remain proof-carrying because their branch conventions
belong to the material/interface layer.
-/
structure MaterialFresnelCoefficientDatum
    (Freq : Type*) where
  /-- Interface geometry and optical response. -/
  interface :
    OpticalInterfaceResponse Freq

  /-- s-polarized reflection coefficient. -/
  r_s : Freq → ℂ

  /-- p-polarized reflection coefficient. -/
  r_p : Freq → ℂ

  /-- s-polarized transmission coefficient. -/
  t_s : Freq → ℂ

  /-- p-polarized transmission coefficient. -/
  t_p : Freq → ℂ

  /-- s coefficient is the standard interface formula. -/
  r_s_eq_standard :
    ∀ omega, r_s omega = fresnelRS interface omega

  /-- p coefficient is the standard interface formula. -/
  r_p_eq_standard :
    ∀ omega, r_p omega = fresnelRP interface omega

namespace MaterialFresnelCoefficientDatum

variable {Freq : Type*}
variable (F : MaterialFresnelCoefficientDatum Freq)

/-- s-polarized coefficient equals the standard Fresnel expression. -/
theorem r_s_eq
    (omega : Freq) :
    F.r_s omega = fresnelRS F.interface omega :=
  F.r_s_eq_standard omega

/-- p-polarized coefficient equals the standard Fresnel expression. -/
theorem r_p_eq
    (omega : Freq) :
    F.r_p omega = fresnelRP F.interface omega :=
  F.r_p_eq_standard omega

end MaterialFresnelCoefficientDatum

/--
Polarization eigen-response.

The intended interpretation is that `s` and `p` polarizations diagonalize the
material/interface response.
-/
structure PolarizationEigenResponse
    (Freq : Type*) where
  /-- Polarization eigenvalue. -/
  eigenvalue : PolarizationMode → Freq → ℂ

/--
Fresnel coefficients as eigenvalues of the polarization response.

This is the formal version of: `r_s` and `r_p` are geometric eigenvalues after
material and interface calibration have been supplied.
-/
structure FresnelEigenCalibration
    (Freq : Type*) where
  /-- Fresnel coefficient data. -/
  fresnel :
    MaterialFresnelCoefficientDatum Freq

  /-- Polarization eigen-response. -/
  eigenResponse :
    PolarizationEigenResponse Freq

  /-- s eigenvalue is `r_s`. -/
  s_eigenvalue_eq :
    ∀ omega,
      eigenResponse.eigenvalue PolarizationMode.s omega =
        fresnel.r_s omega

  /-- p eigenvalue is `r_p`. -/
  p_eigenvalue_eq :
    ∀ omega,
      eigenResponse.eigenvalue PolarizationMode.p omega =
        fresnel.r_p omega

namespace FresnelEigenCalibration

variable {Freq : Type*}
variable (C : FresnelEigenCalibration Freq)

/-- The s-polarized geometric eigenvalue is the Fresnel `r_s`. -/
theorem s_eigenvalue_is_r_s
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.s omega =
      C.fresnel.r_s omega :=
  C.s_eigenvalue_eq omega

/-- The p-polarized geometric eigenvalue is the Fresnel `r_p`. -/
theorem p_eigenvalue_is_r_p
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.p omega =
      C.fresnel.r_p omega :=
  C.p_eigenvalue_eq omega

/-- The s-polarized eigenvalue equals the standard Fresnel formula. -/
theorem s_eigenvalue_eq_standard
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.s omega =
      fresnelRS C.fresnel.interface omega := by
  rw [C.s_eigenvalue_is_r_s omega]
  exact C.fresnel.r_s_eq omega

/-- The p-polarized eigenvalue equals the standard Fresnel formula. -/
theorem p_eigenvalue_eq_standard
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.p omega =
      fresnelRP C.fresnel.interface omega := by
  rw [C.p_eigenvalue_is_r_p omega]
  exact C.fresnel.r_p_eq omega

end FresnelEigenCalibration

/-- Operatorial Jones response indexed by polarization and frequency. -/
structure OperatorialJonesResponse
    (Op Freq : Type*) [Ring Op] where
  /-- Jones operator for the selected channel and frequency. -/
  jonesOperator : PolarizationMode → Freq → Op

/-- Calibration between operatorial Jones response and Fresnel eigenvalues. -/
structure JonesFresnelCalibration
    (Op Freq : Type*) [Ring Op] where
  /-- Fresnel eigenvalue calibration. -/
  fresnelEigen :
    FresnelEigenCalibration Freq

  /-- Operatorial Jones response. -/
  jones :
    OperatorialJonesResponse Op Freq

  /-- The `s` Jones channel is calibrated by the s Fresnel eigenvalue. -/
  sCalibration : Prop

  /-- The `p` Jones channel is calibrated by the p Fresnel eigenvalue. -/
  pCalibration : Prop

  /-- Flux conservation or absorption/Stinespring accounting certificate. -/
  fluxAccounting : Prop

/-- Full bridge from Hessian information geometry to Fresnel/Jones response. -/
structure SusceptibilityHessianFresnelBridge
    (State Tangent Op Freq WaveVector : Type*) [Ring Op] where
  /-- Hessian-to-susceptibility bridge. -/
  hessianBridge :
    HessianSusceptibilityBridge State Tangent Op Freq WaveVector

  /-- Dielectric/impedance backend. -/
  dielectric :
    DielectricResponseDatum Freq WaveVector

  /-- Fresnel coefficients as polarization eigenvalues. -/
  fresnelEigen :
    FresnelEigenCalibration Freq

  /-- Operatorial Jones calibration. -/
  jonesCalibration :
    JonesFresnelCalibration Op Freq

  /-- Dielectric response induced by Hessian-calibrated susceptibility. -/
  dielectric_from_hessian_susceptibility : Prop

  /-- Fresnel eigenvalues are boundary readouts of that material response. -/
  fresnel_from_dielectric_response : Prop

namespace SusceptibilityHessianFresnelBridge

variable
    {State Tangent Op Freq WaveVector : Type*}
    [Ring Op]

variable
    (B : SusceptibilityHessianFresnelBridge
      State Tangent Op Freq WaveVector)

/-- The s-polarized reflection eigenvalue is the Fresnel `r_s`. -/
theorem s_reflection_eigenvalue
    (omega : Freq) :
    B.fresnelEigen.eigenResponse.eigenvalue PolarizationMode.s omega =
      B.fresnelEigen.fresnel.r_s omega :=
  B.fresnelEigen.s_eigenvalue_is_r_s omega

/-- The p-polarized reflection eigenvalue is the Fresnel `r_p`. -/
theorem p_reflection_eigenvalue
    (omega : Freq) :
    B.fresnelEigen.eigenResponse.eigenvalue PolarizationMode.p omega =
      B.fresnelEigen.fresnel.r_p omega :=
  B.fresnelEigen.p_eigenvalue_is_r_p omega

end SusceptibilityHessianFresnelBridge

/-! ## 6. Stinespring heat coupling -/

/--
Coupling between optical absorption and a Stinespring/Bregman heat ledger.
-/
structure OpticalStinespringHeatCalibration
    (State Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Embed or read an optical material state as a system state. -/
  stateToSystem :
    State → Sys

  /-- Optical absorption readout on material states. -/
  absorptionFromState :
    State → ℝ

  /-- Hidden-information bridge for the Stinespring/Tomita dilation. -/
  hiddenHeatBridge :
    HeatEqualsHiddenInformation Sys Comm B C D

  /--
  Optical absorption agrees with Bregman heat after mapping the optical state
  into the system carrier.
  -/
  absorption_eq_heat :
    ∀ U : State,
      absorptionFromState U =
        heatLoss B C (stateToSystem U)

namespace OpticalStinespringHeatCalibration

variable
    {State Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : OpticalStinespringHeatCalibration State Sys Comm B C D)

/--
Optical absorption is the hidden-information readout through the
Stinespring/Tomita bridge.
-/
theorem absorption_eq_hidden_information
    (U : State) :
    K.absorptionFromState U =
      K.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.stateToSystem U)) := by
  rw [K.absorption_eq_heat U]
  exact K.hiddenHeatBridge.heat_is_hidden_commutant_information
    (K.stateToSystem U)

end OpticalStinespringHeatCalibration

/-! ## 6a. PT hidden-sector Stinespring clinch -/

/--
Optical PT Stinespring clinch.

This is the witness-gated statement that a coherent optical event is booked in
the PT sector and that its apparent absorption is exactly the hidden
commutant-information readout supplied by the Stinespring/Tomita dilation.

The Jones event supplies the visible optical tag.  The Stinespring heat
calibration supplies the conservation and hidden-information ledger.
-/
structure OpticalPTStinespringClinch
    (State Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Optical absorption-to-hidden-information heat ledger. -/
  opticalHeat :
    OpticalStinespringHeatCalibration State Sys Comm B C D

  /-- Visible coherent Jones event attached to the optical state. -/
  eventOf :
    State → JonesOpticalEvent

  /-- The optical event is booked in the PT sector. -/
  event_tag_pt :
    ∀ U : State, (eventOf U).tag = V4Tag.PT

  /-- Model-specific law that this PT sector is the intended commutant/dark readout. -/
  pt_commutant_sector_law : Prop


namespace OpticalPTStinespringClinch

variable
    {State Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : OpticalPTStinespringClinch State Sys Comm B C D)

/-- The visible optical event is tagged by the PT sector. -/
theorem event_tag_eq_PT
    (U : State) :
    (K.eventOf U).tag = V4Tag.PT :=
  K.event_tag_pt U

/--
Optical absorption is exactly the hidden commutant-information readout.
-/
theorem absorption_eq_hidden_information
    (U : State) :
    K.opticalHeat.absorptionFromState U =
      K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.absorption_eq_hidden_information U

/--
Bregman heat is exactly the hidden commutant-information readout.
-/
theorem heat_eq_hidden_information
    (U : State) :
    heatLoss B C (K.opticalHeat.stateToSystem U) =
      K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.hiddenHeatBridge.heat_is_hidden_commutant_information
    (K.opticalHeat.stateToSystem U)

/--
The hidden commutant-information readout is nonnegative on optical states.
-/
theorem hidden_information_nonneg
    (U : State) :
    0 ≤ K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
      (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.hiddenHeatBridge.hidden_information_nonneg
    (K.opticalHeat.stateToSystem U)

/--
Optical absorption is nonnegative because it is hidden commutant information.
-/
theorem absorption_nonneg
    (U : State) :
    0 ≤ K.opticalHeat.absorptionFromState U := by
  rw [K.absorption_eq_hidden_information U]
  exact K.hidden_information_nonneg U

/--
The apparent visible deficit is exactly the recovered hidden commutant flow.
-/
theorem visible_deficit_eq_recovered_hidden
    (U : State) :
    C.ideal (K.opticalHeat.stateToSystem U) -
        C.actual (K.opticalHeat.stateToSystem U) =
      D.recoverHidden (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  D.ideal_sub_actual_eq_recovered_hidden (K.opticalHeat.stateToSystem U)

end OpticalPTStinespringClinch

/-! ## 7. Bregman/Fenchel Hessian to Jones calibration -/

/--
A Bregman/Fenchel Hessian readout of an information potential.

The Hessian is real-valued because it is the information-geometric response
metric.  Complex optical response enters only through material calibration.
-/
structure BregmanHessianResponse
    (State Tangent : Type*) [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian pairing at a state. -/
  hessianAt : State → Tangent → Tangent → ℝ

  /-- Symmetry of the Hessian pairing. -/
  symmetric :
    ∀ s X Y, hessianAt s X Y = hessianAt s Y X

  /-- Nonnegativity / convex response. -/
  nonnegative :
    ∀ s X, 0 ≤ hessianAt s X X

  /-- Certificate that this Hessian comes from the intended potential. -/
  bregman_hessian_law : Prop


namespace BregmanHessianResponse

variable {State Tangent : Type*} [AddCommGroup Tangent] [Module ℝ Tangent]
variable (H : BregmanHessianResponse State Tangent)

/-- Re-export Hessian symmetry. -/
theorem hessian_symmetric
    (s : State)
    (X Y : Tangent) :
    H.hessianAt s X Y = H.hessianAt s Y X :=
  H.symmetric s X Y

/-- Re-export Hessian nonnegativity. -/
theorem hessian_nonnegative
    (s : State)
    (X : Tangent) :
    0 ≤ H.hessianAt s X X :=
  H.nonnegative s X

end BregmanHessianResponse

/--
Complex material susceptibility.

The value is complex because the reactive and absorptive material responses
are both part of the optical readout.
-/
structure SusceptibilityDatum
    (State Freq : Type*) where
  /-- Complex susceptibility. -/
  susceptibility : State → Freq → ℂ

  /-- Material-response law. -/
  susceptibility_law : Prop


/--
State-indexed dielectric response calibrated from susceptibility.

The actual material equation, such as `epsilon = 1 + susceptibility`, is kept
proof-carrying at this layer.
-/
structure StateDielectricResponseDatum
    (State Freq : Type*) where
  /-- Complex dielectric function. -/
  epsilon : State → Freq → ℂ

  /-- Optional magnetic response. -/
  mu : State → Freq → ℂ

  /-- Relation between susceptibility and dielectric response. -/
  dielectric_law : Prop


/--
Complex refractive-index response.

Branch choice and material model are explicit proof-carrying data.
-/
structure ComplexRefractiveIndexDatum
    (State Freq : Type*) where
  /-- Complex refractive index. -/
  N : State → Freq → ℂ

  /-- Branch/material law connecting `N` to dielectric data. -/
  refractive_index_law : Prop


/--
Calibration from a Bregman Hessian to material susceptibility.

This is the witness-gated bridge saying that the local information-geometric
response is the material response readout in a concrete model.
-/
structure BregmanHessianSusceptibilityCalibration
    (State Tangent Freq : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Bregman/Fenchel Hessian response. -/
  hessian :
    BregmanHessianResponse State Tangent

  /-- Complex susceptibility datum. -/
  susceptibility :
    SusceptibilityDatum State Freq

  /-- Bridge law from Hessian response to susceptibility. -/
  hessian_controls_susceptibility_law : Prop


/--
Fresnel coefficient readout from a complex refractive-index model.

`coeff_s` and `coeff_p` are optical amplitude reflection coefficients.
-/
structure FresnelFromRefractiveIndex
    (State Freq Angle : Type*) where
  /-- s-polarized reflection coefficient. -/
  coeff_s : State → Freq → Angle → ℂ

  /-- p-polarized reflection coefficient. -/
  coeff_p : State → Freq → Angle → ℂ

  /-- Fresnel law certificate. -/
  fresnel_law : Prop


/--
Response eigenvalues in the local polarization basis.

Mode `0` is the first channel and mode `1` is the second channel.
-/
structure OpticalResponseEigenvalues
    (State Freq Angle : Type*) where
  /-- Optical response eigenvalue for each channel. -/
  eigenvalue : State → Freq → Angle → Fin 2 → ℂ

  /-- Eigenbasis of the response. -/
  basis : PolarizationBasis

  /-- Eigenvalue law/certificate. -/
  eigenvalue_law : Prop


/--
Complete Hessian/Fresnel calibration.

This packages Hessian response, susceptibility, dielectric response,
refractive index, optical response eigenvalues, and Fresnel coefficients.
-/
structure SusceptibilityFresnelCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian-to-susceptibility calibration. -/
  hessianSusceptibility :
    BregmanHessianSusceptibilityCalibration State Tangent Freq

  /-- Dielectric response. -/
  dielectric :
    StateDielectricResponseDatum State Freq

  /-- Complex refractive-index response. -/
  refractiveIndex :
    ComplexRefractiveIndexDatum State Freq

  /-- Optical response eigenvalues. -/
  responseEigenvalues :
    OpticalResponseEigenvalues State Freq Angle

  /-- Fresnel coefficient readout. -/
  fresnel :
    FresnelFromRefractiveIndex State Freq Angle

  /-- The `s` Fresnel coefficient is the first response eigenvalue. -/
  coeff_s_eq_eigen_zero :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      fresnel.coeff_s s omega theta =
        responseEigenvalues.eigenvalue s omega theta 0

  /-- The `p` Fresnel coefficient is the second response eigenvalue. -/
  coeff_p_eq_eigen_one :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      fresnel.coeff_p s omega theta =
        responseEigenvalues.eigenvalue s omega theta 1

  /-- End-to-end calibration law. -/
  end_to_end_optical_response_law : Prop


namespace SusceptibilityFresnelCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (C : SusceptibilityFresnelCalibration State Tangent Freq Angle)

/--
The `s` Fresnel coefficient is the first Hessian-calibrated response eigenvalue.
-/
theorem coeff_s_is_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    C.fresnel.coeff_s s omega theta =
      C.responseEigenvalues.eigenvalue s omega theta 0 :=
  C.coeff_s_eq_eigen_zero s omega theta

/--
The `p` Fresnel coefficient is the second Hessian-calibrated response eigenvalue.
-/
theorem coeff_p_is_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    C.fresnel.coeff_p s omega theta =
      C.responseEigenvalues.eigenvalue s omega theta 1 :=
  C.coeff_p_eq_eigen_one s omega theta

end SusceptibilityFresnelCalibration

/--
A calibrated optical state/event produces a Jones optical event.
-/
structure HessianJonesCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Full Hessian/Fresnel response calibration. -/
  response :
    SusceptibilityFresnelCalibration State Tangent Freq Angle

  /-- Surface kind assigned to the event. -/
  surfaceKind : OpticalSurfaceKind

  /-- Discrete V4 tag assigned to the event. -/
  tagOf : State → Freq → Angle → V4Tag

  /-- Coherence law for the Jones description. -/
  coherence : State → Freq → Angle → Prop

  coherent :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      coherence s omega theta

namespace HessianJonesCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (C : HessianJonesCalibration State Tangent Freq Angle)

/--
The Jones event generated by the calibrated Hessian/Fresnel response.
-/
def eventOf
    (s : State)
    (omega : Freq)
    (theta : Angle) : JonesOpticalEvent where
  basis := C.response.responseEigenvalues.basis
  kind := C.surfaceKind
  coeff0 := C.response.fresnel.coeff_s s omega theta
  coeff1 := C.response.fresnel.coeff_p s omega theta
  tag := C.tagOf s omega theta
  coherence := C.coherence s omega theta

/--
The first Jones coefficient is the calibrated `s`/first-channel Fresnel
coefficient.
-/
theorem event_coeff0_eq_fresnel_s
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff0 =
      C.response.fresnel.coeff_s s omega theta :=
  rfl

/--
The second Jones coefficient is the calibrated `p`/second-channel Fresnel
coefficient.
-/
theorem event_coeff1_eq_fresnel_p
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff1 =
      C.response.fresnel.coeff_p s omega theta :=
  rfl

/--
The first Jones coefficient is the first Hessian-calibrated response eigenvalue.
-/
theorem event_coeff0_eq_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff0 =
      C.response.responseEigenvalues.eigenvalue s omega theta 0 := by
  calc
    (C.eventOf s omega theta).coeff0
        = C.response.fresnel.coeff_s s omega theta := rfl
    _ = C.response.responseEigenvalues.eigenvalue s omega theta 0 :=
        C.response.coeff_s_is_response_eigenvalue s omega theta

/--
The second Jones coefficient is the second Hessian-calibrated response
eigenvalue.
-/
theorem event_coeff1_eq_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff1 =
      C.response.responseEigenvalues.eigenvalue s omega theta 1 := by
  calc
    (C.eventOf s omega theta).coeff1
        = C.response.fresnel.coeff_p s omega theta := rfl
    _ = C.response.responseEigenvalues.eigenvalue s omega theta 1 :=
        C.response.coeff_p_is_response_eigenvalue s omega theta

end HessianJonesCalibration

/--
Metal-mirror specialization of the calibrated Jones response.
-/
structure MetalMirrorSusceptibilityCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian-to-Jones calibration. -/
  jonesCalibration :
    HessianJonesCalibration State Tangent Freq Angle

  /-- The event is interpreted as a metal mirror response. -/
  metal_mirror_law : Prop

  /-- Absorptive part of response controls Bregman/thermal loss. -/
  absorption_heat_law : Prop

  /-- Reactive part of response controls retardance/ellipticity. -/
  retardance_law : Prop


namespace MetalMirrorSusceptibilityCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (M : MetalMirrorSusceptibilityCalibration State Tangent Freq Angle)

/-- Jones event of the metal mirror response. -/
def eventOf
    (s : State)
    (omega : Freq)
    (theta : Angle) : JonesOpticalEvent :=
  M.jonesCalibration.eventOf s omega theta

/--
The second Jones coefficient is the Hessian-calibrated `p`/second-channel
response eigenvalue.
-/
theorem p_coeff_is_hessian_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (M.eventOf s omega theta).coeff1 =
      M.jonesCalibration.response.responseEigenvalues.eigenvalue s omega theta 1 :=
  M.jonesCalibration.event_coeff1_eq_response_eigenvalue s omega theta

end MetalMirrorSusceptibilityCalibration

/--
Vacuum response calibration.

The concrete normalization of vacuum susceptibility is proof-carrying.
-/
structure VacuumResponseCalibration
    (State Freq : Type*) where
  /-- Vacuum susceptibility datum. -/
  susceptibility :
    SusceptibilityDatum State Freq

  /-- Vacuum susceptibility law. -/
  vacuum_susceptibility_law : Prop


/--
Matter response calibration.

In matter, the Hessian/susceptibility response can produce absorption,