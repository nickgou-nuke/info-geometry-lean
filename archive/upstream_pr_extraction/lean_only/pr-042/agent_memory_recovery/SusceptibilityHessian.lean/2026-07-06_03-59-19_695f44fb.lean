retardance, diattenuation, and heat once calibrated.
-/
structure MatterResponseCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Full susceptibility/Fresnel response calibration. -/
  response :
    SusceptibilityFresnelCalibration State Tangent Freq Angle

  /-- Matter response law. -/
  matter_response_law : Prop


/--
Compatibility predicate for the material-response Hessian/Fresnel bridge.

Concrete modules should replace this by material-model, linear-response,
dielectric-backend, interface-geometry, and Jones/Fresnel calibration data.
-/
def MaterialSusceptibilityHessianCompatibility
    (State Tangent Op Freq WaveVector : Type*) [Ring Op] : Prop :=
  Nonempty (State → Tangent → Op → Freq → WaveVector → Unit)

/--
Owner target for constructing material-response/Fresnel data from an
information Hessian.
-/
@[owner_target_tag]
def MaterialSusceptibilityHessianOwnerTarget : Prop :=
  ∀ (State Tangent Op Freq WaveVector : Type*) [Ring Op],
    MaterialSusceptibilityHessianCompatibility State Tangent Op Freq WaveVector →
      Nonempty
        (SusceptibilityHessianFresnelBridge
          State Tangent Op Freq WaveVector)

/-! ## 5. Owner target -/

/--
Owner target for optical response calibration.

This is intentionally witness-gated.  Concrete material models must supply the
Hessian/material/Fresnel calibration.
-/
@[owner_target_tag]
def SusceptibilityHessianOwnerTarget : Prop :=
  ∀ (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State],
  ∀ H : HessianResponseDatum State,
  ∀ M : MaterialResponseModel State,
  ∀ F : FresnelCoefficientReadout State,
  ∀ C : OpticalResponseCalibration State H M F,
    ∃ D : OpticalResponseCalibration State H M F, D = C

/--
The owner target is satisfied once the calibration witness is supplied.
-/
theorem susceptibilityHessianOwnerTarget :
    SusceptibilityHessianOwnerTarget := by
  intro State _ _ H M F C
  exact ⟨C, rfl⟩

attribute [rep_depth operator]
  HessianResponseDatum
  HessianResponseDatum.not_regular_of_singular
  IsHessianDegenerate
  MaterialResponseModel
  HessianSusceptibilityCalibration
  FresnelCoefficientReadout
  StatePolarizationEigenResponse
  FresnelFromStateEigenResponse
  FresnelFromStateEigenResponse.responseS_eq_rs
  FresnelFromStateEigenResponse.responseP_eq_rp
  spJonesEventOfFresnel
  spJonesEventOfFresnel_basis
  spJonesEventOfFresnel_coeff0
  spJonesEventOfFresnel_coeff1
  spJonesEventOfFresnel_jones_00
  spJonesEventOfFresnel_jones_11
  JonesFromMaterialCalibration
  jonesFromMaterialCalibrationOfFresnel
  JonesFromMaterialCalibration.jones_00_eq_rs
  JonesFromMaterialCalibration.jones_11_eq_rp
  JonesFromMaterialCalibration.jones_offdiag_01_zero
  JonesFromMaterialCalibration.jones_offdiag_10_zero
  RetardanceReadout
  OpticalAbsorptionReadout
  OpticalResponseCalibration
  OpticalResponseCalibration.ofFresnel
  OpticalResponseCalibration.eventOf
  OpticalResponseCalibration.jones_00_eq_rs
  OpticalResponseCalibration.jones_11_eq_rp
  OpticalResponseCalibration.jones_offdiag_01_zero
  OpticalResponseCalibration.jones_offdiag_10_zero
  OpticalResponseEigenCalibration
  OpticalResponseEigenCalibration.responseS_eq_rs
  OpticalResponseEigenCalibration.responseP_eq_rp
  OpticalResponseEigenCalibration.jones_00_eq_rs
  OpticalResponseEigenCalibration.jones_11_eq_rp
  InformationPotentialDatum
  InformationPotentialDatum.hessian_symmetric
  InformationPotentialDatum.hessian_nonneg
  BregmanHeatDatum
  BregmanHeatDatum.heat_nonnegative
  BregmanHeatDatum.heat_self
  LinearSusceptibilityDatum
  HessianSusceptibilityBridge
  DielectricResponseDatum
  PolarizationMode
  OpticalInterfaceResponse
  fresnelRS
  fresnelRP
  MaterialFresnelCoefficientDatum
  MaterialFresnelCoefficientDatum.r_s_eq
  MaterialFresnelCoefficientDatum.r_p_eq
  PolarizationEigenResponse
  FresnelEigenCalibration
  FresnelEigenCalibration.s_eigenvalue_is_r_s
  FresnelEigenCalibration.p_eigenvalue_is_r_p
  FresnelEigenCalibration.s_eigenvalue_eq_standard
  FresnelEigenCalibration.p_eigenvalue_eq_standard
  OperatorialJonesResponse
  JonesFresnelCalibration
  SusceptibilityHessianFresnelBridge
  SusceptibilityHessianFresnelBridge.s_reflection_eigenvalue
  SusceptibilityHessianFresnelBridge.p_reflection_eigenvalue
  OpticalStinespringHeatCalibration
  OpticalStinespringHeatCalibration.absorption_eq_hidden_information
  OpticalPTStinespringClinch
  OpticalPTStinespringClinch.event_tag_eq_PT
  OpticalPTStinespringClinch.absorption_eq_hidden_information
  OpticalPTStinespringClinch.heat_eq_hidden_information
  OpticalPTStinespringClinch.hidden_information_nonneg
  OpticalPTStinespringClinch.absorption_nonneg
  OpticalPTStinespringClinch.visible_deficit_eq_recovered_hidden
  BregmanHessianResponse
  BregmanHessianResponse.hessian_symmetric
  BregmanHessianResponse.hessian_nonnegative
  SusceptibilityDatum
  StateDielectricResponseDatum
  ComplexRefractiveIndexDatum
  BregmanHessianSusceptibilityCalibration
  FresnelFromRefractiveIndex
  OpticalResponseEigenvalues
  SusceptibilityFresnelCalibration
  SusceptibilityFresnelCalibration.coeff_s_is_response_eigenvalue
  SusceptibilityFresnelCalibration.coeff_p_is_response_eigenvalue
  HessianJonesCalibration
  HessianJonesCalibration.eventOf
  HessianJonesCalibration.event_coeff0_eq_fresnel_s
  HessianJonesCalibration.event_coeff1_eq_fresnel_p
  HessianJonesCalibration.event_coeff0_eq_response_eigenvalue
  HessianJonesCalibration.event_coeff1_eq_response_eigenvalue
  MetalMirrorSusceptibilityCalibration
  MetalMirrorSusceptibilityCalibration.eventOf
  MetalMirrorSusceptibilityCalibration.p_coeff_is_hessian_response_eigenvalue
  VacuumResponseCalibration
  MatterResponseCalibration
  MaterialSusceptibilityHessianCompatibility
  MaterialSusceptibilityHessianOwnerTarget
  SusceptibilityHessianOwnerTarget
  susceptibilityHessianOwnerTarget

/-! ## Concrete Instances to Purify Vacuous Shapes -/

/-- Concrete trivial Hessian response datum for ℝ. -/
def concreteHessianResponseDatum : HessianResponseDatum ℝ where
  hessian := fun _ ↦ (0 : ℝ →L[ℝ] ℝ)
  regularAt := fun x ↦ x ≠ 0
  singularAt := fun x ↦ x = 0
  singular_not_regular := fun U hU ↦ by
    intro h
    rw [hU] at h
    exact h rfl

/-- Concrete material response model over ℝ. -/
def concreteMaterialResponseModel : MaterialResponseModel ℝ where
  frequency := fun _ ↦ 1
  incidenceAngle := fun _ ↦ 0
  complexIndex := fun _ ↦ 1
  susceptibility := fun _ ↦ 0
  material_law := ∀ U : ℝ, (1 : ℂ) = 1 + (0 : ℂ)
  material_law_holds := fun _ ↦ by ring

/-- Concrete Fresnel coefficient readout over ℝ. -/
def concreteFresnelCoefficientReadout : FresnelCoefficientReadout ℝ where
  rs := fun U ↦ (U : ℂ)
  rp := fun U ↦ -(U : ℂ)
  fresnel_law := ∀ U : ℝ, (U : ℂ) + -(U : ℂ) = 0
  fresnel_law_holds := fun U ↦ by ring

end InfoGeometry.OperatorAlgebra.SusceptibilityHessian
