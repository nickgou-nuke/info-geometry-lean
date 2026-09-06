import InfoGeometry.SuperMetriplectic.Flow

/-!
# BPS Central Charge and Witten Index Packets

Conservative body-level packets for the supersymmetric thermodynamic layer.

This file keeps the BPS/Witten statements explicit:

* central charge data are represented by scalar readouts;
* BPS saturation is an assumption, not derived here;
* protected Onsager directions are represented by an explicit null response;
* the Witten index is represented by a temperature-invariant scalar readout.

The operatorial Fredholm/index owner remains the existing canonical central
charge surface; this file only provides the super-metriplectic interface.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Scalar BPS central-charge packet.

`massReadout = |centralCharge|` is the BPS saturation condition.  The protected
direction is encoded by `protectedOnsagerResponse = 0`, representing the
singular/null Onsager response in the BPS lane.
-/
structure BPSCentralChargePacket where
  massReadout : ℝ
  centralCharge : ℝ
  protectedForce : ℝ
  protectedOnsagerResponse : ℝ
  souriauHessianEntry : ℝ
  covarianceEntry : ℝ
  centralCocycleEntry : ℝ
  bps_saturation :
    massReadout = |centralCharge|
  hessian_eq_covariance_plus_central_cocycle :
    souriauHessianEntry = covarianceEntry + centralCocycleEntry
  protected_response_eq_zero :
    protectedOnsagerResponse = 0

namespace BPSCentralChargePacket

/-- Public BPS saturation equation `M = |Z|`. -/
theorem mass_eq_abs_centralCharge (B : BPSCentralChargePacket) :
    B.massReadout = |B.centralCharge| :=
  B.bps_saturation

/-- The central charge modifies the Souriau Hessian by a cocycle term. -/
theorem souriauHessianEntry_eq_covariance_plus_central_cocycle
    (B : BPSCentralChargePacket) :
    B.souriauHessianEntry = B.covarianceEntry + B.centralCocycleEntry :=
  B.hessian_eq_covariance_plus_central_cocycle

/-- BPS-protected Onsager response vanishes in the protected direction. -/
theorem protected_onsager_response_zero
    (B : BPSCentralChargePacket) :
    B.protectedOnsagerResponse = 0 :=
  B.protected_response_eq_zero

end BPSCentralChargePacket

/--
Witten-index thermodynamic packet.

`temperatureDerivative = 0` records temperature independence of the index.
`supportedOnBPS` records that the represented index readout is carried by the
BPS sector.  Both are explicit fields because this layer does not construct the
supertrace.
-/
structure WittenIndexThermoPacket where
  indexValue : ℝ
  inverseTemperature : ℝ
  centralPotential : ℝ
  temperatureDerivative : ℝ
  bpsSectorWeight : ℝ
  supportedOnBPS :
    indexValue = bpsSectorWeight
  temperatureDerivative_eq_zero :
    temperatureDerivative = 0

namespace WittenIndexThermoPacket

/-- The Witten-index readout is supported on the BPS sector in this packet. -/
theorem index_eq_bps_sector_weight
    (W : WittenIndexThermoPacket) :
    W.indexValue = W.bpsSectorWeight :=
  W.supportedOnBPS

/-- The Witten-index readout is temperature-invariant. -/
theorem temperature_derivative_zero
    (W : WittenIndexThermoPacket) :
    W.temperatureDerivative = 0 :=
  W.temperatureDerivative_eq_zero

end WittenIndexThermoPacket

/--
BPS/Witten super-metriplectic capstone packet.

It joins:

* a BPS central-charge Hessian modification;
* a Witten-index invariant;
* a metriplectic flow whose entropy production remains nonnegative.
-/
structure BPSSuperMetriplecticCapstone
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  flow : MetriplecticFlow V
  bps : BPSCentralChargePacket
  witten : WittenIndexThermoPacket
  protectedFlowReadout : ℝ
  protectedFlowReadout_eq_bps_response :
    protectedFlowReadout = bps.protectedOnsagerResponse

namespace BPSSuperMetriplecticCapstone

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The BPS-protected dissipative readout vanishes. -/
theorem protected_flow_readout_zero
    (C : BPSSuperMetriplecticCapstone V) :
    C.protectedFlowReadout = 0 := by
  rw [C.protectedFlowReadout_eq_bps_response]
  exact C.bps.protected_onsager_response_zero

/-- The Witten-index readout is temperature-invariant in the capstone packet. -/
theorem witten_temperature_derivative_zero
    (C : BPSSuperMetriplecticCapstone V) :
    C.witten.temperatureDerivative = 0 :=
  C.witten.temperature_derivative_zero

/-- The metriplectic entropy production remains nonnegative. -/
theorem entropyProduction_nonnegative
    (C : BPSSuperMetriplecticCapstone V) :
    0 ≤ C.flow.entropyProduction :=
  C.flow.entropyProduction_nonnegative

/-- Combined BPS/Witten/second-law capstone statement. -/
theorem bps_witten_capstone
    (C : BPSSuperMetriplecticCapstone V) :
    C.bps.massReadout = |C.bps.centralCharge|
      ∧ C.bps.souriauHessianEntry =
          C.bps.covarianceEntry + C.bps.centralCocycleEntry
      ∧ C.protectedFlowReadout = 0
      ∧ C.witten.temperatureDerivative = 0
      ∧ 0 ≤ C.flow.entropyProduction := by
  exact ⟨C.bps.mass_eq_abs_centralCharge,
    C.bps.souriauHessianEntry_eq_covariance_plus_central_cocycle,
    C.protected_flow_readout_zero,
    C.witten_temperature_derivative_zero,
    C.entropyProduction_nonnegative⟩

end BPSSuperMetriplecticCapstone

end InfoGeometry.SuperMetriplectic
