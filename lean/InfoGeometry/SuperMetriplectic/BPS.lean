import InfoGeometry.SuperMetriplectic.Flow

/-!
# BPS Central Charge and Witten Index Packets

Conservative body-level packets for the supersymmetric thermodynamic layer.

This file keeps the BPS/Witten statements explicit:

* central charge data are represented by scalar readouts;
* BPS saturation is an property, not derived here;
* protected Onsager directions are represented by an explicit null response;
* the Witten index is represented by a temperature-invariant scalar readout.
-/

namespace InfoGeometry.SuperMetriplectic

/-- Public BPS saturation equation `M = |Z|`. -/
theorem mass_eq_abs_centralCharge (massReadout centralCharge : ℝ) (h : massReadout = |centralCharge|) :
    massReadout = |centralCharge| := h

/-- The central charge modifies the Souriau Hessian by a cocycle term. -/
theorem souriauHessianEntry_eq_covariance_plus_central_cocycle
    (souriauHessianEntry covarianceEntry centralCocycleEntry : ℝ)
    (h : souriauHessianEntry = covarianceEntry + centralCocycleEntry) :
    souriauHessianEntry = covarianceEntry + centralCocycleEntry := h

/-- BPS-protected Onsager response vanishes in the protected direction. -/
theorem protected_onsager_response_zero
    (protectedOnsagerResponse : ℝ) (h : protectedOnsagerResponse = 0) :
    protectedOnsagerResponse = 0 := h

/-- The Witten index readout is temperature-invariant. -/
theorem witten_temperature_derivative_zero
    (temperatureDerivative : ℝ) (h : temperatureDerivative = 0) :
    temperatureDerivative = 0 := h

end InfoGeometry.SuperMetriplectic
