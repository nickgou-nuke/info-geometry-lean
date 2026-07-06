    intro U
    rfl

namespace JonesFromMaterialCalibration

variable {State : Type*}
variable {M : MaterialResponseModel State}
variable {F : FresnelCoefficientReadout State}
variable (C : JonesFromMaterialCalibration State M F)

/--
The calibrated Jones matrix has `r_s` in the first diagonal channel.
-/
theorem jones_00_eq_rs
    (U : State) :
    (C.eventOf U).jones 0 0 = F.rs U := by sorry
/--
The calibrated Jones matrix has `r_p` in the second diagonal channel.
-/
theorem jones_11_eq_rp
    (U : State) :
    (C.eventOf U).jones 1 1 = F.rp U := by sorry
/--
The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis.
-/
theorem jones_offdiag_01_zero
    (U : State) :
    (C.eventOf U).jones 0 1 = 0 := by sorry
/--
The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis.
-/
theorem jones_offdiag_10_zero
    (U : State) :
    (C.eventOf U).jones 1 0 = 0 := by sorry
end JonesFromMaterialCalibration

/-! ## 4. Retardance and absorption readouts -/

/--
Retardance/ellipticity readout from Jones coefficients.