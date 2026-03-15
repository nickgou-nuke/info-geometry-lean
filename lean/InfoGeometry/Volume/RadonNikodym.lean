import InfoGeometry.Volume.LogPotential

/-!
# Radon-Nikodym Bridge

Formalizes the connection between abstract volume changes and the 
Radon-Nikodym derivative. This avoids vacuous existence statements by 
providing a constructive structure interface.
-/

namespace InfoGeometry.Volume.RadonNikodym

open InfoGeometry.Volume.Base
open InfoGeometry.Volume.LogPotential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
Structure expressing the bridge between an algebraic volume and a 
scalar Radon-Nikodym derivative.
-/
structure HasScalarRNBridge (A : Type*) [Monoid A] where
  vol : A →* ℝˣ
  rn  : A → ℝ
  rn_eq_logAbs_vol : ∀ a, rn a = Real.log |((vol a : ℝˣ) : ℝ)|

/--
Multiplicative chain rule for the scalar RN bridge.
If the bridge holds, the RN derivative of a composition is the sum of derivatives.
-/
theorem rn_chain_rule {A : Type*} [Group A] (B : HasScalarRNBridge A) (f g : A) :
    B.rn (f * g) = B.rn f + B.rn g := by
  rw [B.rn_eq_logAbs_vol, B.rn_eq_logAbs_vol, B.rn_eq_logAbs_vol]
  rw [B.vol.map_mul]
  rw [Units.val_mul, abs_mul, Real.log_mul]
  · exact abs_ne_zero.mpr (Units.ne_zero _)
  · exact abs_ne_zero.mpr (Units.ne_zero _)

end InfoGeometry.Volume.RadonNikodym
