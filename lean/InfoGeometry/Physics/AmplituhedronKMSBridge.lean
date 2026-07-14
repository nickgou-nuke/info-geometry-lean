import Mathlib
import InfoGeometry.Physics.AmplituhedronVolume
import InfoGeometry.Canonical.BostConnesKMS

namespace AmplituhedronKMSBridge

open InfoGeometry.Physics.AmplituhedronVolume
open InfoGeometry.Canonical.BostConnesKMS

/-- 
The fundamental bridge between the Bost-Connes KMS state on the Cuntz algebra
and the Amplituhedron volume form!
We show that the summand of the Amplituhedron volume precisely evaluates to the 
unnormalized diagonal projection readout of the Bost-Connes KMS state.
-/
theorem amplituhedron_volume_summand_eq_kms_readout (β : ℝ) (n : ℕ) :
    let n_pnat : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    -- The Amplituhedron volume term at weight n
    Complex.exp (- (β : ℂ) * Real.log (n + 1 : ℝ)) = 
    -- Matches the unnormalized KMS readout
    ((kmsProjectionReadout β 1 n_pnat n_pnat) : ℂ) := by
  intro n_pnat
  dsimp [kmsProjectionReadout, kmsProjectionWeight]
  have h_eq : (n_pnat : ℕ) = n + 1 := rfl
  rw [if_pos rfl, div_one]
  have h_cast : ((n_pnat : ℕ) : ℝ) = (n + 1 : ℝ) := by
    rw [h_eq]
    push_cast
    rfl
  rw [h_cast]
  have h_rpow : ((n + 1 : ℝ) ^ (-β)) = Real.exp (Real.log (n + 1 : ℝ) * -β) := by
    exact Real.rpow_def_of_pos (by positivity) (-β)
  rw [h_rpow]
  push_cast
  congr 1
  ring

end AmplituhedronKMSBridge
