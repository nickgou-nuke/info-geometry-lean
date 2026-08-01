import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.SplitCliffordFiveBladeBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.Gr5ToGr4AmplituhedronProjectionBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.SplitCliffordFiveBladeBridge

variable {R V4 V5 : Type*} [CommRing R] [AddCommGroup V4] [Module R V4] [AddCommGroup V5] [Module R V5]

/-- **Theorem**: Projection from 5D Split Kinematics to 4D Twistor Space Preserves Nilpotency.
    For any projection map P : V5 →ₗ[R] V4 and 5-blade K5 = v1 ∧ v2 ∧ v3 ∧ v4 ∧ v5 ∈ ⋀⁵ V5,
    the pushed forward 5-blade in ExteriorAlgebra R V4 satisfies (map P K5)² = 0. -/
theorem gr5_to_gr4_projection_nilpotent (P : V5 →ₗ[R] V4) (v1 v2 v3 v4 v5 : V5) :
    (map P (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) * (map P (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) = 0 :=
  native_plucker_five_blade_linear_map_conservation P v1 v2 v3 v4 v5

end InfoGeometry.Canonical.Gr5ToGr4AmplituhedronProjectionBridge
