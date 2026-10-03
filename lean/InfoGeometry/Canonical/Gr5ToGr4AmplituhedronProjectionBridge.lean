import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordFiveBladeBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.Gr5ToGr4AmplituhedronProjectionBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.SplitCliffordFiveBladeBridge

variable {R V4 V5 : Type*} [CommRing R] [AddCommGroup V4] [Module R V4] [AddCommGroup V5] [Module R V5]

/-- The exterior-algebra map induced by `P` preserves the square-zero identity
    for this decomposable 5-vector.  The theorem makes no dimensional,
    split-signature, twistor, Plücker-quadric, or amplituhedron assertion. -/
theorem gr5_to_gr4_projection_nilpotent (P : V5 →ₗ[R] V4) (v1 v2 v3 v4 v5 : V5) :
    (map P (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) * (map P (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) = 0 :=
  native_plucker_five_blade_linear_map_conservation P v1 v2 v3 v4 v5

/-- Packages square-zero for a decomposable exterior 5-vector with the same
    identity after the induced exterior-algebra map.  These conclusions are
    valid for the stated modules and linear map; the theorem does not package
    a Grassmannian projection or an amplituhedron boundary embedding. -/
theorem master_gr5_to_gr4_amplituhedron_projection_synthesis
    (P : V5 →ₗ[R] V4) (v1 v2 v3 v4 v5 : V5) :
    ((ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) * (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) = 0) ∧
    ((map P (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) * (map P (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) = 0) := ⟨
  native_plucker_five_blade_nilpotent v1 v2 v3 v4 v5,
  gr5_to_gr4_projection_nilpotent P v1 v2 v3 v4 v5
⟩

end InfoGeometry.Canonical.Gr5ToGr4AmplituhedronProjectionBridge
