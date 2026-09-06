import InfoGeometry.Canonical.DeterminantCore
import InfoGeometry.Canonical.LogGenerator
import InfoGeometry.Volume.Base
import InfoGeometry.Volume.LogPotential

/-!
# InfoGeometry.Canonical.Determinant

Canonical determinant/group surface for linear equivalences.
-/

namespace InfoGeometry.Canonical.Determinant

open InfoGeometry.Canonical
open InfoGeometry.Volume.Base
open InfoGeometry.Volume.LogPotential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
Exact multiplicative-to-additive bridge for determinant/volume change on linear
automorphisms.
-/
noncomputable def linearEquivExactBridge :
    ExactMultiplicativeToAdditiveBridge (V ≃ₗ[ℝ] V) ℝˣ ℝ where
  toExactAbelianizingBridge := ⟨VolumeHom⟩
  toAdditiveLinearization := logAbsUnitsLinearization

/-- High-level logarithmic generator induced by determinant/volume change. -/
noncomputable def linearEquivLogGenerator : LogGenerator (V ≃ₗ[ℝ] V) ℝ :=
  (ExactDescentLogGenerator.ofBridge linearEquivExactBridge).toLogGenerator

/-- The determinant log-generator is exactly the canonical log-volume potential. -/
@[simp] theorem linearEquivLogGenerator_eq_logAbsVolume (g : V ≃ₗ[ℝ] V) :
    linearEquivLogGenerator.logGen g = LogAbsVolume g := rfl

/-- Determinant/log-volume obeys the additive law upstairs on automorphisms. -/
theorem linearEquivLogGenerator_mul (f g : V ≃ₗ[ℝ] V) :
    linearEquivLogGenerator.logGen (f * g) =
      linearEquivLogGenerator.logGen f + linearEquivLogGenerator.logGen g :=
  ExactDescentLogGenerator.map_mul (ExactDescentLogGenerator.ofBridge linearEquivExactBridge) f g

end InfoGeometry.Canonical.Determinant
