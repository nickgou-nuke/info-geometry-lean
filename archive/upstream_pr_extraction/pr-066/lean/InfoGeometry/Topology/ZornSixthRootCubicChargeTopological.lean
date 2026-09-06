import Mathlib
import InfoGeometry.Canonical.ZornSixthRootCubicChargeBridge
import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological

/-!
# Topological sixth-root to cubic-charge bridge

The atlas parameter is a genuine sixth root of unity.  Squaring it gives the
effective cube root used by the native Zorn cyclotomic charge.  This owner
records the parameter readout and the resulting order-three Zorn homeomorph;
it does not identify the Heisenberg current carrier with Zorn.
-/

namespace InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological

noncomputable section

abbrev Zorn := ZornMatrix ℂ

/-- Effective cube root associated with a sixth-root parameter. -/
def effectiveCubeRoot (q : SixthRootParameter) : ℂ :=
  (q.1 : ℂ) ^ 2

theorem effectiveCubeRoot_cube (q : SixthRootParameter) :
    effectiveCubeRoot q ^ 3 = 1 := by
  exact zornSixthRoot_effectiveCubeRoot q.1 q.2

/-- The effective root readout is continuous on the discrete parameter set. -/
theorem continuous_effectiveCubeRoot :
    Continuous effectiveCubeRoot := by
  simpa [effectiveCubeRoot] using
    (continuous_of_discreteTopology : Continuous effectiveCubeRoot)

/-- The effective root readout is locally constant. -/
theorem isLocallyConstant_effectiveCubeRoot :
    IsLocallyConstant effectiveCubeRoot := by
  simpa [effectiveCubeRoot] using
    (IsLocallyConstant.of_discrete (f := effectiveCubeRoot))

/-- Order-three cyclotomic Zorn action associated with a sixth root. -/
def sixthRootCubicCharge (q : SixthRootParameter) : Zorn →ₗ[ℂ] Zorn :=
  cubicCharge (effectiveCubeRoot q)

/-- The order-three action, equipped with its topological inverse. -/
noncomputable def sixthRootCubicChargeHomeomorph
    (q : SixthRootParameter) : Zorn ≃ₜ Zorn :=
  cubicChargeHomeomorph (effectiveCubeRoot q) (effectiveCubeRoot_cube q)

@[simp] theorem sixthRootCubicChargeHomeomorph_apply
    (q : SixthRootParameter) (Z : Zorn) :
    sixthRootCubicChargeHomeomorph q Z =
      sixthRootCubicCharge q Z := by
  rfl

theorem sixthRootCubicChargeHomeomorph_cube
    (q : SixthRootParameter) :
    (sixthRootCubicCharge q).comp
          ((sixthRootCubicCharge q).comp (sixthRootCubicCharge q)) =
      LinearMap.id := by
  simpa [sixthRootCubicCharge] using
    cubicCharge_pow_three (effectiveCubeRoot q) (effectiveCubeRoot_cube q)

end
end InfoGeometry.Topology.ZornSixthRootCubicChargeTopological
