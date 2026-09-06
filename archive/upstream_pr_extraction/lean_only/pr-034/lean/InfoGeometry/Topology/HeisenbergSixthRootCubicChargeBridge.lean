import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

/-!
# Heisenberg sixth-root / cubic-charge bridge

This file packages the verified Heisenberg boundary atlas together with the
effective cube-root readout and the induced cubic Zorn action.  It records the
triple-shadow of the sixth-root parameter:

* the Heisenberg boundary packet;
* the effective cube root `q^2`;
* the order-three cyclotomic action on Zorn.

It does not identify the Heisenberg carrier with the Zorn carrier.
-/

namespace InfoGeometry.Topology.HeisenbergSixthRootCubicChargeBridge

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

abbrev Zorn := InfoGeometry.Canonical.ZornMatrix ℂ

instance zornCubicChargeTopologicalSpace :
    TopologicalSpace (Zorn →ₗ[ℂ] Zorn) := ⊥

instance zornCubicChargeDiscreteTopology :
    DiscreteTopology (Zorn →ₗ[ℂ] Zorn) := ⟨rfl⟩

/-- The combined Heisenberg boundary / sixth-root / cubic-charge packet. -/
noncomputable def heisenbergSixthRootCubicChargeReadout
    (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
      (ℂ × (Zorn →ₗ[ℂ] Zorn)) :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
    (effectiveCubeRoot q, sixthRootCubicCharge q))

@[simp] theorem heisenbergSixthRootCubicChargeReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  rfl

@[simp] theorem heisenbergSixthRootCubicChargeReadout_snd_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.1 =
      effectiveCubeRoot q := by
  rfl

@[simp] theorem heisenbergSixthRootCubicChargeReadout_snd_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2 =
      sixthRootCubicCharge q := by
  rfl

/-- The Heisenberg boundary component is independent of the sixth-root lane. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  rfl

/-- The effective cube root is genuinely cubic. -/
theorem heisenbergSixthRootCubicChargeReadout_root_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.1 ^ 3 = 1 := by
  simpa [heisenbergSixthRootCubicChargeReadout] using
    (effectiveCubeRoot_cube q)

/-- The cubic Zorn action has order three on the readout. -/
theorem heisenbergSixthRootCubicChargeReadout_charge_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2.comp
        ((heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2.comp
          (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2) =
      LinearMap.id := by
  simpa [heisenbergSixthRootCubicChargeReadout] using
    (sixthRootCubicChargeHomeomorph_cube q)

/-- The combined readout is continuous because the parameter space is discrete. -/
theorem continuous_heisenbergSixthRootCubicChargeReadout (α : 𝕜) :
    Continuous (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α) := by
  simpa [heisenbergSixthRootCubicChargeReadout] using
    (continuous_of_discreteTopology :
      Continuous (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α))

/-- The combined readout is locally constant on the discrete sixth-root lane. -/
theorem isLocallyConstant_heisenbergSixthRootCubicChargeReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α) := by
  simpa [heisenbergSixthRootCubicChargeReadout] using
    (IsLocallyConstant.of_discrete
      (f := heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α))

end
end InfoGeometry.Topology.HeisenbergSixthRootCubicChargeBridge
