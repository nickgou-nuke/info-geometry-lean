import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
import InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

/-!
# Heisenberg sixth-root / cubic monodromy bridge

This file packages the already verified Heisenberg boundary atlas with the
effective cube-root parameter and the Klein-bottle cubic monodromy readout.
It records the triple-shadow of the sixth-root lane:

* the Heisenberg boundary packet;
* the effective cube-root parameter `q^2`;
* the induced order-three colour monodromy.

It does not identify the Heisenberg carrier with the Klein-bottle colour fibre.
-/

namespace InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The cubic-root parameter induced by a sixth-root parameter. -/
def effectiveCubicRootParameter (q : SixthRootParameter) : CubicRootParameter :=
  ⟨effectiveCubeRoot q, effectiveCubeRoot_cube q⟩

/-- The combined Heisenberg boundary / cubic-root monodromy packet. -/
noncomputable def heisenbergSixthRootCubicMonodromyReadout
    (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
      (CubicRootParameter × ColourOperator) :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
    (effectiveCubicRootParameter q,
      cubicRootChargeReadout (effectiveCubicRootParameter q)))

@[simp] theorem heisenbergSixthRootCubicMonodromyReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  rfl

@[simp] theorem heisenbergSixthRootCubicMonodromyReadout_snd_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.1 =
      effectiveCubicRootParameter q := by
  rfl

@[simp] theorem heisenbergSixthRootCubicMonodromyReadout_snd_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2 =
      cubicRootChargeReadout (effectiveCubicRootParameter q) := by
  rfl

/-- The Heisenberg boundary component is independent of the six-root lane. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  rfl

/-- The effective cubic-root parameter is genuinely cubic. -/
theorem heisenbergSixthRootCubicMonodromyReadout_root_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.1.1 ^ 3 = 1 := by
  simpa [heisenbergSixthRootCubicMonodromyReadout, effectiveCubicRootParameter] using
    (effectiveCubeRoot_cube q)

/-- The cubic monodromy family has order three on the readout. -/
theorem heisenbergSixthRootCubicMonodromyReadout_charge_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
        ((heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
          (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2) =
      LinearMap.id := by
  simpa [heisenbergSixthRootCubicMonodromyReadout, effectiveCubicRootParameter] using
    (cubicRootChargeReadout_cube (effectiveCubicRootParameter q))

/-- The exchange conjugates the cubic charge to its square. -/
theorem heisenbergSixthRootCubicMonodromyReadout_exchange_conj
    (α : 𝕜) (q : SixthRootParameter) :
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
      (K := ℂ)).comp
        ((heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
          (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
            (K := ℂ))) =
      (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
        (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2 := by
  simpa [heisenbergSixthRootCubicMonodromyReadout, effectiveCubicRootParameter] using
    (chiralExchange_conj_cubicRootChargeReadout
      (q := effectiveCubicRootParameter q))

/-- The combined readout is continuous because the parameter space is discrete. -/
theorem continuous_heisenbergSixthRootCubicMonodromyReadout (α : 𝕜) :
    Continuous (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α) := by
  simpa [heisenbergSixthRootCubicMonodromyReadout] using
    (continuous_of_discreteTopology :
      Continuous (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α))

/-- The combined readout is locally constant on the discrete sixth-root lane. -/
theorem isLocallyConstant_heisenbergSixthRootCubicMonodromyReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α) := by
  simpa [heisenbergSixthRootCubicMonodromyReadout] using
    (IsLocallyConstant.of_discrete
      (f := heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α))

end

end InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge
