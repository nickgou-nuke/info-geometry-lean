import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

/-!
# Heisenberg / Klein-bottle cyclotomic bridge

This file packages two already verified topological readouts:

* the Heisenberg boundary atlas together with its sixth-root parameter;
* the Klein-bottle chiral lift with its cubic charge and exchange.

The bridge only records a product readout and the induced cube-root / reflection
relations. It does not identify the Heisenberg carrier with the Klein-bottle
colour fibre.
-/

namespace InfoGeometry.Topology.HeisenbergKleinBottleCyclotomicBridge

open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.KleinBottleCyclotomicChiralLift
open InfoGeometry.Canonical

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance a2ColourEndomorphismTopologicalSpace :
    TopologicalSpace
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) := ⊥

instance a2ColourEndomorphismDiscreteTopology :
    DiscreteTopology
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) := ⟨rfl⟩

/-- The combined Heisenberg boundary / Klein-bottle cyclotomic packet. -/
noncomputable def heisenbergKleinCyclotomicReadout (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) ×
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge
      ((q.1 : ℂ) ^ 2),
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
        (K := ℂ)))

@[simp] theorem heisenbergKleinCyclotomicReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  rfl

@[simp] theorem heisenbergKleinCyclotomicReadout_snd_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1 =
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge
        ((q.1 : ℂ) ^ 2) := by
  rfl

@[simp] theorem heisenbergKleinCyclotomicReadout_snd_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2 =
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
        (K := ℂ) := by
  rfl

/-- The Heisenberg boundary component is independent of the Klein-bottle lift. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  rfl

/-- The Klein-bottle cube charge induced by a sixth-root parameter is cubic. -/
theorem heisenbergKleinCyclotomicReadout_charge_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
        ((heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
          (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1) =
      LinearMap.id := by
  have hq : ((q.1 : ℂ) ^ 2) ^ 3 = 1 := by
    calc
      ((q.1 : ℂ) ^ 2) ^ 3 = (q.1 : ℂ) ^ 6 := by ring
      _ = 1 := by
        simpa using q.2
  simpa [heisenbergKleinCyclotomicReadout] using
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge_cube
      (K := ℂ) ((q.1 : ℂ) ^ 2) hq)

/-- The Klein-bottle exchange remains involutive on the combined packet. -/
theorem heisenbergKleinCyclotomicReadout_exchange_square
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2.comp
        (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2 =
      LinearMap.id := by
  simpa [heisenbergKleinCyclotomicReadout] using
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange_square
      (K := ℂ))

/-- The exchange conjugates the cubic charge to its square. -/
theorem heisenbergKleinCyclotomicReadout_exchange_conj
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2.comp
        ((heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
          (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2) =
      (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
        (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1 := by
  have hq : ((q.1 : ℂ) ^ 2) ^ 3 = 1 := by
    calc
      ((q.1 : ℂ) ^ 2) ^ 3 = (q.1 : ℂ) ^ 6 := by ring
      _ = 1 := by
        simpa using q.2
  simpa [heisenbergKleinCyclotomicReadout] using
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange_conj_cubicCharge
      (K := ℂ) ((q.1 : ℂ) ^ 2) hq)

/-- The combined readout is continuous because the parameter space is discrete. -/
theorem continuous_heisenbergKleinCyclotomicReadout (α : 𝕜) :
    Continuous (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α) := by
  simpa [heisenbergKleinCyclotomicReadout] using
    (continuous_of_discreteTopology :
      Continuous (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α))

/-- The combined packet is locally constant on the discrete six-root lane. -/
theorem isLocallyConstant_heisenbergKleinCyclotomicReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α) := by
  simpa [heisenbergKleinCyclotomicReadout] using
    (IsLocallyConstant.of_discrete
      (f := heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α))

end InfoGeometry.Topology.HeisenbergKleinBottleCyclotomicBridge
